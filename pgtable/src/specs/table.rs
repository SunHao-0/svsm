// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Layer 3: the page table - a collection of page-table-node *permissions*.
//
// Unlike the old conceptual `PTMem` (a bare `Map<PFN, PTNode>` "node view"), the
// table here owns the actual linear permissions: `Map<PFN, PTNodePerm<V>>`, plus
// the set of data frames its leaves map (`frames_`). Each node entry is the unique
// authority over one live page-table page; the tree-shape invariants and the MMU
// walk are stated *directly over those permission pages*, via each permission's
// `node()` view (`self.node(p).e[idx]`) and `level()`. So the table is not a
// re-derived abstraction - it is the owned permission set, and `walk`/`wf` read it
// through the permission interface.
//
// This module holds the table-level *definitions and invariants*: the walk, the
// structural well-formedness (`wf`/`node_wf`/`tree_wf`), the mapped-frame tracking,
// the region-typing and confidentiality policies, and the A/D-pin discipline. The
// permission-threading *operations* (map/unmap) are built on `node`'s verified ops
// in a later layer.
//
// Compiled only under verification (`verus_only`).
use crate::specs::node::{
    ENTRIES, Entry, PFN, PTNode, PTNodePerm, PageSz, PtPage, ROOT_LEVEL, VPage, entry_absent,
    interior_entry, lemma_node_level_bound, lemma_node_pfn, lemma_node_struct_wf, node_alloc,
    node_free, node_read_entry, node_set_entry, pt_index, size_of_level, span,
};
use crate::specs::perm::{PA, VA, pfn_of_pa};
use crate::specs::table_proof::*;
use crate::stubs::SvsmError;
use vstd::prelude::*;

verus! {

// =====================================================================
// Top-level (PML4) index partition of the address space
// =====================================================================
pub spec const IDX_PERTASK: nat = 508;

pub spec const IDX_SELFMAP: nat = 493;

pub spec const IDX_PERCPU: nat = 510;

pub spec const IDX_SHARED: nat = 511;

// =====================================================================
// Walk result and the (compile-time) architecture permission algebra
// =====================================================================
/// Effective access permission produced by a walk.
#[derive(PartialEq, Eq, Structural, Debug)]
pub struct Perm {
    pub r: bool,
    pub w: bool,
    pub x: bool,
    pub user: bool,
}

/// The result of translating a page.
pub struct Walk {
    pub frame: PFN,
    pub size: PageSz,
    pub perm: Perm,
    pub enc: bool,
    pub global: bool,
}

/// One user-requested mapping: the base data frame `va` (the key in `va_map_`) is
/// mapped to, the page size, the effective access permission, and the
/// confidentiality bit. Keyed by the mapping's *base* page, so one `map(va, pa, sz)`
/// is one entry covering `size.pages()` frames. Because SVSM's interiors are
/// permissive, the walk's accumulated `perm` reduces to the leaf's, so `perm` here
/// is the leaf's own permission (`leaf_only_perm`).
pub struct VMap {
    pub frame: PFN,
    pub size: PageSz,
    pub perm: Perm,
    pub enc: bool,
}

/// The paging level a leaf of size `sz` lives at (inverse of `size_of_level`).
pub open spec fn level_of_size(sz: PageSz) -> nat {
    match sz {
        PageSz::Size4K => 0,
        PageSz::Size2M => 1,
        PageSz::Size1G => 2,
    }
}

/// The effective permission is combined over EVERY entry on the walk (parents +
/// leaf). The rule is architecture specific: x86 intersects (AND), an ARM-like
/// arch unions (OR).
#[derive(PartialEq, Eq, Structural, Debug)]
pub enum Arch {
    X86,
    ArmLike,
}

/// The target architecture is fixed at COMPILE TIME by this constant rather than
/// threaded as a walk parameter. The arch-specific algebra below selects on it;
/// the ArmLike variant is kept in the model but is not the configured target.
pub spec const ARCH: Arch = Arch::X86;

pub open spec fn perm_identity() -> Perm {
    match ARCH {
        Arch::X86 => Perm { r: true, w: true, x: true, user: true },
        Arch::ArmLike => Perm { r: false, w: false, x: false, user: false },
    }
}

pub open spec fn combine_step(acc: Perm, e: Entry) -> Perm {
    match ARCH {
        Arch::X86 => Perm {
            r: acc.r && e.present,
            w: acc.w && e.present && e.w,
            x: acc.x && e.present && !e.nx,
            user: acc.user && e.present && e.user,
        },
        Arch::ArmLike => Perm {
            r: acc.r || e.present,
            w: acc.w || (e.present && e.w),
            x: acc.x || (e.present && !e.nx),
            user: acc.user || (e.present && e.user),
        },
    }
}

/// The permission a single (leaf) entry grants on its own.
pub open spec fn leaf_only_perm(e: Entry) -> Perm {
    Perm { r: e.present, w: e.present && e.w, x: e.present && !e.nx, user: e.present && e.user }
}

// =====================================================================
// The page table: a permission collection + its mapped-frame footprint
// =====================================================================
/// All page-table-node permissions of one page table, keyed by physical frame,
/// the root frame (CR3), plus the ghost record of the user-requested mappings.
/// Owning the permissions - not just a view - is what makes this the page table
/// rather than a snapshot of it.
///
/// The mapping bookkeeping (replacing the old `frames_: Set<PFN>`, which lost the
/// va<->pa association):
///   * `xlate_base_` - the base virtual page each node translates (its vpn prefix),
///     maintained structurally; it turns the global `walk` into a local leaf fact.
///   * `va_map_` - the user-requested mappings, keyed by base virtual page.
/// `mapping_inv` couples these to the actual `walk`; one-to-one (each frame used by
/// at most one mapping) is a disjointness clause on `va_map_`, so no separate
/// inverse map is stored.
pub tracked struct PageTablePerms<V: PtPage> {
    ghost root_: PFN,
    tracked pages_: Map<PFN, PTNodePerm<V>>,
    ghost xlate_base_: Map<PFN, VPage>,
    ghost va_map_: Map<VPage, VMap>,
    /// `None` = a full table (level-3 root, self-map). `Some(i)` = a subtree view
    /// checked out from a full table's top-level entry `i` (root is the level-2
    /// child, no self-map). See `split`/`join`.
    ghost sub_idx_: Option<nat>,
}

impl<V: PtPage> PageTablePerms<V> {
    pub closed spec fn root(self) -> PFN {
        self.root_
    }

    /// `None` for a full table, `Some(i)` for the subtree under top-level entry `i`.
    pub closed spec fn sub_idx(self) -> Option<nat> {
        self.sub_idx_
    }

    /// The paging level of this (sub)table's root: 3 for a full table, 2 for a
    /// subtree.
    pub open spec fn root_level(self) -> nat {
        if self.sub_idx() is None {
            ROOT_LEVEL
        } else {
            (ROOT_LEVEL - 1) as nat
        }
    }

    /// The base virtual page of this (sub)table's root: 0 for a full table, the base
    /// of top-level entry `i` for the subtree under `i`.
    pub open spec fn root_base(self) -> VPage {
        if self.sub_idx() is None {
            0
        } else {
            (self.sub_idx()->Some_0 * span(ROOT_LEVEL)) as nat
        }
    }

    /// The recursive self-map back-edge, present only in a full table.
    pub open spec fn self_map_inv(self) -> bool {
        self.sub_idx() is None ==> {
            &&& self.interior_at(self.root(), IDX_SELFMAP)
            &&& self.entry(self.root(), IDX_SELFMAP).target == self.root()
        }
    }

    pub closed spec fn pages(self) -> Map<PFN, PTNodePerm<V>> {
        self.pages_
    }

    /// The base virtual page node `n` translates (the vpn prefix of its subtree).
    pub closed spec fn xlate_base(self, n: PFN) -> VPage {
        self.xlate_base_[n]
    }

    /// The user-requested mappings, keyed by each mapping's base virtual page.
    pub closed spec fn va_map(self) -> Map<VPage, VMap> {
        self.va_map_
    }

    /// Is `p` a live page-table node of this table?
    pub open spec fn contains(self, p: PFN) -> bool {
        self.pages().dom().contains(p)
    }

    /// The paging level of node `p`, read through its permission.
    pub open spec fn level(self, p: PFN) -> nat {
        self.pages()[p].level()
    }

    /// The abstract node of `p`, read through its permission's mapping.
    pub open spec fn node(self, p: PFN) -> PTNode {
        self.pages()[p].node()
    }

    /// Decoded entry `idx` of node `p`.
    pub open spec fn entry(self, p: PFN, idx: nat) -> Entry {
        self.node(p).e[idx]
    }

    /// The direct-map virtual address of node `p` - the access handle the exec
    /// code uses to read/write the page. Exposed so operations can tie the `VA`
    /// the caller passes (from a walk) to the node in the store.
    pub open spec fn node_va(self, p: PFN) -> VA {
        self.pages()[p].va()
    }

    // --- entry classification ----------------------------------------
    /// `(n, idx)` is a present interior (child-pointing) entry of a live node. A
    /// level-0 entry is never interior (its target is a 4K frame, not a child
    /// table - x86 leaves the HUGE bit clear there), so `interior_at` and `leaf_at`
    /// are complementary on present entries.
    pub open spec fn interior_at(self, n: PFN, idx: nat) -> bool {
        &&& self.contains(n)
        &&& idx < ENTRIES
        &&& self.node(n).e.dom().contains(idx)
        &&& self.entry(n, idx).present
        &&& self.level(n) != 0
        &&& !self.entry(n, idx).leaf
    }

    /// `(n, idx)` is a present leaf entry of a live node (a level-0 entry is a leaf
    /// positionally even without the HUGE bit).
    pub open spec fn leaf_at(self, n: PFN, idx: nat) -> bool {
        &&& self.contains(n)
        &&& idx < ENTRIES
        &&& self.node(n).e.dom().contains(idx)
        &&& self.entry(n, idx).present
        &&& (self.level(n) == 0 || self.entry(n, idx).leaf)
    }

    /// The (focused, mostly local) precondition under which writing entry `idx` of
    /// node `pfn` to `e` preserves `tree_inv` - the obligation `table_set_entry`
    /// asks of the caller. It covers the common map/unmap-DATA case:
    ///   * the slot is currently NOT an interior link (so the tree shape - which is
    ///     entirely about interior links - cannot change);
    ///   * the new entry is itself NOT an interior link, and if present is a valid
    ///     leaf (aligned to its level, level <= 2);
    ///   * the new entry is A/D-pinned.
    /// Building/tearing-down interior links is the job of `alloc_child`/`free_child`.
    pub open spec fn valid_leaf_write(self, pfn: PFN, idx: nat, e: Entry) -> bool {
        &&& self.contains(pfn)
        &&& idx < ENTRIES
        &&& !self.interior_at(pfn, idx)
        &&& entry_pinned(e)
        &&& (e.present ==> {
            &&& (self.level(pfn) == 0 || e.leaf)
            &&& self.level(pfn) <= 2
            &&& e.target % span(self.level(pfn)) == 0
        })
    }

    // --- mapped-frame footprint --------------------------------------
    /// The 4K data frames mapped by leaf `(n, idx)`: one frame for a 4K leaf, 512
    /// for a 2M leaf, 512*512 for a 1G leaf. Empty if `(n, idx)` is not a leaf.
    pub open spec fn entry_frames(self, n: PFN, idx: nat) -> Set<PFN> {
        if self.leaf_at(n, idx) {
            let base = self.entry(n, idx).target;
            Set::new(|f: PFN| base <= f < base + span(self.level(n)))
        } else {
            Set::empty()
        }
    }

    /// Every normal/huge data frame referred to by some leaf of this table. This is
    /// the footprint `frames()` is required (in `wf`) to equal.
    pub open spec fn mapped_frames(self) -> Set<PFN> {
        Set::new(
            |f: PFN|
                exists|n: PFN, idx: nat|
                    (#[trigger] self.leaf_at(n, idx)) && self.entry_frames(n, idx).contains(f),
        )
    }

    // --- the MMU walk, over the permission set -----------------------
    /// The MMU walk from `node` at `level` for page `vpn`, accumulating permission.
    /// Bounded by `level`, so it terminates even though the self-map makes the
    /// graph cyclic. Architecture is fixed by `ARCH`.
    pub open spec fn walk_from(self, node: PFN, level: nat, vpn: VPage, acc: Perm) -> Option<Walk>
        decreases level,
    {
        if !self.contains(node) {
            None
        } else {
            let e = self.entry(node, pt_index(vpn, level));
            if !e.present {
                None
            } else {
                let acc2 = combine_step(acc, e);
                if level == 0 || e.leaf {
                    Some(
                        Walk {
                            frame: (e.target + vpn % span(level)) as nat,
                            size: size_of_level(level),
                            perm: acc2,
                            enc: e.enc,
                            global: e.global,
                        },
                    )
                } else {
                    self.walk_from(e.target, (level - 1) as nat, vpn, acc2)
                }
            }
        }
    }

    /// Translate `vpn` from the root (i.e. CR3).
    pub open spec fn walk(self, vpn: VPage) -> Option<Walk> {
        self.walk_from(self.root(), ROOT_LEVEL, vpn, perm_identity())
    }

    // --- the translation base: which vpns each node/entry covers -----
    /// The node the walk for `vpn` visits at `level` (descending interior links
    /// from the root), or `None` if an interior link is missing before then. This
    /// is the *structural* path; `xlate_base_reflects_walk` ties it to `xlate_base`.
    pub open spec fn node_on_path(self, vpn: VPage, level: nat) -> Option<PFN>
        decreases ROOT_LEVEL - level,
    {
        if level >= ROOT_LEVEL {
            Some(self.root())
        } else {
            match self.node_on_path(vpn, level + 1) {
                Some(p) => if self.interior_at(p, pt_index(vpn, level + 1)) {
                    Some(self.entry(p, pt_index(vpn, level + 1)).target)
                } else {
                    None
                },
                None => None,
            }
        }
    }

    /// The permission the walk for `vpn` has accumulated by the time it reaches
    /// `level` (mirrors `node_on_path`); the accumulator argument of `walk_from`
    /// at the node `node_on_path(vpn, level)`.
    pub open spec fn path_acc(self, vpn: VPage, level: nat) -> Perm
        decreases ROOT_LEVEL - level,
    {
        if level >= ROOT_LEVEL {
            perm_identity()
        } else {
            match self.node_on_path(vpn, level + 1) {
                Some(p) => combine_step(
                    self.path_acc(vpn, level + 1),
                    self.entry(p, pt_index(vpn, level + 1)),
                ),
                None => perm_identity(),
            }
        }
    }

    /// The base virtual page that entry `idx` of node `n` translates: the node's
    /// base plus `idx` strides of one entry's coverage (`span(level(n))` pages).
    pub open spec fn entry_vpn_base(self, n: PFN, idx: nat) -> VPage {
        (self.xlate_base(n) + idx * span(self.level(n))) as nat
    }

    /// Is `vpn` inside node `n`'s translated range (`span(level(n)+1)` pages)?
    pub open spec fn node_covers(self, n: PFN, vpn: VPage) -> bool {
        self.xlate_base(n) <= vpn < self.xlate_base(n) + span((self.level(n) + 1) as nat)
    }

    /// `xlate_base` is faithful: every live node sits at the end of the walk path
    /// for exactly the vpns in its range. The structural backing of `mapping_inv`,
    /// maintained by the structural ops (it is about interior links, so leaf writes
    /// leave it alone) and the bridge from a leaf entry to a concrete `walk` result.
    pub open spec fn xlate_base_reflects_walk(self) -> bool {
        forall|n: PFN, vpn: VPage|
            #![trigger self.node_covers(n, vpn)]
            (self.contains(n) && self.node_covers(n, vpn)) ==> self.node_on_path(
                vpn,
                self.level(n),
            ) == Some(n)
    }

    /// SVSM builds every interior link PRESENT|WRITABLE|USER (NX clear), so interiors
    /// never restrict the x86 walk and the leaf alone decides the permission. The
    /// structural backing that lets `walk(vpn).perm` reduce to `leaf_only_perm`.
    pub open spec fn interiors_permissive(self) -> bool {
        forall|n: PFN, idx: nat| #[trigger] self.interior_at(n, idx) ==> permissive(self.entry(n, idx))
    }

    /// The base virtual page of node `n` is aligned to its own coverage stride
    /// (`span(level(n)+1)` pages), so each entry's base is a multiple of `span(level)`
    /// and `vpn % span(level)` is the in-entry offset. Maintained structurally.
    pub open spec fn xlate_base_aligned(self) -> bool {
        forall|n: PFN| #[trigger]
            self.contains(n) ==> self.xlate_base(n) % span((self.level(n) + 1) as nat) == 0
    }

    /// The LOCAL base relationship (the easy-to-preserve form of `xlate_base`
    /// correctness): the root is based at 0, and every interior link sets its child's
    /// base to the entry's base. `reflects_walk` is *derived* from this + `tree_inv`
    /// by `lemma_reflects_walk`, so the structural ops only maintain this local fact.
    pub open spec fn xlate_base_consistent(self) -> bool {
        &&& self.xlate_base(self.root()) == self.root_base()
        // The self-map `root[IDX_SELFMAP] -> root` is a back-edge, not a normal
        // parent link, so it is exempt (its target's base is the root base, not the
        // entry base).
        &&& forall|p: PFN, idx: nat|
            (#[trigger] self.interior_at(p, idx) && !self.is_self_map(p, idx))
                ==> self.xlate_base(self.entry(p, idx).target) == self.entry_vpn_base(p, idx)
    }

    // --- the user-mapping coupling -----------------------------------
    /// Does mapping `m` based at vpn `b` cover `vpn` (i.e. `vpn` in its range)?
    pub open spec fn vmap_covers(b: VPage, m: VMap, vpn: VPage) -> bool {
        b <= vpn < b + m.size.pages()
    }

    /// The `VMap` a leaf entry `(n, idx)` records: its target frame, the page size
    /// for `n`'s level, the leaf's own permission, and its confidentiality bit.
    pub open spec fn vmap_of_leaf(self, n: PFN, idx: nat) -> VMap {
        VMap {
            frame: self.entry(n, idx).target,
            size: size_of_level(self.level(n)),
            perm: leaf_only_perm(self.entry(n, idx)),
            enc: self.entry(n, idx).enc,
        }
    }

    /// `(n, idx)` is the leaf that records the mapping based at vpn `b` of size `m`:
    /// a present user-region leaf at the right level, based exactly at `b`, matching
    /// the record. Stated over `node_covers`/`leaf_at` (both structural / per-slot),
    /// so EVERY op preserves it locally - `node_on_path` and the walk are not here.
    pub open spec fn records_leaf(self, b: VPage, m: VMap, n: PFN, idx: nat) -> bool {
        &&& self.contains(n)
        &&& self.level(n) == level_of_size(m.size)
        &&& idx == pt_index(b, level_of_size(m.size))
        &&& self.node_covers(n, b)
        &&& self.leaf_at(n, idx)
        &&& self.entry_vpn_base(n, idx) == b
        &&& self.vmap_of_leaf(n, idx) == m
    }

    /// The user-mapping invariant, stated LEAF-LOCALLY so a single leaf write moves
    /// exactly one `va_map` key (no global walk reasoning per op). The walk-level
    /// consistency you actually want - `walk(vpn)` agrees with `va_map` - is the
    /// THEOREM `lemma_mapping_walk_coupling`, derived from this + the bridge lemmas.
    /// Not yet part of `wf`.
    pub open spec fn mapping_inv(self) -> bool {
        // (Q) COMPLETE: every recorded mapping is a present user-region leaf at the
        // node covering its base, based exactly there - so the walk realizes it.
        &&& forall|b: VPage| #[trigger]
            self.va_map().dom().contains(b) ==> {
                let m = self.va_map()[b];
                &&& in_user_region(b)
                &&& b % m.size.pages() == 0
                &&& m.frame % m.size.pages() == 0
                &&& exists|n: PFN| self.records_leaf(b, m, n, pt_index(b, level_of_size(m.size)))
            }
        // (P) SOUND: every user-region leaf is recorded at its base - so the walk
        // never resolves a user mapping we did not record.
        &&& forall|n: PFN, idx: nat|
            (#[trigger] self.leaf_at(n, idx) && in_user_region(self.entry_vpn_base(n, idx)))
                ==> self.va_map().dom().contains(self.entry_vpn_base(n, idx))
        // (C) one-to-one: distinct mappings use disjoint data-frame ranges (the
        // pa side of the bijection, kept as a clause on `va_map_` - no inverse map).
        &&& forall|b1: VPage, b2: VPage|
            (b1 != b2 && #[trigger] self.va_map().dom().contains(b1)
                && #[trigger] self.va_map().dom().contains(b2)) ==> {
                let f1 = self.va_map()[b1].frame;
                let f2 = self.va_map()[b2].frame;
                f1 + self.va_map()[b1].size.pages() <= f2 || f2 + self.va_map()[b2].size.pages() <= f1
            }
        // (D) ranges disjoint: distinct mappings cover disjoint vpn ranges.
        &&& forall|b1: VPage, b2: VPage|
            (b1 != b2 && #[trigger] self.va_map().dom().contains(b1)
                && #[trigger] self.va_map().dom().contains(b2)) ==> (b1 + self.va_map()[b1].size.pages()
                <= b2 || b2 + self.va_map()[b2].size.pages() <= b1)
    }

    /// The STRUCTURAL backing of the mapping coupling: permissive interiors and the
    /// local `xlate_base` facts. Preserved by ANY op that does not create a
    /// restrictive interior or move a node's base - including a plain leaf write -
    /// so `table_set_entry` keeps it while `mapping_inv` is re-established by
    /// `map`/`unmap`.
    pub open spec fn xlate_wf(self) -> bool {
        &&& self.interiors_permissive()
        &&& self.xlate_base_consistent()
        &&& self.xlate_base_aligned()
    }

    /// The full mapping invariant: the structural backing plus the leaf-local
    /// coupling. `wf` already gives the tree; this is the user-mapping layer on top.
    pub open spec fn mapping_wf(self) -> bool {
        &&& self.xlate_wf()
        &&& self.mapping_inv()
    }

    // --- structural well-formedness ----------------------------------
    /// The recursive self-map slot: the root's entry that points back to the root.
    /// Present only in a full table - a subtree (`sub_idx` Some) has no self-map and
    /// no node at `ROOT_LEVEL`, so this is unconditionally false there.
    pub open spec fn is_self_map(self, n: PFN, idx: nat) -> bool {
        self.sub_idx() is None && self.level(n) == ROOT_LEVEL && idx == IDX_SELFMAP
    }

    /// Node `n`'s present entries resolve correctly: leaves are aligned to their
    /// level, interior links resolve one level down (self-map aside).
    pub open spec fn node_wf(self, n: PFN) -> bool {
        forall|idx: nat|
            #![trigger self.entry(n, idx)]
            (idx < ENTRIES && self.node(n).e.dom().contains(idx) && self.entry(n, idx).present)
                ==> {
                let e = self.entry(n, idx);
                if self.level(n) == 0 || e.leaf {
                    &&& self.level(n) <= 2
                    &&& e.target % span(self.level(n)) == 0
                } else {
                    &&& self.contains(e.target)
                    &&& if self.is_self_map(n, idx) {
                        e.target == n
                    } else {
                        self.level(n) >= 1 && self.level(e.target) == self.level(n) - 1
                    }
                }
            }
    }

    /// Every link of every live node resolves (the content-dependent half of
    /// `node_wf`; the structural full-512-entry half is in `store_wf` via each
    /// node permission's own `wf()`).
    pub open spec fn links_wf(self) -> bool {
        forall|n: PFN| #[trigger] self.contains(n) ==> self.node_wf(n)
    }

    /// The table is a valid TREE with a single self-reference (the self-map):
    ///   * the root is the unique node at the top level;
    ///   * the self-map `root[IDX_SELFMAP] -> root` is present - the one allowed
    ///     back-reference, and it is at the top level;
    ///   * distinct present interior entries have distinct targets, so no node has
    ///     two parents (a tree, not a DAG);
    ///   * every live node is the target of some interior entry, so there are no
    ///     orphans. With the previous clause, every node then has exactly one
    ///     parent - the root's being its self-map.
    pub open spec fn tree_wf(self) -> bool {
        &&& forall|n: PFN| #[trigger]
            self.contains(n) ==> (self.level(n) == self.root_level() ==> n == self.root())
        &&& self.self_map_inv()
        &&& forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
            #![trigger self.interior_at(n1, i1), self.interior_at(n2, i2)]
            (self.interior_at(n1, i1) && self.interior_at(n2, i2) && self.entry(n1, i1).target
                == self.entry(n2, i2).target) ==> (n1 == n2 && i1 == i2)
        // every live node EXCEPT the (sub)root has a parent (the full root's parent
        // is its self-map, asserted separately; the subtree root has none).
        &&& forall|c: PFN|
            #![trigger self.contains(c)]
            (self.contains(c) && c != self.root()) ==> exists|n: PFN, idx: nat|
                #![trigger self.interior_at(n, idx)]
                self.interior_at(n, idx) && self.entry(n, idx).target == c
    }

    /// The STRUCTURAL store invariant: every live entry is a well-formed node
    /// permission keyed by its own PFN. This half is *free* - preserved by any
    /// node-content edit and by insert/remove - so the table behaves like a plain
    /// `PtPage` store for editing (cf. `PTNodePerm::wf`, which is also structural).
    pub open spec fn store_wf(self) -> bool {
        forall|p: PFN| #[trigger]
            self.contains(p) ==> {
                &&& self.pages()[p].wf()
                &&& self.pages()[p].pfn() == p
            }
    }

    /// The EARNED page-table invariant: the store represents a valid tree. This
    /// half is content-dependent (links resolve, the tree shape with its single
    /// self-map, A/D-pinning) and is maintained by the modification operations; it
    /// is the hypothesis `walk`/`region_typed`/`confidential` rely on.
    ///
    /// (Frame tracking - `frames() == mapped_frames()` - is intentionally NOT part
    /// of this yet; it is left simple and will be reworked later.)
    pub open spec fn tree_inv(self) -> bool {
        &&& self.contains(self.root())
        &&& self.level(self.root()) == self.root_level()
        &&& self.links_wf()
        &&& self.tree_wf()
        &&& self.ad_pinned()
    }

    /// The full root-owned page-table invariant: the free structural store part
    /// plus the earned valid-tree part.
    pub open spec fn wf(self) -> bool {
        &&& self.store_wf()
        &&& self.tree_inv()
    }

    // --- region typing -----------------------------------------------
    /// Every translation respects its region's policy.
    pub open spec fn region_typed(self) -> bool {
        forall|vpn: VPage|
            #![trigger self.walk(vpn)]
            self.walk(vpn) is Some ==> region_walk_ok(region_of(vpn), self.walk(vpn)->Some_0)
    }

    // --- the A/D ownership discipline --------------------------------
    /// Every entry of every live node is A/D-pinned, so the MMU's only concurrent
    /// write (raising ACCESSED) is a no-op (see `lemma_entry_pin_accessed_noop`).
    pub open spec fn ad_pinned(self) -> bool {
        forall|n: PFN, i: nat|
            #![trigger self.entry(n, i)]
            (self.contains(n) && i < ENTRIES && self.node(n).e.dom().contains(i)) ==> entry_pinned(
                self.entry(n, i),
            )
    }

    // --- confidentiality ---------------------------------------------
    /// Every translation reads a page as host-shared (`enc == false`) iff its
    /// frames are in the software's `host_shared` set.
    pub open spec fn confidential(self, host_shared: Set<PFN>) -> bool {
        forall|vpn: VPage|
            #![trigger self.walk(vpn)]
            self.walk(vpn) is Some ==> {
                let w = self.walk(vpn)->Some_0;
                (!w.enc) <==> walk_frames(w).subset_of(host_shared)
            }
    }
}

// =====================================================================
// Table operations: edit the store, the invariant is maintained
// =====================================================================
//
// The table is a `PtPage` store: an operation borrows a node out of the store,
// drives it with the existing `node_*` ops (which the user can think of as
// "operating on a page"), and the framework re-establishes the table invariant.
// Reads/leaf-writes only need `store_wf` to be touched; the earned `tree_inv` is
// re-derived by the per-op preservation argument.

/// Read entry `idx` of node `pfn` through the store. `node_va` is the access
/// handle the caller holds for that node (e.g. obtained from a walk).
pub fn table_read_entry<V: PtPage>(
    node_va: VA,
    Ghost(pfn): Ghost<PFN>,
    idx: usize,
    Tracked(perms): Tracked<&PageTablePerms<V>>,
) -> (pte: V::Pte)
    requires
        perms.store_wf(),
        perms.contains(pfn),
        node_va == perms.node_va(pfn),
        idx < 512,
    ensures
        V::decode(pte) == perms.entry(pfn, idx as nat),
{
    let tracked node_perm = perms.pages_.tracked_borrow(pfn);
    node_read_entry::<V>(node_va, Tracked(node_perm), idx)
}

/// Write entry `idx` of node `pfn` to `pte` (a leaf/absent value), maintaining the
/// table invariant AND the mapping backing (`xlate_wf`). Feels like editing a page
/// in the store: it borrows the node, drives it with `node_set_entry`, then
/// re-establishes the invariants. The caller's only obligation is `valid_leaf_write`.
/// `mapping_inv` is the caller's (`map`/`unmap`) job, after recording the change.
pub fn table_set_entry<V: PtPage>(
    node_va: VA,
    Ghost(pfn): Ghost<PFN>,
    idx: usize,
    pte: V::Pte,
    Tracked(perms): Tracked<&mut PageTablePerms<V>>,
)
    requires
        old(perms).wf(),
        old(perms).xlate_wf(),
        node_va == old(perms).node_va(pfn),
        idx < 512,
        old(perms).valid_leaf_write(pfn, idx as nat, V::decode(pte)),
    ensures
        final(perms).wf(),
        final(perms).xlate_wf(),
        final(perms).root() == old(perms).root(),
        final(perms).pages().dom() == old(perms).pages().dom(),
        final(perms).node(pfn) == old(perms).node(pfn).update(idx as nat, V::decode(pte)),
        forall|m: PFN| m != pfn ==> #[trigger] final(perms).node(m) == old(perms).node(m),
        forall|m: PFN| #[trigger] final(perms).level(m) == old(perms).level(m),
        forall|m: PFN| #[trigger] final(perms).xlate_base(m) == old(perms).xlate_base(m),
        final(perms).va_map() == old(perms).va_map(),
{
    let ghost t0 = *perms;
    let ghost e = V::decode(pte);
    let tracked node_perm = perms.pages_.tracked_borrow_mut(pfn);
    node_set_entry::<V>(node_va, Tracked(node_perm), idx, pte);
    proof {
        broadcast use lemma_node_struct_wf;

        let t1 = *perms;
        // After the borrow, the store is t0 with pfn's node replaced (everything
        // else identical) - spell that out for the lemma and the postconditions.
        assert(t1.pages().dom() =~= t0.pages().dom());
        assert(t1.pages()[pfn].wf());
        assert(t1.pages()[pfn].pfn() == pfn);
        assert(t1.node(pfn) == t0.node(pfn).update(idx as nat, e));
        assert forall|m: PFN| m != pfn implies #[trigger] t1.node(m) == t0.node(m) by {}
        assert forall|m: PFN| #[trigger] t1.level(m) == t0.level(m) by {}
        assert forall|m: PFN| #[trigger] t1.xlate_base(m) == t0.xlate_base(m) by {}
        assert(t1.va_map() == t0.va_map());
        // store_wf survives: pfn's permission stays well-formed and PFN-keyed
        // (node_set_entry keeps its pa, hence pfn), the rest is untouched.
        assert forall|p: PFN| t1.contains(p) implies (#[trigger] t1.pages()[p].wf()
            && t1.pages()[p].pfn() == p) by {
            assert(t0.contains(p));
            if p != pfn {
                assert(t1.pages()[p] == t0.pages()[p]);
            }
        }
        lemma_leaf_write_preserves_tree_inv::<V>(t0, t1, pfn, idx as nat, e);
        lemma_leaf_write_preserves_xlate_wf::<V>(t0, t1, pfn, idx as nat, e);
    }
}

/// Allocate a fresh, empty page-table node at paging `level`, distinct from every
/// node already in `perms`. Freshness w.r.t. the store is the trusted allocator
/// boundary: the global allocator never hands back a frame the page table already
/// owns (the owned frames are exactly `perms.pages().dom()`). Returns the access
/// `VA`, the child PFN as an exec `usize`, and the owning node permission.
#[verifier::external_body]
pub fn table_alloc_fresh<V: PtPage>(
    level: usize,
    Tracked(perms): Tracked<&PageTablePerms<V>>,
) -> (r: Result<(VA, usize, Tracked<PTNodePerm<V>>), SvsmError>)
    requires
        level <= 3,
    ensures
        r matches Ok((va, pfn, perm)) ==> {
            &&& perm@.wf()
            &&& perm@.node().empty()
            &&& perm@.level() == level as nat
            &&& perm@.va() == va
            &&& perm@.pfn() == pfn as nat
            &&& !perms.contains(pfn as nat)
        },
{
    let (va, pa, perm) = match node_alloc::<V>(level) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    let pfn = pa.0 >> 12;
    Ok((va, pfn, perm))
}

/// Allocate a fresh child table and link it under the absent slot `parent[idx]`,
/// maintaining the table invariant. This is map's "grow the tree" primitive: the
/// caller (a walk that hit an absent interior slot) passes the parent and the
/// level it is at, and gets back the new child's access `VA` and PFN to descend
/// into. The caller proves only the local slot/level facts; the framework owns the
/// freshness + tree argument (`lemma_link_child_preserves_tree_inv`).
pub fn alloc_child<V: PtPage>(
    parent_va: VA,
    Ghost(parent): Ghost<PFN>,
    parent_level: usize,
    idx: usize,
    Tracked(perms): Tracked<&mut PageTablePerms<V>>,
) -> (r: Result<(VA, usize), SvsmError>)
    requires
        old(perms).wf(),
        old(perms).mapping_wf(),
        parent_va == old(perms).node_va(parent),
        parent_level as nat == old(perms).level(parent),
        parent_level >= 1,
        idx < 512,
        old(perms).contains(parent),
        !old(perms).node(parent).e[idx as nat].present,
        !(parent == old(perms).root() && idx as nat == IDX_SELFMAP),
    ensures
        final(perms).wf(),
        final(perms).mapping_wf(),
        final(perms).root() == old(perms).root(),
        r matches Ok((child_va, child_pfn)) ==> {
            &&& !old(perms).contains(child_pfn as nat)
            &&& final(perms).contains(child_pfn as nat)
            &&& final(perms).level(child_pfn as nat) == old(perms).level(parent) - 1
            &&& final(perms).node(child_pfn as nat).empty()
            &&& child_va == final(perms).node_va(child_pfn as nat)
            &&& final(perms).node(parent) == old(perms).node(parent).update(
                idx as nat,
                interior_entry(child_pfn as nat),
            )
            &&& final(perms).xlate_base(child_pfn as nat) == old(perms).entry_vpn_base(
                parent,
                idx as nat,
            )
            &&& final(perms).va_map() == old(perms).va_map()
        },
        r matches Err(_) ==> *final(perms) == *old(perms),
{
    let ghost t0 = *perms;
    proof {
        broadcast use lemma_node_level_bound;
        assert(perms.level(parent) <= ROOT_LEVEL);
    }
    let (child_va, child_pfn, child_perm_t) = match table_alloc_fresh::<V>(
        parent_level - 1,
        Tracked(&*perms),
    ) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    let Tracked(child_perm) = child_perm_t;
    proof {
        perms.pages_.tracked_insert(child_pfn as nat, child_perm);
        // The child translates the sub-range of `parent[idx]` (structural base).
        perms.xlate_base_ = perms.xlate_base_.insert(
            child_pfn as nat,
            t0.entry_vpn_base(parent, idx as nat),
        );
    }
    let pte = V::make_interior(child_pfn);
    let tracked parent_perm = perms.pages_.tracked_borrow_mut(parent);
    node_set_entry::<V>(parent_va, Tracked(parent_perm), idx, pte);
    proof {
        broadcast use lemma_node_struct_wf;

        let t1 = *perms;
        let ghost cp = child_pfn as nat;
        // The store is t0 with `child` inserted and `parent[idx]` linked.
        assert(t1.pages().dom() =~= t0.pages().dom().insert(cp));
        assert forall|c: PFN| #[trigger] t1.contains(c) <==> (c == cp || t0.contains(c)) by {}
        assert(t1.node(cp).empty());
        assert(t1.node(cp).e.dom().contains(0) || true);
        assert(t1.node(parent) == t0.node(parent).update(idx as nat, interior_entry(cp)));
        assert forall|m: PFN| m != cp && m != parent implies #[trigger] t1.node(m) == t0.node(m)
            by {}
        assert forall|m: PFN| m != cp implies #[trigger] t1.level(m) == t0.level(m) by {}
        // store_wf survives.
        assert forall|p: PFN| t1.contains(p) implies (#[trigger] t1.pages()[p].wf()
            && t1.pages()[p].pfn() == p) by {
            if p != cp && p != parent {
                assert(t0.contains(p));
                assert(t1.pages()[p] == t0.pages()[p]);
            }
        }
        lemma_link_child_preserves_tree_inv::<V>(t0, t1, parent, idx as nat, cp);
        // mapping_wf: the structural base relationship + untouched va_map.
        assert(t1.xlate_base(cp) == t0.entry_vpn_base(parent, idx as nat));
        assert forall|m: PFN| m != cp implies #[trigger] t1.xlate_base(m) == t0.xlate_base(m) by {}
        assert(t1.va_map() == t0.va_map());
        lemma_link_child_preserves_mapping_wf::<V>(t0, t1, parent, idx as nat, cp);
    }
    Ok((child_va, child_pfn))
}

/// The executable self-map index, tied to the spec constant `IDX_SELFMAP`.
pub fn idx_selfmap() -> (r: usize)
    ensures
        r as nat == IDX_SELFMAP,
{
    493
}

/// Build the one-node, self-mapped table from a root node permission whose only
/// present entry is the self-map. Proves the full invariant for the singleton
/// store. (A proof fn so the tracked `Map`/struct construction is in proof mode.)
pub proof fn lemma_singleton_table<V: PtPage>(rp: PFN, tracked root_perm: PTNodePerm<V>) -> (tracked
    perms: PageTablePerms<V>)
    requires
        root_perm.wf(),
        root_perm.pfn() == rp,
        root_perm.level() == ROOT_LEVEL,
        root_perm.node().e[IDX_SELFMAP] == interior_entry(rp),
        forall|i: nat| i < ENTRIES && i != IDX_SELFMAP ==> !(#[trigger] root_perm.node().e[i]).present,
    ensures
        perms.wf(),
        perms.mapping_wf(),
        perms.root() == rp,
        perms.contains(rp),
        perms.node_va(rp) == root_perm.va(),
        perms.level(rp) == ROOT_LEVEL,
{
    broadcast use lemma_node_struct_wf, lemma_node_pfn;

    let va = root_perm.va();
    let tracked mut m = Map::<PFN, PTNodePerm<V>>::tracked_empty();
    m.tracked_insert(rp, root_perm);
    let tracked perms = PageTablePerms {
        root_: rp,
        pages_: m,
        xlate_base_: Map::empty().insert(rp, 0),
        va_map_: Map::empty(),
        sub_idx_: None,
    };

    assert(perms.contains(rp));
    assert(perms.node_va(rp) == va);
    assert(perms.node(rp).wf());
    assert(perms.entry(rp, IDX_SELFMAP) == interior_entry(rp));
    assert(perms.interior_at(rp, IDX_SELFMAP));
    assert forall|c: PFN| perms.contains(c) implies c == rp by {}
    assert(perms.store_wf());
    assert(perms.tree_wf()) by {
        assert forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
            (perms.interior_at(n1, i1) && perms.interior_at(n2, i2)) implies (n1 == n2 && i1 == i2)
            by {}
        assert forall|c: PFN| #![trigger perms.contains(c)]
            perms.contains(c) implies exists|n: PFN, i: nat|
            #[trigger] perms.interior_at(n, i) && perms.entry(n, i).target == c by {
            assert(perms.interior_at(rp, IDX_SELFMAP) && perms.entry(rp, IDX_SELFMAP).target == rp);
        }
    }
    assert(perms.links_wf()) by {
        assert(perms.node_wf(rp));
    }
    assert(perms.ad_pinned()) by {
        assert forall|n: PFN, i: nat|
            (perms.contains(n) && i < ENTRIES && perms.node(n).e.dom().contains(i)) implies
                entry_pinned(#[trigger] perms.entry(n, i)) by {}
    }
    // mapping_wf: the only interior is the (permissive, self-map) link; no leaves;
    // empty va_map.
    assert(perms.xlate_base(rp) == 0);
    assert(perms.interiors_permissive()) by {
        assert forall|n: PFN, idx: nat| #[trigger] perms.interior_at(n, idx) implies permissive(
            perms.entry(n, idx),
        ) by {
            assert(n == rp && idx == IDX_SELFMAP);
        }
    }
    assert(perms.xlate_base_consistent()) by {
        assert forall|p: PFN, idx: nat| (#[trigger] perms.interior_at(p, idx) && !perms.is_self_map(
            p,
            idx,
        )) implies perms.xlate_base(perms.entry(p, idx).target) == perms.entry_vpn_base(p, idx) by {
            assert(p == rp && idx == IDX_SELFMAP);  // contradicts !is_self_map
        }
    }
    assert(perms.xlate_base_aligned()) by {
        assert forall|n: PFN| #[trigger] perms.contains(n) implies perms.xlate_base(n) % span(
            (perms.level(n) + 1) as nat,
        ) == 0 by {
            assert(n == rp);
            assert(perms.xlate_base(n) == 0);
            lemma_span_pos((perms.level(n) + 1) as nat);
        }
    }
    assert(perms.mapping_inv()) by {
        // va_map is empty; the singleton has no leaves, so (Q)/(C)/(D)/(P) are vacuous.
        assert forall|n: PFN, idx: nat|
            (#[trigger] perms.leaf_at(n, idx) && in_user_region(perms.entry_vpn_base(n, idx)))
                implies perms.va_map().dom().contains(perms.entry_vpn_base(n, idx)) by {
            assert(!perms.leaf_at(n, idx));
        }
    }
    perms
}

/// Create a fresh, self-mapped page table: a single empty root node at the top
/// level whose only entry is the recursive self-map `root[IDX_SELFMAP] -> root`.
/// This is the bootstrap that establishes `wf` (every other op preserves it).
pub fn new_root<V: PtPage>() -> (r: Result<(VA, usize, Tracked<PageTablePerms<V>>), SvsmError>)
    ensures
        r matches Ok((root_va, root_pfn, perms)) ==> {
            &&& perms@.wf()
            &&& perms@.mapping_wf()
            &&& perms@.root() == root_pfn as nat
            &&& perms@.contains(root_pfn as nat)
            &&& root_va == perms@.node_va(root_pfn as nat)
            &&& perms@.level(root_pfn as nat) == ROOT_LEVEL
        },
{
    let (root_va, root_pa, root_perm_t) = match node_alloc::<V>(3) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    let Tracked(mut root_perm) = root_perm_t;
    let root_pfn = pfn_of_pa(root_pa);
    proof {
        broadcast use lemma_node_pfn;
    }
    // Install the recursive self-map: root[IDX_SELFMAP] -> root.
    let sm = idx_selfmap();
    let pte = V::make_interior(root_pfn);
    node_set_entry::<V>(root_va, Tracked(&mut root_perm), sm, pte);
    let tracked perms;
    proof {
        broadcast use lemma_node_struct_wf, lemma_node_pfn;
        perms = lemma_singleton_table::<V>(root_pfn as nat, root_perm);
    }
    Ok((root_va, root_pfn, Tracked(perms)))
}

/// Unlink and free an EMPTY child table, maintaining the table invariant. This is
/// unmap's "shrink the tree" primitive: clear the parent's interior slot and
/// reclaim the (now unreferenced, empty) child node. The caller proves only the
/// local facts - the slot is an interior link to `child`, and `child` is empty -
/// and the framework owns the tree argument.
pub fn free_child<V: PtPage>(
    parent_va: VA,
    Ghost(parent): Ghost<PFN>,
    idx: usize,
    child_va: VA,
    Ghost(child): Ghost<PFN>,
    Tracked(perms): Tracked<&mut PageTablePerms<V>>,
)
    requires
        old(perms).wf(),
        old(perms).mapping_wf(),
        parent_va == old(perms).node_va(parent),
        child_va == old(perms).node_va(child),
        idx < 512,
        old(perms).contains(parent),
        old(perms).interior_at(parent, idx as nat),
        old(perms).entry(parent, idx as nat).target == child,
        !(parent == old(perms).root() && idx as nat == IDX_SELFMAP),
        old(perms).node(child).empty(),
    ensures
        final(perms).wf(),
        final(perms).mapping_wf(),
        final(perms).root() == old(perms).root(),
        !final(perms).contains(child),
        final(perms).node(parent) == old(perms).node(parent).update(idx as nat, entry_absent()),
        final(perms).va_map() == old(perms).va_map(),
{
    let ghost t0 = *perms;
    // 1. clear the parent's interior slot.
    let absent = V::make_absent();
    let tracked parent_perm = perms.pages_.tracked_borrow_mut(parent);
    node_set_entry::<V>(parent_va, Tracked(parent_perm), idx, absent);
    // 2. remove the child from the store and free its page.
    let tracked child_perm;
    proof {
        child_perm = perms.pages_.tracked_remove(child);
        perms.xlate_base_ = perms.xlate_base_.remove(child);
    }
    node_free::<V>(child_va, Tracked(child_perm));
    // 3. re-establish the invariant.
    proof {
        broadcast use lemma_node_struct_wf, lemma_node_pfn;

        let t1 = *perms;
        assert(child != parent);
        assert(t1.pages().dom() =~= t0.pages().dom().remove(child));
        assert forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)) by {}
        assert(t1.node(parent) == t0.node(parent).update(idx as nat, entry_absent()));
        assert forall|m: PFN| m != child && m != parent implies #[trigger] t1.node(m) == t0.node(m)
            by {}
        assert forall|m: PFN| m != child implies #[trigger] t1.level(m) == t0.level(m) by {}
        assert forall|p: PFN| t1.contains(p) implies (#[trigger] t1.pages()[p].wf()
            && t1.pages()[p].pfn() == p) by {
            assert(t0.contains(p));
            if p != parent {
                assert(t1.pages()[p] == t0.pages()[p]);
            }
        }
        lemma_unlink_free_preserves_tree_inv::<V>(t0, t1, parent, idx as nat, child);
        // mapping_wf: child removed from xlate_base, va_map untouched.
        assert forall|m: PFN| m != child implies #[trigger] t1.xlate_base(m) == t0.xlate_base(m)
            by {}
        assert(t1.va_map() == t0.va_map());
        lemma_unlink_child_preserves_mapping_wf::<V>(t0, t1, parent, idx as nat, child);
    }
}

/// Record a user mapping: write the data leaf `pte` into the absent, user-region
/// slot `(node, idx)` (the level-`level(node)` leaf the caller's descent reached for
/// the target page) and record it in `va_map` at its base vpn. Maintains the full
/// table + mapping invariant; after it, `walk` of any covered vpn agrees with the
/// record (`lemma_mapping_walk_coupling`). The caller proves the local facts: the
/// slot is free, `pte` is a valid leaf for the target frame, the base is in the user
/// region, and the new vpn/frame ranges do not overlap any existing mapping.
pub fn map<V: PtPage>(
    node_va: VA,
    Ghost(node): Ghost<PFN>,
    idx: usize,
    pte: V::Pte,
    Tracked(perms): Tracked<&mut PageTablePerms<V>>,
)
    requires
        old(perms).wf(),
        old(perms).mapping_wf(),
        node_va == old(perms).node_va(node),
        idx < 512,
        old(perms).contains(node),
        old(perms).level(node) <= 2,
        !old(perms).entry(node, idx as nat).present,
        old(perms).valid_leaf_write(node, idx as nat, V::decode(pte)),
        V::decode(pte).present,
        in_user_region(old(perms).entry_vpn_base(node, idx as nat)),
        forall|b2: VPage| #[trigger]
            old(perms).va_map().dom().contains(b2) ==> {
                let s = size_of_level(old(perms).level(node)).pages();
                let bb = old(perms).entry_vpn_base(node, idx as nat);
                let f = V::decode(pte).target;
                &&& (bb + s <= b2 || b2 + old(perms).va_map()[b2].size.pages() <= bb)
                &&& (f + s <= old(perms).va_map()[b2].frame || old(perms).va_map()[b2].frame
                    + old(perms).va_map()[b2].size.pages() <= f)
            },
    ensures
        final(perms).wf(),
        final(perms).mapping_wf(),
        final(perms).va_map().dom().contains(old(perms).entry_vpn_base(node, idx as nat)),
{
    let ghost t0 = *perms;
    let ghost e = V::decode(pte);
    let ghost b = t0.entry_vpn_base(node, idx as nat);
    table_set_entry::<V>(node_va, Ghost(node), idx, pte, Tracked(perms));
    let ghost tmid = *perms;
    proof {
        // record the mapping (a ghost va_map insert).
        let mm = tmid.vmap_of_leaf(node, idx as nat);
        perms.va_map_ = perms.va_map_.insert(b, mm);
        let t1 = *perms;
        // recording the mapping keeps wf / xlate_wf (they ignore va_map).
        assert forall|n: PFN| #[trigger] t1.xlate_base(n) == tmid.xlate_base(n) by {}
        lemma_va_map_irrelevant::<V>(tmid, t1);
        // The insert keeps nodes/levels, so t1's structure == tmid's == t0-with-leaf.
        assert forall|m: PFN| #[trigger] t1.node(m) == tmid.node(m) by {}
        assert forall|m: PFN| #[trigger] t1.level(m) == tmid.level(m) by {}
        assert(e.target % span(t0.level(node)) == 0);  // valid_leaf_write + e.present
        assert(t1.vmap_of_leaf(node, idx as nat) == mm);
        assert(t1.va_map() == t0.va_map().insert(b, t1.vmap_of_leaf(node, idx as nat)));
        // relationship facts the records lemma needs (chain t1 == tmid == t0+leaf).
        assert(t1.node(node) == t0.node(node).update(idx as nat, e));
        assert forall|m: PFN| m != node implies #[trigger] t1.node(m) == t0.node(m) by {}
        assert forall|m: PFN| #[trigger] t1.level(m) == t0.level(m) by {}
        assert forall|m: PFN| #[trigger] t1.xlate_base(m) == t0.xlate_base(m) by {}
        assert(t1.pages().dom() == t0.pages().dom());
        // disjointness in the lemma's exact (inner-let) form.
        assert forall|b2: VPage| #[trigger] t0.va_map().dom().contains(b2) implies {
            let s = t1.vmap_of_leaf(node, idx as nat).size.pages();
            let f = t1.vmap_of_leaf(node, idx as nat).frame;
            &&& (b + s <= b2 || b2 + t0.va_map()[b2].size.pages() <= b)
            &&& (f + s <= t0.va_map()[b2].frame || t0.va_map()[b2].frame
                + t0.va_map()[b2].size.pages() <= f)
        } by {
            assert(t1.vmap_of_leaf(node, idx as nat).size.pages() == size_of_level(
                t0.level(node),
            ).pages());
            assert(t1.vmap_of_leaf(node, idx as nat).frame == e.target);
        }
        lemma_map_records_mapping_inv::<V>(t0, t1, node, idx as nat, e, b);
        assert(t1.mapping_wf());
        assert(t1.va_map().dom().contains(b));
    }
}

/// Remove a user mapping: clear the data leaf at `(node, idx)` - the leaf the
/// caller's walk reached for the target page - and drop it from `va_map`. Maintains
/// the table + mapping invariant. The caller proves the local facts: the slot is the
/// recorded user leaf, and it is the unique leaf at its base (the walk found it).
pub fn unmap<V: PtPage>(
    node_va: VA,
    Ghost(node): Ghost<PFN>,
    idx: usize,
    Tracked(perms): Tracked<&mut PageTablePerms<V>>,
)
    requires
        old(perms).wf(),
        old(perms).mapping_wf(),
        node_va == old(perms).node_va(node),
        idx < 512,
        old(perms).contains(node),
        old(perms).level(node) <= 2,
        old(perms).leaf_at(node, idx as nat),
        in_user_region(old(perms).entry_vpn_base(node, idx as nat)),
        old(perms).va_map().dom().contains(old(perms).entry_vpn_base(node, idx as nat)),
        forall|n2: PFN, i2: nat|
            (#[trigger] old(perms).leaf_at(n2, i2) && old(perms).entry_vpn_base(n2, i2) == old(
                perms,
            ).entry_vpn_base(node, idx as nat)) ==> (n2 == node && i2 == idx),
    ensures
        final(perms).wf(),
        final(perms).mapping_wf(),
        !final(perms).va_map().dom().contains(old(perms).entry_vpn_base(node, idx as nat)),
{
    let ghost t0 = *perms;
    let ghost b = t0.entry_vpn_base(node, idx as nat);
    proof {
        assert(!t0.interior_at(node, idx as nat));  // leaf_at => not interior
    }
    let absent = V::make_absent();
    table_set_entry::<V>(node_va, Ghost(node), idx, absent, Tracked(perms));
    let ghost tmid = *perms;
    proof {
        // drop the mapping key.
        perms.va_map_ = perms.va_map_.remove(b);
        let t1 = *perms;
        assert forall|n: PFN| #[trigger] t1.xlate_base(n) == tmid.xlate_base(n) by {}
        lemma_va_map_irrelevant::<V>(tmid, t1);
        // chain t1 == tmid == t0-with-cleared-leaf.
        assert forall|m: PFN| #[trigger] t1.node(m) == tmid.node(m) by {}
        assert forall|m: PFN| #[trigger] t1.level(m) == tmid.level(m) by {}
        assert(t1.node(node) == t0.node(node).update(idx as nat, entry_absent()));
        assert forall|m: PFN| m != node implies #[trigger] t1.node(m) == t0.node(m) by {}
        assert forall|m: PFN| #[trigger] t1.level(m) == t0.level(m) by {}
        assert forall|m: PFN| #[trigger] t1.xlate_base(m) == t0.xlate_base(m) by {}
        assert(t1.pages().dom() == t0.pages().dom());
        assert(t1.va_map() == t0.va_map().remove(b));
        lemma_unmap_clears_mapping_inv::<V>(t0, t1, node, idx as nat, b);
        assert(t1.mapping_wf());
        assert(!t1.va_map().dom().contains(b));
    }
}

// =====================================================================
// The permissive-interior / leaf-only bridge
// =====================================================================
//
// SVSM builds every interior entry PRESENT|WRITABLE|USER (NX clear). Under x86,
// such permissive interiors do not restrict, so the combined walk permission is
// decided by the leaf alone. The two algebraic facts below are the heart of that
// argument; both are independent of any particular table.
pub open spec fn permissive(e: Entry) -> bool {
    e.present && e.w && e.user && !e.nx
}

// =====================================================================
// Region typing policy
// =====================================================================
#[derive(PartialEq, Eq, Structural, Debug)]
pub enum RegionKind {
    User,
    PerTask,
    PerCpu,
    Shared,
    SelfMap,
    Unused,
}

/// Which region a page falls in, from its top-level (PML4) index.
pub open spec fn region_of(vpn: VPage) -> RegionKind {
    let idx = pt_index(vpn, ROOT_LEVEL);
    if idx <= 255 {
        RegionKind::User
    } else if idx == IDX_PERTASK {
        RegionKind::PerTask
    } else if idx == IDX_SELFMAP {
        RegionKind::SelfMap
    } else if idx == IDX_PERCPU {
        RegionKind::PerCpu
    } else if idx == IDX_SHARED {
        RegionKind::Shared
    } else {
        RegionKind::Unused
    }
}

/// A vpn whose translation is a user data mapping (recorded in `va_map_`) rather
/// than the recursive self-map subtree (which resolves page-table pages, not data,
/// and is governed by `tree_inv`). Soundness clause (B) is scoped to this region.
pub open spec fn in_user_region(vpn: VPage) -> bool {
    region_of(vpn) != RegionKind::SelfMap
}

/// The attribute policy each region's translations must satisfy.
pub open spec fn region_walk_ok(kind: RegionKind, w: Walk) -> bool {
    match kind {
        RegionKind::User => w.perm.user && !w.global && w.enc,
        RegionKind::PerTask => !w.perm.user && w.global && w.enc,
        RegionKind::PerCpu => !w.perm.user && w.global,
        RegionKind::Shared => !w.perm.user && w.global,
        RegionKind::SelfMap => !w.perm.x && w.enc,
        RegionKind::Unused => false,
    }
}

// =====================================================================
// A/D-pin discipline and confidentiality helpers
// =====================================================================
/// A present entry has ACCESSED set, and a writable one has DIRTY set.
pub open spec fn entry_pinned(e: Entry) -> bool {
    e.present ==> (e.accessed && (e.w ==> e.dirty))
}

/// Frames covered by a translation.
pub open spec fn walk_frames(w: Walk) -> Set<PFN> {
    Set::new(|f: PFN| w.frame <= f < w.frame + w.size.pages())
}

} // verus!
