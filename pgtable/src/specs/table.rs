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
    ENTRIES, Entry, PFN, PTNode, PTNodePerm, PageSz, PtPage, ROOT_LEVEL, VPage, pt_index,
    size_of_level, span,
};
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
#[allow(missing_debug_implementations)]
pub struct Walk {
    pub frame: PFN,
    pub size: PageSz,
    pub perm: Perm,
    pub enc: bool,
    pub global: bool,
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
/// the root frame (CR3), and the set of data frames the leaves map (`frames_`).
/// Owning the permissions - not just a view - is what makes this the page table
/// rather than a snapshot of it; `frames_` is the analogue for the data pages it
/// refers to.
#[allow(missing_debug_implementations)]
pub tracked struct PageTablePerms<V: PtPage> {
    root_: PFN,
    pages_: Map<PFN, PTNodePerm<V>>,
    frames_: Set<PFN>,
}

impl<V: PtPage> PageTablePerms<V> {
    pub closed spec fn root(self) -> PFN {
        self.root_
    }

    pub closed spec fn pages(self) -> Map<PFN, PTNodePerm<V>> {
        self.pages_
    }

    /// The tracked set of normal/huge data frames the leaves of this table map
    /// (NOT page-table pages, which are `pages().dom()`). `wf` ties it to the
    /// actual leaf entries (`mapped_frames`).
    pub closed spec fn frames(self) -> Set<PFN> {
        self.frames_
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

    // --- entry classification ----------------------------------------

    /// `(n, idx)` is a present interior (child-pointing) entry of a live node.
    pub open spec fn interior_at(self, n: PFN, idx: nat) -> bool {
        &&& self.contains(n)
        &&& idx < ENTRIES
        &&& self.node(n).e.dom().contains(idx)
        &&& self.entry(n, idx).present
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

    // --- structural well-formedness ----------------------------------

    /// The recursive self-map slot: the root's entry that points back to the root.
    pub open spec fn is_self_map(self, n: PFN, idx: nat) -> bool {
        self.level(n) == ROOT_LEVEL && idx == IDX_SELFMAP
    }

    /// Node `n`'s present entries resolve correctly: leaves are aligned to their
    /// level, interior links resolve one level down (self-map aside).
    pub open spec fn node_wf(self, n: PFN) -> bool {
        forall|idx: nat| #![trigger self.entry(n, idx)]
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

    /// Every live node has its full 512 entries and obeys `node_wf`.
    pub open spec fn nodes_wf(self) -> bool {
        forall|n: PFN| #[trigger]
            self.contains(n) ==> (forall|i: nat| self.node(n).e.dom().contains(i) <==> i < ENTRIES)
                && self.node_wf(n)
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
            self.contains(n) ==> (self.level(n) == ROOT_LEVEL ==> n == self.root())
        &&& self.interior_at(self.root(), IDX_SELFMAP)
        &&& self.entry(self.root(), IDX_SELFMAP).target == self.root()
        &&& forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
            #![trigger self.interior_at(n1, i1), self.interior_at(n2, i2)]
            (self.interior_at(n1, i1) && self.interior_at(n2, i2) && self.entry(n1, i1).target
                == self.entry(n2, i2).target) ==> (n1 == n2 && i1 == i2)
        &&& forall|c: PFN| #![trigger self.contains(c)]
            self.contains(c) ==> exists|n: PFN, idx: nat| #![trigger self.interior_at(n, idx)]
                self.interior_at(n, idx) && self.entry(n, idx).target == c
    }

    /// The root-owned page-table invariant: the root is a live top-level node,
    /// every permission is well-formed and keyed by its own PFN, every node is
    /// structurally well-formed, the table is a valid tree with the single
    /// self-map, the whole table is A/D-pinned, and the tracked mapped-frame set
    /// is exactly the frames the leaves refer to.
    pub open spec fn wf(self) -> bool {
        &&& self.contains(self.root())
        &&& self.level(self.root()) == ROOT_LEVEL
        &&& forall|p: PFN| #[trigger] self.contains(p) ==> {
            &&& self.pages()[p].wf()
            &&& self.pages()[p].pfn() == p
        }
        &&& self.nodes_wf()
        &&& self.tree_wf()
        &&& self.ad_pinned()
        &&& self.frames() == self.mapped_frames()
    }

    // --- region typing -----------------------------------------------

    /// Every translation respects its region's policy.
    pub open spec fn region_typed(self) -> bool {
        forall|vpn: VPage| #![trigger self.walk(vpn)]
            self.walk(vpn) is Some ==> region_walk_ok(region_of(vpn), self.walk(vpn)->Some_0)
    }

    // --- the A/D ownership discipline --------------------------------

    /// Every entry of every live node is A/D-pinned, so the MMU's only concurrent
    /// write (raising ACCESSED) is a no-op (see `lemma_entry_pin_accessed_noop`).
    pub open spec fn ad_pinned(self) -> bool {
        forall|n: PFN, i: nat| #![trigger self.entry(n, i)]
            (self.contains(n) && i < ENTRIES && self.node(n).e.dom().contains(i))
                ==> entry_pinned(self.entry(n, i))
    }

    // --- confidentiality ---------------------------------------------

    /// Every translation reads a page as host-shared (`enc == false`) iff its
    /// frames are in the software's `host_shared` set.
    pub open spec fn confidential(self, host_shared: Set<PFN>) -> bool {
        forall|vpn: VPage| #![trigger self.walk(vpn)]
            self.walk(vpn) is Some ==> {
                let w = self.walk(vpn)->Some_0;
                (!w.enc) <==> walk_frames(w).subset_of(host_shared)
            }
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

/// A permissive interior entry leaves the (x86) identity accumulator unchanged.
pub proof fn lemma_permissive_keeps_top(e: Entry)
    requires
        permissive(e),
    ensures
        combine_step(perm_identity(), e) == perm_identity(),
{
}

/// With the identity accumulator, the leaf alone decides the permission.
pub proof fn lemma_top_combine_is_leaf_only(e: Entry)
    ensures
        combine_step(perm_identity(), e) == leaf_only_perm(e),
{
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

/// THE A/D-pin fact (per entry). Under the pinned invariant the MMU's only
/// permitted write (raise ACCESSED) leaves the entry unchanged, so the sole
/// concurrent writer is neutralized and exclusive `&mut` reasoning is sound.
pub proof fn lemma_entry_pin_accessed_noop(e: Entry)
    requires
        entry_pinned(e),
        e.present,
    ensures
        (Entry { accessed: true, ..e }) == e,
{
}

/// Frames covered by a translation.
pub open spec fn walk_frames(w: Walk) -> Set<PFN> {
    Set::new(|f: PFN| w.frame <= f < w.frame + w.size.pages())
}

} // verus!
