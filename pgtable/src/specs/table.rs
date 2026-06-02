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
pub tracked struct PageTablePerms<V: PtPage> {
    ghost root_: PFN,
    tracked pages_: Map<PFN, PTNodePerm<V>>,
    ghost frames_: Set<PFN>,
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

    // --- structural well-formedness ----------------------------------
    /// The recursive self-map slot: the root's entry that points back to the root.
    pub open spec fn is_self_map(self, n: PFN, idx: nat) -> bool {
        self.level(n) == ROOT_LEVEL && idx == IDX_SELFMAP
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
            self.contains(n) ==> (self.level(n) == ROOT_LEVEL ==> n == self.root())
        &&& self.interior_at(self.root(), IDX_SELFMAP)
        &&& self.entry(self.root(), IDX_SELFMAP).target == self.root()
        &&& forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
            #![trigger self.interior_at(n1, i1), self.interior_at(n2, i2)]
            (self.interior_at(n1, i1) && self.interior_at(n2, i2) && self.entry(n1, i1).target
                == self.entry(n2, i2).target) ==> (n1 == n2 && i1 == i2)
        &&& forall|c: PFN|
            #![trigger self.contains(c)]
            self.contains(c) ==> exists|n: PFN, idx: nat|
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
        &&& self.level(self.root()) == ROOT_LEVEL
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

/// The framework's whole preservation argument for a leaf write: if `t1` is `t0`
/// with node `pfn`'s entry `idx` set to a leaf/absent `e` that satisfies
/// `valid_leaf_write` - and nothing else changed - then `t1` is still a valid
/// tree. Because a leaf write never touches an interior link, `interior_at` (and
/// hence the entire tree shape) is unchanged, so every `tree_wf` clause transfers
/// verbatim. The caller of `table_set_entry` never sees this.
#[verifier::rlimit(40)]
pub proof fn lemma_leaf_write_preserves_tree_inv<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    pfn: PFN,
    idx: nat,
    e: Entry,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.valid_leaf_write(pfn, idx, e),
        t1.root() == t0.root(),
        t1.pages().dom() == t0.pages().dom(),
        t1.node(pfn) == t0.node(pfn).update(idx, e),
        forall|m: PFN| m != pfn ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| #[trigger] t1.level(m) == t0.level(m),
    ensures
        t1.tree_inv(),
{
    broadcast use lemma_node_struct_wf;

    let r = t0.root();
    // node(pfn) has its full entry set, so inserting at idx (already present)
    // leaves its domain - and hence `contains` and node domains - unchanged.
    assert(t0.node(pfn).e.dom().contains(idx));
    assert forall|n: PFN| t1.contains(n) implies #[trigger] t1.node(n).e.dom() =~= t0.node(n).e.dom()
        by {
        if n == pfn {
            assert(t0.node(pfn).e.insert(idx, e).dom() =~= t0.node(pfn).e.dom());
        }
    }
    // Entries agree everywhere except (pfn, idx); at (pfn, idx) it is a leaf/absent.
    assert forall|n: PFN, i: nat| (n != pfn || i != idx) implies #[trigger] t1.entry(n, i)
        == t0.entry(n, i) by {
        if n == pfn {
            assert(t1.node(pfn).e[i] == t0.node(pfn).e.insert(idx, e)[i]);
        }
    }
    // Therefore interior_at is unchanged everywhere - the heart of the argument.
    assert forall|n: PFN, i: nat| #[trigger] t1.interior_at(n, i) == t0.interior_at(n, i) by {
        if !(n == pfn && i == idx) {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }
    assert(!t1.interior_at(pfn, idx));
    assert(t0.interior_at(r, IDX_SELFMAP));
    assert(!t0.interior_at(pfn, idx));
    // An interior entry of t1 is not the edited slot, so its entry is unchanged.
    assert forall|n: PFN, i: nat| t1.interior_at(n, i) implies #[trigger] t1.entry(n, i) == t0.entry(
        n,
        i,
    ) by {
        if n == pfn && i == idx {
        } else {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }

    // --- tree_wf, clause by clause -----------------------------------
    // root is still the unique top-level node (levels/contains/root fixed).
    assert forall|n: PFN| #![trigger t1.contains(n)]
        t1.contains(n) && t1.level(n) == ROOT_LEVEL implies n == r by {
        assert(t0.contains(n));
    }
    // the self-map is unchanged (it is interior in t0, hence not the edited slot).
    assert(t1.interior_at(r, IDX_SELFMAP));
    assert(t1.entry(r, IDX_SELFMAP) == t0.entry(r, IDX_SELFMAP));
    // injectivity: an interior entry of t1 is one of t0 with the same target.
    assert forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
        (#[trigger] t1.interior_at(n1, i1) && #[trigger] t1.interior_at(n2, i2) && t1.entry(
            n1,
            i1,
        ).target == t1.entry(n2, i2).target) implies (n1 == n2 && i1 == i2) by {
        assert(t0.interior_at(n1, i1));
        assert(t0.interior_at(n2, i2));
    }
    // connectivity: t0's parent of c is still a parent in t1.
    assert forall|c: PFN| #![trigger t1.contains(c)]
        t1.contains(c) implies exists|n: PFN, i: nat|
        #[trigger] t1.interior_at(n, i) && t1.entry(n, i).target == c by {
        assert(t0.contains(c));
        let w = choose|n: PFN, i: nat|
            #![trigger t0.interior_at(n, i)]
            t0.interior_at(n, i) && t0.entry(n, i).target == c;
        assert(t1.interior_at(w.0, w.1));
    }
    assert(t1.tree_wf());

    // links resolve: away from pfn unchanged; at pfn the edited slot is a valid leaf.
    assert forall|n: PFN| t1.contains(n) implies #[trigger] t1.node_wf(n) by {
        if n != pfn {
            assert(t0.node_wf(n));
        } else {
            assert(t0.node_wf(pfn));
        }
    }
    // A/D pinned: away from (pfn, idx) unchanged; at (pfn, idx) `e` is pinned.
    assert forall|n: PFN, i: nat|
        (t1.contains(n) && i < ENTRIES && t1.node(n).e.dom().contains(i)) implies entry_pinned(
            #[trigger] t1.entry(n, i),
        ) by {
        if !(n == pfn && i == idx) {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }
}

/// Write entry `idx` of node `pfn` to `pte` (a leaf/absent value), maintaining the
/// table invariant. Feels like editing a page in the store: it borrows the node,
/// drives it with `node_set_entry`, then re-establishes `tree_inv` via the
/// framework lemma. The caller's only obligation is the local `valid_leaf_write`.
pub fn table_set_entry<V: PtPage>(
    node_va: VA,
    Ghost(pfn): Ghost<PFN>,
    idx: usize,
    pte: V::Pte,
    Tracked(perms): Tracked<&mut PageTablePerms<V>>,
)
    requires
        old(perms).wf(),
        node_va == old(perms).node_va(pfn),
        idx < 512,
        old(perms).valid_leaf_write(pfn, idx as nat, V::decode(pte)),
    ensures
        final(perms).wf(),
        final(perms).root() == old(perms).root(),
        final(perms).node(pfn) == old(perms).node(pfn).update(idx as nat, V::decode(pte)),
        forall|m: PFN| m != pfn ==> #[trigger] final(perms).node(m) == old(perms).node(m),
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

/// The framework's preservation argument for linking a FRESH child: if `t1` is
/// `t0` with a fresh, empty child node inserted (at `level(parent)-1`) and
/// `parent[idx]` - previously absent - set to `interior_entry(child)`, then `t1`
/// is still a valid tree. Freshness is the crux: because `child` was not in `t0`,
/// no existing interior entry targets it (their targets are live nodes), so the
/// new link is `child`'s unique parent (injectivity) and gives it connectivity.
#[verifier::rlimit(60)]
pub proof fn lemma_link_child_preserves_tree_inv<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.contains(parent),
        idx < ENTRIES,
        t0.level(parent) >= 1,
        !t0.node(parent).e[idx].present,
        !(parent == t0.root() && idx == IDX_SELFMAP),
        !t0.contains(child),
        t1.store_wf(),
        t1.root() == t0.root(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c == child || t0.contains(c)),
        t1.node(child).empty(),
        t1.level(child) == t0.level(parent) - 1,
        t1.node(parent) == t0.node(parent).update(idx, interior_entry(child)),
        t1.level(parent) == t0.level(parent),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
    ensures
        t1.tree_inv(),
{
    broadcast use lemma_node_struct_wf, lemma_node_level_bound;

    let r = t0.root();
    let ei = interior_entry(child);
    assert(child != parent && child != r);
    assert(t0.node(parent).e.dom().contains(idx));
    assert(t0.level(parent) <= ROOT_LEVEL);
    assert(t1.level(child) < ROOT_LEVEL);

    // Entries: unchanged except (parent, idx) -> ei; child's entries are all absent.
    assert forall|n: PFN, i: nat| (n != parent || i != idx) && n != child implies
        #[trigger] t1.entry(n, i) == t0.entry(n, i) by {
        if n == parent {
            assert(t1.node(parent).e[i] == t0.node(parent).e.insert(idx, ei)[i]);
        }
    }
    assert(t1.entry(parent, idx) == ei);
    // interior_at: gains (parent, idx); child has none; unchanged elsewhere.
    assert(t1.interior_at(parent, idx));
    assert forall|i: nat| !#[trigger] t1.interior_at(child, i) by {}
    assert forall|n: PFN, i: nat| (n != parent || i != idx) implies
        #[trigger] t1.interior_at(n, i) == t0.interior_at(n, i) by {
        if n != child {
            assert(t1.entry(n, i) == t0.entry(n, i));
        } else {
            assert(!t1.interior_at(child, i));
            assert(!t0.interior_at(child, i));
        }
    }
    // A t0 interior entry targets a live t0 node (via node_wf), hence not `child`.
    assert forall|n: PFN, i: nat| t0.interior_at(n, i) implies
        (#[trigger] t0.contains(t0.entry(n, i).target) && t0.entry(n, i).target != child) by {
        assert(t0.node_wf(n));
    }

    // --- tree_wf, clause by clause -----------------------------------
    assert forall|n: PFN| #![trigger t1.contains(n)]
        t1.contains(n) && t1.level(n) == ROOT_LEVEL implies n == r by {
        if n != child {
            assert(t0.contains(n));
        }
    }
    assert(t1.interior_at(r, IDX_SELFMAP));
    assert(t1.entry(r, IDX_SELFMAP) == t0.entry(r, IDX_SELFMAP));
    // injectivity: each interior entry of t1 is (parent,idx)->child, or a t0
    // interior with target in t0's store (so != child) - the two never collide.
    assert forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
        (#[trigger] t1.interior_at(n1, i1) && #[trigger] t1.interior_at(n2, i2) && t1.entry(
            n1,
            i1,
        ).target == t1.entry(n2, i2).target) implies (n1 == n2 && i1 == i2) by {
        if (n1 == parent && i1 == idx) && !(n2 == parent && i2 == idx) {
            assert(t0.interior_at(n2, i2) && t1.entry(n2, i2) == t0.entry(n2, i2));
        } else if !(n1 == parent && i1 == idx) && (n2 == parent && i2 == idx) {
            assert(t0.interior_at(n1, i1) && t1.entry(n1, i1) == t0.entry(n1, i1));
        } else if !(n1 == parent && i1 == idx) && !(n2 == parent && i2 == idx) {
            assert(t0.interior_at(n1, i1) && t1.entry(n1, i1) == t0.entry(n1, i1));
            assert(t0.interior_at(n2, i2) && t1.entry(n2, i2) == t0.entry(n2, i2));
        }
    }
    // connectivity: child's parent is (parent, idx); t0 nodes keep their parents.
    assert forall|c: PFN| #![trigger t1.contains(c)]
        t1.contains(c) implies exists|n: PFN, i: nat|
        #[trigger] t1.interior_at(n, i) && t1.entry(n, i).target == c by {
        if c == child {
            assert(t1.interior_at(parent, idx) && t1.entry(parent, idx).target == child);
        } else {
            assert(t0.contains(c));
            let w = choose|n: PFN, i: nat|
                #![trigger t0.interior_at(n, i)]
                t0.interior_at(n, i) && t0.entry(n, i).target == c;
            assert(t1.interior_at(w.0, w.1) && t1.entry(w.0, w.1).target == c);
        }
    }
    assert(t1.tree_wf());

    // links resolve.
    assert forall|n: PFN| t1.contains(n) implies #[trigger] t1.node_wf(n) by {
        if n == child {
        } else if n == parent {
            assert(t0.node_wf(parent));
        } else {
            assert(t0.node_wf(n));
        }
    }
    // A/D pinned: the new interior entry is pinned; child's are absent; rest fixed.
    assert forall|n: PFN, i: nat|
        (t1.contains(n) && i < ENTRIES && t1.node(n).e.dom().contains(i)) implies entry_pinned(
            #[trigger] t1.entry(n, i),
        ) by {
        if (n != parent || i != idx) && n != child {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }
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
        parent_va == old(perms).node_va(parent),
        parent_level as nat == old(perms).level(parent),
        parent_level >= 1,
        idx < 512,
        old(perms).contains(parent),
        !old(perms).node(parent).e[idx as nat].present,
        !(parent == old(perms).root() && idx as nat == IDX_SELFMAP),
    ensures
        final(perms).wf(),
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
        perms.root() == rp,
        perms.contains(rp),
        perms.node_va(rp) == root_perm.va(),
        perms.level(rp) == ROOT_LEVEL,
{
    broadcast use lemma_node_struct_wf, lemma_node_pfn;

    let va = root_perm.va();
    let tracked mut m = Map::<PFN, PTNodePerm<V>>::tracked_empty();
    m.tracked_insert(rp, root_perm);
    let tracked perms = PageTablePerms { root_: rp, pages_: m, frames_: Set::empty() };

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
    perms
}

/// Create a fresh, self-mapped page table: a single empty root node at the top
/// level whose only entry is the recursive self-map `root[IDX_SELFMAP] -> root`.
/// This is the bootstrap that establishes `wf` (every other op preserves it).
pub fn new_root<V: PtPage>() -> (r: Result<(VA, usize, Tracked<PageTablePerms<V>>), SvsmError>)
    ensures
        r matches Ok((root_va, root_pfn, perms)) ==> {
            &&& perms@.wf()
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

/// `node_wf` transfer for unlink, isolated to a SMALL proof context so the (heavy)
/// `node_wf` unfolding does not interact with the main lemma's large proof state -
/// the difference between a 4s and a >75s check. Given that present entries are
/// unchanged, surviving interior targets are still live (`!= child`), and levels
/// are preserved off `child`, a node that was well-formed in `t0` still is in `t1`.
#[verifier::rlimit(40)]
pub proof fn lemma_unlink_node_wf<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
    n: PFN,
)
    requires
        t0.node_wf(n),
        t0.node(n).wf(),
        t1.node(n).wf(),
        t1.contains(n),
        n != child,
        t1.entry(parent, idx) == entry_absent(),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)),
        forall|m: PFN, j: nat|
            (m != child && (m != parent || j != idx)) ==> #[trigger] t1.entry(m, j) == t0.entry(
                m,
                j,
            ),
        forall|m: PFN, j: nat| #[trigger] t1.interior_at(m, j) ==> t1.entry(m, j).target != child,
    ensures
        t1.node_wf(n),
{
    assert(t1.level(n) == t0.level(n));
    assert forall|i: nat|
        #![trigger t1.entry(n, i)]
        (i < ENTRIES && t1.node(n).e.dom().contains(i) && t1.entry(n, i).present) implies {
            let e = t1.entry(n, i);
            if t1.level(n) == 0 || e.leaf {
                t1.level(n) <= 2 && e.target % span(t1.level(n)) == 0
            } else {
                &&& t1.contains(e.target)
                &&& if t1.is_self_map(n, i) {
                    e.target == n
                } else {
                    t1.level(n) >= 1 && t1.level(e.target) == t1.level(n) - 1
                }
            }
        } by {
        if n == parent && i == idx {
            assert(t1.entry(parent, idx) == entry_absent());  // !present: antecedent is false
        } else {
            assert(t1.entry(n, i) == t0.entry(n, i));  // surviving slot is unchanged
            let e = t1.entry(n, i);
            if t1.level(n) != 0 && !e.leaf {
                assert(t1.interior_at(n, i));  // present interior
                assert(e.target != child);  // surviving target is live
                assert(t0.contains(e.target));  // t0.node_wf at i
                assert(t1.contains(e.target));  // contains-iff (target != child)
                assert(t1.is_self_map(n, i) == t0.is_self_map(n, i));  // level(n) unchanged
                assert(t1.level(e.target) == t0.level(e.target));  // target != child
            }
        }
    }
}

/// `links_wf` transfer for unlink, in its OWN small proof context: the main lemma
/// accumulates a large quantifier set (the whole tree argument), which makes even
/// discharging this grind. Taking only the RAW structural relationship (the main
/// lemma's own hypotheses, so the call discharges verbatim) and re-deriving the
/// per-entry facts here keeps the context small and the check fast.
#[verifier::rlimit(40)]
pub proof fn lemma_unlink_links_wf<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.contains(parent),
        idx < ENTRIES,
        t0.interior_at(parent, idx),
        t0.entry(parent, idx).target == child,
        t0.node(child).empty(),
        t1.store_wf(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)),
        t1.node(parent) == t0.node(parent).update(idx, entry_absent()),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
    ensures
        t1.links_wf(),
{
    broadcast use lemma_node_struct_wf, lemma_node_level_bound;

    assert(t0.node_wf(parent));
    assert(t0.contains(child));
    assert(t0.node(parent).e.dom().contains(idx));
    assert(t1.entry(parent, idx) == entry_absent());
    // entries unchanged off the absent slot and the removed child:
    assert forall|n: PFN, i: nat| (n != child && (n != parent || i != idx)) implies
        #[trigger] t1.entry(n, i) == t0.entry(n, i) by {
        if n == parent {
            assert(t1.node(parent).e[i] == t0.node(parent).e.insert(idx, entry_absent())[i]);
        }
    }
    assert(!t1.interior_at(parent, idx));
    // a t1 interior entry is an unchanged t0 interior entry:
    assert forall|n: PFN, i: nat| t1.interior_at(n, i) implies (#[trigger] t0.interior_at(n, i)
        && t1.entry(n, i) == t0.entry(n, i)) by {
        assert(t1.contains(n));  // => n != child
        assert(n != parent || i != idx);
    }
    // (parent,idx) is the unique t0 interior targeting child; hence no surviving
    // interior entry targets child.
    assert forall|n: PFN, i: nat| (#[trigger] t0.interior_at(n, i) && t0.entry(n, i).target == child)
        implies (n == parent && i == idx) by {
        assert(t0.interior_at(parent, idx) && t0.entry(parent, idx).target == child);
    }
    assert forall|n: PFN, i: nat| #[trigger] t1.interior_at(n, i) implies t1.entry(n, i).target
        != child by {
        assert(t0.interior_at(n, i) && t1.entry(n, i) == t0.entry(n, i));
    }
    // node_wf per node, in the isolated node-level context.
    assert forall|n: PFN| #[trigger] t1.contains(n) implies t1.node_wf(n) by {
        assert(t0.contains(n));  // contains-iff
        assert(t0.node_wf(n));  // t0.links_wf
        lemma_unlink_node_wf::<V>(t0, t1, parent, idx, child, n);
    }
}

/// `tree_wf` (+ root) transfer for unlink, in its own small context. By injectivity
/// `(parent, idx)` was `child`'s only parent and an empty `child` is nobody's
/// parent, so the surviving interior entries are an injective, fully-connected
/// subset of `t0`'s.
#[verifier::rlimit(40)]
pub proof fn lemma_unlink_tree_wf<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.contains(parent),
        idx < ENTRIES,
        t0.interior_at(parent, idx),
        t0.entry(parent, idx).target == child,
        !(parent == t0.root() && idx == IDX_SELFMAP),
        t0.node(child).empty(),
        t1.store_wf(),
        t1.root() == t0.root(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)),
        t1.node(parent) == t0.node(parent).update(idx, entry_absent()),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
    ensures
        t1.tree_wf(),
        t1.contains(t1.root()),
        t1.level(t1.root()) == ROOT_LEVEL,
{
    broadcast use lemma_node_struct_wf, lemma_node_level_bound;

    let r = t0.root();
    assert(t0.node_wf(parent));
    assert(t0.contains(child));
    assert(child != parent);
    // `child` is not the root: only the self-map targets the root (injectivity),
    // and (parent, idx) is not the self-map.
    assert(child != r) by {
        if child == r {
            assert(t0.interior_at(r, IDX_SELFMAP) && t0.entry(r, IDX_SELFMAP).target == r);
        }
    }
    assert(t0.node(parent).e.dom().contains(idx));
    assert forall|n: PFN, i: nat| (n != child && (n != parent || i != idx)) implies
        #[trigger] t1.entry(n, i) == t0.entry(n, i) by {
        if n == parent {
            assert(t1.node(parent).e[i] == t0.node(parent).e.insert(idx, entry_absent())[i]);
        }
    }
    assert(t1.entry(parent, idx) == entry_absent());
    assert(!t1.interior_at(parent, idx));
    assert forall|i: nat| !#[trigger] t0.interior_at(child, i) by {}
    assert forall|i: nat| !#[trigger] t1.interior_at(child, i) by {}
    assert forall|n: PFN, i: nat| t1.interior_at(n, i) implies (#[trigger] t0.interior_at(n, i)
        && t1.entry(n, i) == t0.entry(n, i) && n != child) by {
        assert(t1.contains(n));  // => n != child
        assert(n != parent || i != idx);  // else contradicts !t1.interior_at(parent, idx)
    }
    // root stays live, at the top level.
    assert(t1.contains(r));
    assert(t1.level(r) == ROOT_LEVEL);

    // --- tree_wf, clause by clause -----------------------------------
    assert forall|n: PFN| #![trigger t1.contains(n)]
        t1.contains(n) && t1.level(n) == ROOT_LEVEL implies n == r by {
        assert(t0.contains(n));
    }
    assert(t1.interior_at(r, IDX_SELFMAP));
    assert(t1.entry(r, IDX_SELFMAP) == t0.entry(r, IDX_SELFMAP));
    // injectivity: t1's interior entries are a subset of t0's (unchanged), so inherit it.
    assert forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
        (#[trigger] t1.interior_at(n1, i1) && #[trigger] t1.interior_at(n2, i2) && t1.entry(
            n1,
            i1,
        ).target == t1.entry(n2, i2).target) implies (n1 == n2 && i1 == i2) by {
        assert(t0.interior_at(n1, i1) && t1.entry(n1, i1) == t0.entry(n1, i1));
        assert(t0.interior_at(n2, i2) && t1.entry(n2, i2) == t0.entry(n2, i2));
    }
    // connectivity: each surviving node keeps its (unchanged) t0 parent.
    assert forall|c: PFN| #![trigger t1.contains(c)]
        t1.contains(c) implies exists|n: PFN, i: nat|
        #[trigger] t1.interior_at(n, i) && t1.entry(n, i).target == c by {
        assert(t0.contains(c) && c != child);
        let w = choose|n: PFN, i: nat|
            #![trigger t0.interior_at(n, i)]
            t0.interior_at(n, i) && t0.entry(n, i).target == c;
        // w is not in `child` (empty) and not (parent, idx) (it targets c != child),
        // so w is an unchanged t1 interior entry.
        assert(w.0 != child);  // `child` has no interior entries
        assert(w.0 != parent || w.1 != idx);  // (parent,idx) targets child != c
        assert(t1.entry(w.0, w.1) == t0.entry(w.0, w.1));
        assert(t1.interior_at(w.0, w.1) && t1.entry(w.0, w.1).target == c);
    }
    assert(t1.tree_wf());
}

/// `ad_pinned` transfer for unlink, in its own small context: the cleared slot is
/// now absent (vacuously pinned) and every other present entry of a live node is
/// unchanged from `t0`, where it was pinned.
#[verifier::rlimit(40)]
pub proof fn lemma_unlink_ad<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.contains(parent),
        idx < ENTRIES,
        t1.store_wf(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)),
        t1.node(parent) == t0.node(parent).update(idx, entry_absent()),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
    ensures
        t1.ad_pinned(),
{
    broadcast use lemma_node_struct_wf;

    assert(t0.node(parent).e.dom().contains(idx));
    assert(t1.entry(parent, idx) == entry_absent());
    assert forall|n: PFN, i: nat| (n != child && (n != parent || i != idx)) implies
        #[trigger] t1.entry(n, i) == t0.entry(n, i) by {
        if n == parent {
            assert(t1.node(parent).e[i] == t0.node(parent).e.insert(idx, entry_absent())[i]);
        }
    }
    assert forall|n: PFN, i: nat|
        (t1.contains(n) && i < ENTRIES && t1.node(n).e.dom().contains(i)) implies entry_pinned(
            #[trigger] t1.entry(n, i),
        ) by {
        if n != parent || i != idx {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }
}

/// The framework's preservation argument for unlinking and freeing an EMPTY
/// child: if `t1` is `t0` with `parent[idx]` (an interior link to `child`) cleared
/// and `child` removed from the store, then `t1` is still a valid tree. Kept THIN
/// - each conjunct of `tree_inv` is discharged by a sub-lemma with its own small
/// proof context, so no single check drowns in the combined quantifier set.
#[verifier::rlimit(40)]
pub proof fn lemma_unlink_free_preserves_tree_inv<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.contains(parent),
        idx < ENTRIES,
        t0.interior_at(parent, idx),
        t0.entry(parent, idx).target == child,
        !(parent == t0.root() && idx == IDX_SELFMAP),
        t0.node(child).empty(),
        t1.store_wf(),
        t1.root() == t0.root(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)),
        t1.node(parent) == t0.node(parent).update(idx, entry_absent()),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
    ensures
        t1.tree_inv(),
{
    lemma_unlink_links_wf::<V>(t0, t1, parent, idx, child);
    lemma_unlink_ad::<V>(t0, t1, parent, idx, child);
    lemma_unlink_tree_wf::<V>(t0, t1, parent, idx, child);
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
        final(perms).root() == old(perms).root(),
        !final(perms).contains(child),
        final(perms).node(parent) == old(perms).node(parent).update(idx as nat, entry_absent()),
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
