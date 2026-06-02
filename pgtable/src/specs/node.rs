// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Layer 2: the page-table-page permission.
//
// This layer instantiates the generic `PagePerm<V>` (Layer 1) with a *page-table
// page* content type and ties it to the conceptual model (`PTNode`/`Entry` from
// `specs`). The connection is NOT a fixed `decode()` baked into this module;
// instead the page-table author defines their own page-table page type `V` and
// implements the **mapping trait** `PtPage` for it. `PtPage` says:
//
//   * how one concrete entry decodes to an abstract `Entry`        (`decode`)
//   * how the whole page maps to an abstract `PTNode`              (`view`)
//   * how to read / write one entry in place, specified entrywise  (`get`/`set`)
//
// Because `view` is entrywise, a single concrete entry write refines to a single
// `PTNode::update` (this is what `set`'s postcondition states), so the verified
// node operations below need no per-entry trusted axioms: they hold for *any*
// lawful `PtPage` implementor.
//
// `PTNodePerm<V>` wraps `PagePerm<V>` plus the ghost paging level, and its `wf()`
// pins the abstraction (`node().wf()`). The node operations are *verified* (not
// trusted): they get a real `&mut V` from the Layer-1 permission and drive the
// author's `PtPage` methods, then re-derive the abstract-node update.
//
// Compiled only under verification (`verus_only`).
use crate::specs::perm::{
    PA, PagePerm, VA, page_alloc_zeroed, page_borrow, page_borrow_mut, page_free, zeroed,
};
use crate::stubs::SvsmError;
use vstd::prelude::*;

verus! {

// =====================================================================
// The conceptual model: page-table entries and nodes
// =====================================================================
/// Virtual page number (`vaddr >> 12`).
pub type VPage = nat;

/// Physical frame number (`paddr >> 12`); also the identity of a node.
pub type PFN = nat;

/// Entries per node, and the top paging level (PML4 = level 3).
pub spec const ENTRIES: nat = 512;

pub spec const ROOT_LEVEL: nat = 3;

#[derive(PartialEq, Eq, Structural, Debug)]
pub enum PageSz {
    Size4K,
    Size2M,
    Size1G,
}

impl PageSz {
    /// 4K pages spanned by a leaf of this size.
    pub open spec fn pages(self) -> nat {
        match self {
            PageSz::Size4K => 1,
            PageSz::Size2M => 512,
            PageSz::Size1G => 512 * 512,
        }
    }
}

/// 4K pages spanned by one entry at paging `level` (= 512^level).
pub open spec fn span(level: nat) -> nat
    decreases level,
{
    if level == 0 {
        1
    } else {
        512 * span((level - 1) as nat)
    }
}

pub open spec fn size_of_level(level: nat) -> PageSz {
    if level == 0 {
        PageSz::Size4K
    } else if level == 1 {
        PageSz::Size2M
    } else {
        PageSz::Size1G
    }
}

/// Page-table index used at `level` for page `vpn` = `(vpn / 512^level) % 512`,
/// matching `VirtAddr::to_pgtbl_idx::<level>`.
pub open spec fn pt_index(vpn: VPage, level: nat) -> nat {
    (vpn / span(level)) % ENTRIES
}

/// One decoded page-table entry - the information the MMU extracts from the
/// 8-byte word. STRUCTURAL bits (software-written): present, leaf, target, w,
/// user, nx, global, enc. STATUS bits (co-owned with the MMU, monotone):
/// accessed, dirty.
pub struct Entry {
    pub present: bool,
    /// `true` = leaf (maps `target` as a frame); `false` = interior (child table).
    pub leaf: bool,
    /// Child node PFN (interior) or mapped base frame PFN (leaf).
    pub target: PFN,
    pub w: bool,
    pub user: bool,
    pub nx: bool,
    pub global: bool,
    /// C-bit: `true` = private, `false` = host-shared.
    pub enc: bool,
    pub accessed: bool,
    pub dirty: bool,
}

/// A node: 512 entries (indices `0..512`).
pub struct PTNode {
    pub e: Map<nat, Entry>,
}

impl PTNode {
    /// A concrete page-table page always has exactly the architectural entry set.
    pub open spec fn wf(self) -> bool {
        forall|i: nat| self.e.dom().contains(i) <==> i < ENTRIES
    }

    /// Fresh zeroed page-table pages contain no present entries.
    pub open spec fn empty(self) -> bool {
        &&& self.wf()
        &&& forall|i: nat| i < ENTRIES ==> !(#[trigger] self.e[i]).present
    }

    pub open spec fn update(self, idx: nat, e: Entry) -> PTNode {
        PTNode { e: self.e.insert(idx, e) }
    }
}

/// The abstract interior entry SVSM installs to link a child table at frame
/// `child`: present, NOT a leaf, *permissive* (writable/user, executable) and
/// *A/D-pinned*, encrypted. Permissive interiors don't restrict the x86 walk (so
/// the leaf decides the permission), and A/D-pinning neutralizes the MMU's
/// ACCESSED write. (Flavor-specific: a Linux interior would set different flags;
/// `make_interior` is where the concrete bit pattern is built.)
pub open spec fn interior_entry(child: PFN) -> Entry {
    Entry {
        present: true,
        leaf: false,
        target: child,
        w: true,
        user: true,
        nx: false,
        global: false,
        enc: true,
        accessed: true,
        dirty: true,
    }
}

// =====================================================================
// The mapping trait: a page-table page maps to an abstract `PTNode`
// =====================================================================
/// A page-table page content type, mapped to the conceptual `PTNode`.
///
/// The page-table author implements this for their concrete page type (e.g. the
/// architectural `[PTEntry; 512]` page). It is the seam between the executable
/// representation - which the author manipulates in place through a real
/// `&mut Self` - and the abstract node the verifier reasons about.
pub trait PtPage: Sized {
    /// The concrete entry type (e.g. the architectural `PTEntry`).
    type Pte: Copy;

    /// Decode one concrete entry to its abstract meaning.
    spec fn decode(pte: Self::Pte) -> Entry;

    /// The abstract node this concrete page maps to. Must be *entrywise* over
    /// `decode` (see `get`/`set`), so a single-entry write refines to a single
    /// `PTNode::update`.
    spec fn view(&self) -> PTNode;

    /// Every page maps to a *structurally* well-formed node: the full
    /// architectural entry set (`PTNode::wf`). This holds for any contents, since
    /// editing entries changes their meaning, not the entry set. It is what lets
    /// a node permission hand out a raw `&mut Self` (`node_borrow_mut`) without
    /// losing `PTNodePerm::wf()`. The author discharges it once, structurally.
    proof fn view_wf(&self)
        ensures
            self.view().wf(),
    ;

    /// A freshly zeroed page maps to the empty node (no present entries). This is
    /// what lets `node_alloc` mint a well-formed, empty node. `zeroed::<Self>()` is
    /// the all-zero (`FromZeros`) value the allocator writes, so a concrete impl
    /// discharges this from "decoding an all-zero entry yields not-present".
    proof fn zeroed_is_empty()
        ensures
            zeroed::<Self>().view().empty(),
    ;

    /// Read entry `i`. Specified against the abstract node.
    fn get(&self, i: usize) -> (pte: Self::Pte)
        requires
            i < 512,
        ensures
            Self::decode(pte) == self.view().e[i as nat],
    ;

    /// Write entry `i` in place. The abstract node updates at exactly `i`
    /// (well-formedness of the result follows from `view_wf`).
    fn set(&mut self, i: usize, pte: Self::Pte)
        requires
            i < 512,
        ensures
            final(self).view() == old(self).view().update(i as nat, Self::decode(pte)),
    ;

    /// Build the concrete entry that links a child table at frame `child` - the
    /// PTE bits whose decoding is `interior_entry(child)`. Only the author knows
    /// the architectural layout, so the structural operations get it from here.
    fn make_interior(child: usize) -> (pte: Self::Pte)
        ensures
            Self::decode(pte) == interior_entry(child as nat),
    ;
}

/// Every page of a given `PtPage` type maps to a structurally well-formed node.
/// The universal form lets the node operations re-establish `node().wf()` after
/// handing out a raw `&mut Self`, where the resulting page value is not known.
pub proof fn lemma_all_views_wf<V: PtPage>()
    ensures
        forall|v: V| (#[trigger] v.view()).wf(),
{
    assert forall|v: V| (#[trigger] v.view()).wf() by {
        v.view_wf();
    }
}

/// A node permission's mapped node is ALWAYS structurally well-formed (the full
/// architectural entry set), for any page value - via `view_wf`. Broadcast so the
/// table layer, which only sees the closed `PTNodePerm`, can still rely on
/// `node().wf()` without unfolding `PTNodePerm::wf`.
pub broadcast proof fn lemma_node_struct_wf<V: PtPage>(perm: PTNodePerm<V>)
    ensures
        (#[trigger] perm.node()).wf(),
{
    perm.perm.value().view_wf();
}

/// A well-formed node permission sits at a real paging level (<= ROOT_LEVEL).
/// Broadcast so the table layer can use it past the closed `PTNodePerm::wf`.
pub broadcast proof fn lemma_node_level_bound<V: PtPage>(perm: PTNodePerm<V>)
    requires
        perm.wf(),
    ensures
        (#[trigger] perm.level()) <= ROOT_LEVEL,
{
}

// =====================================================================
// PTNodePerm<V>: the page-table-page permission
// =====================================================================
/// The unique authority over one live page-table node: a Layer-1 `PagePerm<V>`
/// for the page, plus the ghost paging `level` the node sits at (needed by the
/// tree invariants to prove parent/child levels decrease and huge leaves align).
pub tracked struct PTNodePerm<V: PtPage> {
    perm: PagePerm<V>,
    level: nat,
}

impl<V: PtPage> PTNodePerm<V> {
    /// Direct-map virtual address through which the node is accessed.
    pub closed spec fn va(self) -> VA {
        self.perm.va()
    }

    /// Physical address of the node.
    pub closed spec fn pa(self) -> PA {
        self.perm.pa()
    }

    /// Physical frame number identity of the node.
    pub closed spec fn pfn(self) -> nat {
        self.perm.pfn()
    }

    /// Paging level (0 = PT .. 3 = PML4).
    pub closed spec fn level(self) -> nat {
        self.level
    }

    /// The abstract node this permission currently maps to. This is the seam to
    /// the conceptual model: it is exactly the author's `view()` of the live page.
    pub closed spec fn node(self) -> PTNode {
        self.perm.value().view()
    }

    /// Well-formedness: the underlying page is live and address-coherent, the
    /// level is in range, and the mapped node has the full architectural entry
    /// set. (Tree-shape invariants live one layer up, over a map of these.)
    pub closed spec fn wf(self) -> bool {
        &&& self.perm.wf()
        &&& self.perm.is_init()
        &&& self.level <= ROOT_LEVEL
        &&& self.node().wf()
    }
}

// =====================================================================
// Verified node operations (no per-entry trusted axioms)
// =====================================================================
/// Allocate a fresh, zeroed page-table node at paging `level`.
pub fn node_alloc<V: PtPage>(level: usize) -> (r: Result<
    (VA, PA, Tracked<PTNodePerm<V>>),
    SvsmError,
>)
    requires
        level <= 3,
    ensures
        r matches Ok((va, pa, perm)) ==> {
            &&& perm@.wf()
            &&& perm@.node().empty()
            &&& perm@.va() == va
            &&& perm@.pa() == pa
            &&& perm@.level() == level as nat
        },
{
    let (va, pa, tpp) = match page_alloc_zeroed::<V>() {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    let Tracked(pp) = tpp;
    proof {
        V::zeroed_is_empty();
        assert(pp.value() == zeroed::<V>());
    }
    let tracked node = PTNodePerm { perm: pp, level: level as nat };
    Ok((va, pa, Tracked(node)))
}

/// Borrow the node's page immutably. The returned `&V` is the live page, and its
/// `view()` is the node this permission maps to. This hands the author the
/// tracked value directly - they may read it however they like, not only through
/// `node_read_entry`.
pub fn node_borrow<'a, V: PtPage>(va: VA, Tracked(perm): Tracked<&'a PTNodePerm<V>>) -> (r: &'a V)
    requires
        perm.wf(),
        va == perm.va(),
    ensures
        (*r).view() == perm.node(),
{
    page_borrow::<V>(va, Tracked(&perm.perm))
}

/// Borrow the node's page mutably. The returned `&mut V` is the live page; the
/// permission tracks the final value and its mapped node follows. This is the
/// handle through which the author manipulates the page in place with their own
/// code - any sequence of `PtPage::set` calls, or any other editing - rather than
/// being forced through `node_set_entry`. `wf()` is preserved for *any* resulting
/// page, because `view_wf` guarantees every page maps to a structurally
/// well-formed node.
pub fn node_borrow_mut<'a, V: PtPage>(va: VA, Tracked(perm): Tracked<&'a mut PTNodePerm<V>>) -> (r:
    &'a mut V)
    requires
        old(perm).wf(),
        va == old(perm).va(),
    ensures
        (*r).view() == old(perm).node(),
        final(perm).node() == (*final(r)).view(),
        final(perm).wf(),
        final(perm).va() == old(perm).va(),
        final(perm).pa() == old(perm).pa(),
        final(perm).level() == old(perm).level(),
{
    proof {
        lemma_all_views_wf::<V>();
    }
    page_borrow_mut::<V>(va, Tracked(&mut perm.perm))
}

/// Read entry `i` of the node. Returns the concrete entry; its decoding is the
/// abstract entry the node maps to at `i`.
pub fn node_read_entry<V: PtPage>(va: VA, Tracked(perm): Tracked<&PTNodePerm<V>>, i: usize) -> (pte:
    V::Pte)
    requires
        perm.wf(),
        va == perm.va(),
        i < 512,
    ensures
        V::decode(pte) == perm.node().e[i as nat],
{
    let page: &V = page_borrow::<V>(va, Tracked(&perm.perm));
    page.get(i)
}

/// Write entry `i` of the node in place. The mapped abstract node updates at
/// exactly `i`, and the node stays well-formed.
pub fn node_set_entry<V: PtPage>(
    va: VA,
    Tracked(perm): Tracked<&mut PTNodePerm<V>>,
    i: usize,
    pte: V::Pte,
)
    requires
        old(perm).wf(),
        va == old(perm).va(),
        i < 512,
    ensures
        final(perm).wf(),
        final(perm).va() == old(perm).va(),
        final(perm).pa() == old(perm).pa(),
        final(perm).pfn() == old(perm).pfn(),
        final(perm).level() == old(perm).level(),
        final(perm).node() == old(perm).node().update(i as nat, V::decode(pte)),
{
    proof {
        lemma_all_views_wf::<V>();
    }
    let page: &mut V = page_borrow_mut::<V>(va, Tracked(&mut perm.perm));
    page.set(i, pte);
}

/// Free a page-table node, consuming the only authority that can access it.
pub fn node_free<V: PtPage>(va: VA, Tracked(perm): Tracked<PTNodePerm<V>>)
    requires
        perm.wf(),
        va == perm.va(),
{
    let tracked PTNodePerm { perm: pp, level: _ } = perm;
    page_free::<V>(va, Tracked(pp));
}

// =====================================================================
// Verified demo: the node API threads end-to-end, generically over PtPage
// =====================================================================
//
// Verified (not trusted) and fully generic over any lawful `PtPage`: it proves
// the operations compose under the linear discipline. `pte` is taken as a
// parameter because a concrete `V::Pte` cannot be conjured generically.
pub fn node_demo<V: PtPage>(pte: V::Pte) {
    let (va, _pa, mut perm) = match node_alloc::<V>(2) {
        Ok(t) => t,
        Err(_) => return,
    };

    // (A) Entry-level convenience: write via `node_set_entry`, read it back.
    node_set_entry::<V>(va, Tracked(perm.borrow_mut()), 5, pte);
    let got = node_read_entry::<V>(va, Tracked(perm.borrow()), 5);
    assert(V::decode(got) == V::decode(pte));

    // (B) Obtain the tracked page directly and manipulate it in place with the
    //     author's own method - no forced get/set wrapper. The mapped node
    //     follows the edit, and the permission stays well-formed.
    let page: &mut V = node_borrow_mut::<V>(va, Tracked(perm.borrow_mut()));
    page.set(7, pte);
    let got7 = node_read_entry::<V>(va, Tracked(perm.borrow()), 7);
    assert(V::decode(got7) == V::decode(pte));

    // Reclaim the node: consumes `perm`, so no use-after-free is possible.
    node_free::<V>(va, perm);
}

} // verus!
