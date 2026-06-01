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

use crate::perm::{
    PA, PagePerm, VA, ZeroInit, page_alloc_zeroed, page_borrow, page_borrow_mut, page_free,
};
use crate::specs::{Entry, PTNode, ROOT_LEVEL};
use crate::stubs::SvsmError;
use vstd::prelude::*;

verus! {

// =====================================================================
// The mapping trait: a page-table page maps to an abstract `PTNode`
// =====================================================================

/// A page-table page content type, mapped to the conceptual `PTNode`.
///
/// The page-table author implements this for their concrete page type (e.g. the
/// architectural `[PTEntry; 512]` page). It is the seam between the executable
/// representation - which the author manipulates in place through a real
/// `&mut Self` - and the abstract node the verifier reasons about.
pub trait PtPage: ZeroInit + Sized {
    /// The concrete entry type (e.g. the architectural `PTEntry`).
    type Pte: Copy;

    /// Decode one concrete entry to its abstract meaning.
    spec fn decode(pte: Self::Pte) -> Entry;

    /// The abstract node this concrete page maps to. Must be *entrywise* over
    /// `decode` (see `get`/`set`), so a single-entry write refines to a single
    /// `PTNode::update`.
    spec fn view(&self) -> PTNode;

    /// A freshly zeroed page maps to the empty node (no present entries). This is
    /// what lets `node_alloc` mint a well-formed, empty node.
    proof fn zeroed_is_empty()
        ensures
            Self::zeroed().view().empty(),
    ;

    /// Read entry `i`. Specified against the abstract node.
    fn get(&self, i: usize) -> (pte: Self::Pte)
        requires
            i < 512,
        ensures
            Self::decode(pte) == self.view().e[i as nat],
    ;

    /// Write entry `i` in place. The abstract node updates at exactly `i`, and the
    /// page stays well-formed (the full architectural entry set). The author
    /// discharges both facts once, from real array manipulation.
    fn set(&mut self, i: usize, pte: Self::Pte)
        requires
            i < 512,
        ensures
            final(self).view() == old(self).view().update(i as nat, Self::decode(pte)),
            final(self).view().wf(),
    ;
}

// =====================================================================
// PTNodePerm<V>: the page-table-page permission
// =====================================================================

/// The unique authority over one live page-table node: a Layer-1 `PagePerm<V>`
/// for the page, plus the ghost paging `level` the node sits at (needed by the
/// tree invariants to prove parent/child levels decrease and huge leaves align).
#[allow(missing_debug_implementations)]
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
        assert(pp.value() == V::zeroed());
    }
    let tracked node = PTNodePerm { perm: pp, level: level as nat };
    Ok((va, pa, Tracked(node)))
}

/// Read entry `i` of the node. Returns the concrete entry; its decoding is the
/// abstract entry the node maps to at `i`.
pub fn node_read_entry<V: PtPage>(
    va: VA,
    Tracked(perm): Tracked<&PTNodePerm<V>>,
    i: usize,
) -> (pte: V::Pte)
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
        final(perm).level() == old(perm).level(),
        final(perm).node() == old(perm).node().update(i as nat, V::decode(pte)),
{
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

    // Write `pte` at index 5; the abstract node now decodes to `pte` there.
    node_set_entry::<V>(va, Tracked(perm.borrow_mut()), 5, pte);

    // Read it back: the decoded entry matches what we wrote.
    let got = node_read_entry::<V>(va, Tracked(perm.borrow()), 5);
    assert(V::decode(got) == V::decode(pte));

    // Reclaim the node: consumes `perm`, so no use-after-free is possible.
    node_free::<V>(va, perm);
}

} // verus!
