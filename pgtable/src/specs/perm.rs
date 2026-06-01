// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Linear page permissions for the SVSM page table, in the style of vstd's
// `raw_ptr` / `simple_pptr`, but specialized for direct-mapped physical pages.
//
// THE ESSENCE. A permission is a `tracked`, non-`Copy` (affine) capability that
// is the *unique authority* to touch a page. Executable code only ever carries
// authority-free, `Copy` addresses (`VA` / `PA`); the permission token is
// threaded linearly through the proof. All `unsafe` is confined to the
// `external_body` primitives in this file, whose pre/post-conditions are the
// trusted axioms that everything above is *verified* against.
//
// LAYERS. The design has three layers; the two generic, page-table-agnostic ones
// live here. The third (the page-table-page permission) instantiates
// `PagePerm<V>` with the page-table page content type and lives with the
// page-table model.
//
//   Layer 0  `FramePerm`     ownership of a physical-frame *region* whose
//                            contents are NOT tracked (à la `PointsToRaw`). The
//                            domain is a set of 4K PFNs that can be split/joined,
//                            which is what backs huge-page splitting (a 2M frame
//                            into 512 4K frames). Deliberately minimal.
//
//   Layer 1  `PagePerm<V>`   the unique authority to access one 4K page holding a
//                            typed value `V` (à la `PointsTo<V>`). Differences
//                            from vstd, by design:
//                              * it additionally records the physical frame
//                                (`pa` / `pfn`), with the direct-map relation to
//                                the access `va` baked into `wf()`;
//                              * it carries NO deallocation token: every page
//                                comes from the global page allocator, so the
//                                right to free a page is exactly ownership of its
//                                `PagePerm`.
//
// `VA` / `PA` are plain addresses, named to avoid confusion with vstd's `PPtr`.
//
// Compiled only under verification (`verus_only`).
use crate::stubs::address::{Address, PhysAddr, VirtAddr};
use crate::stubs::{SvsmError, alloc_zeroed_page, free_page, phys_to_virt, virt_to_phys};
use core::marker::PhantomData;
use vstd::prelude::*;
use vstd::raw_ptr::MemContents;

verus! {

/// Declare the trusted `SvsmError` (defined outside `verus!`, in `stubs`) as an
/// opaque type so it may appear in spec-visible signatures (e.g. allocator
/// `Result` returns).
#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(missing_debug_implementations)]
pub struct ExSvsmError(SvsmError);

/// Bytes per 4K page (spec-level arithmetic uses `nat`).
pub spec const PAGE_SIZE: nat = 4096;

/// Types whose all-zero bit pattern is a valid value. `zeroed()` is the spec
/// value a freshly zeroed page of this type holds. A page is never allocated by
/// moving a (page-sized) value in; it is allocated zeroed, and this trait names
/// the resulting value. When this crate moves into the kernel, the implementors
/// are exactly the `zerocopy::FromZeros` page-content types.
pub trait ZeroInit: Sized {
    spec fn zeroed() -> Self;
}

// A small concrete implementor so the verified `perm_demo` below can allocate.
impl ZeroInit for u64 {
    open spec fn zeroed() -> u64 {
        0
    }
}

// =====================================================================
// Addresses: authority-free, Copy handles
// =====================================================================
//
// An address carries no ownership. It can only be used to access memory together
// with a matching tracked permission. The fields are public so the solver knows
// that equal addresses are equal `VA`/`PA` values.
/// A physical address. The page identity (`pfn`) is derived from it.
#[allow(missing_debug_implementations)]
pub struct PA(pub usize);

/// A virtual address. For a page permission this is the *direct-map* virtual
/// address through which the page is accessed.
#[allow(missing_debug_implementations)]
pub struct VA(pub usize);

impl Clone for PA {
    fn clone(&self) -> Self {
        *self
    }
}

impl Copy for PA {

}

impl Clone for VA {
    fn clone(&self) -> Self {
        *self
    }
}

impl Copy for VA {

}

impl PA {
    pub open spec fn addr(self) -> usize {
        self.0
    }
}

impl VA {
    pub open spec fn addr(self) -> usize {
        self.0
    }
}

/// Physical frame number of a physical address (`paddr >> 12`).
pub open spec fn pfn_of(pa: PA) -> nat {
    (pa.addr() as nat) / PAGE_SIZE
}

/// `pa` is 4K-aligned.
pub open spec fn pa_page_aligned(pa: PA) -> bool {
    (pa.addr() as nat) % PAGE_SIZE == 0
}

/// Trusted direct-map relation: the virtual address the kernel accesses a
/// physical page through. Both directions are functions; a `PagePerm`'s `wf()`
/// pins them together. This intentionally talks about raw integers — neither
/// address has authority on its own.
pub uninterp spec fn direct_map(pa: PA) -> VA;

pub uninterp spec fn reverse_direct_map(va: VA) -> PA;

/// Compute the direct-map virtual address of a physical address. Trusted: wraps
/// the platform `phys_to_virt`, and is the only executable bridge from a `PA` to
/// its `VA`.
#[verifier::external_body]
pub fn va_of(pa: PA) -> (r: VA)
    ensures
        r == direct_map(pa),
        reverse_direct_map(r) == pa,
{
    VA(phys_to_virt(PhysAddr::from(pa.0)).bits())
}

// =====================================================================
// Layer 0: FramePerm - physical-frame region (contents not tracked)
// =====================================================================
//
// The page-table-page proofs do not need this layer yet, so it is kept basic: it
// provides the region algebra (`split`/`join`) and the bridges to/from the typed
// `PagePerm<V>`. Minting a fresh raw region (e.g. a contiguous 2M frame) is left
// as a future trusted entry point.
/// Ownership of a set of physical 4K frames, without tracking their contents.
#[verifier::external_body]
#[allow(missing_debug_implementations)]
pub tracked struct FramePerm {}

impl FramePerm {
    /// The set of 4K physical frame numbers this permission owns.
    pub uninterp spec fn frames(self) -> Set<nat>;

    /// This permission owns exactly the `npages` 4K frames starting at `base`.
    pub open spec fn is_frame(self, base: nat, npages: nat) -> bool {
        self.frames() =~= Set::new(|p: nat| base <= p < base + npages)
    }

    /// Carve out the sub-region `sub`, splitting into (owned `sub`, owned rest).
    /// The two results partition the original, so no frame is ever duplicated.
    pub axiom fn split(tracked self, sub: Set<nat>) -> (tracked res: (FramePerm, FramePerm))
        requires
            sub.subset_of(self.frames()),
        ensures
            res.0.frames() == sub,
            res.1.frames() == self.frames().difference(sub),
    ;

    /// Merge two regions back into one (the union of their frames).
    pub axiom fn join(tracked self, tracked other: FramePerm) -> (tracked res: FramePerm)
        ensures
            res.frames() == self.frames().union(other.frames()),
    ;

    /// Reinterpret a single owned 4K frame as an *uninitialized* typed page
    /// permission. `va` must be the direct-map address of the frame.
    pub axiom fn into_typed<V>(tracked self, va: VA, pa: PA) -> (tracked perm: PagePerm<V>)
        requires
            self.is_frame(pfn_of(pa), 1),
            pa_page_aligned(pa),
            va == direct_map(pa),
            reverse_direct_map(va) == pa,
        ensures
            perm.wf(),
            perm.va() == va,
            perm.pa() == pa,
            perm.is_uninit(),
    ;
}

// =====================================================================
// Layer 1: PagePerm<V> - typed, PFN-tagged 4K page permission (the core)
// =====================================================================
/// The ghost contents of a `PagePerm<V>`: the access address, the physical frame,
/// and the (possibly uninitialized) value.
#[allow(missing_debug_implementations)]
pub ghost struct PagePermData<V> {
    pub va: VA,
    pub pa: PA,
    pub value: MemContents<V>,
}

/// The unique authority to access one 4K page that holds a `V`.
#[verifier::external_body]
#[verifier::accept_recursive_types(V)]
#[allow(missing_debug_implementations)]
pub tracked struct PagePerm<V> {
    phantom: PhantomData<V>,
}

impl<V> PagePerm<V> {
    pub uninterp spec fn view(self) -> PagePermData<V>;

    /// Direct-map virtual address through which the page is accessed.
    pub open spec fn va(self) -> VA {
        self.view().va
    }

    /// Physical address / stable identity of the page.
    pub open spec fn pa(self) -> PA {
        self.view().pa
    }

    /// Physical frame number identity (matches the conceptual model's `PFN`).
    pub open spec fn pfn(self) -> nat {
        pfn_of(self.pa())
    }

    /// The (possibly uninitialized) memory contents.
    pub open spec fn opt_value(self) -> MemContents<V> {
        self.view().value
    }

    pub open spec fn is_init(self) -> bool {
        self.opt_value().is_init()
    }

    pub open spec fn is_uninit(self) -> bool {
        self.opt_value().is_uninit()
    }

    /// The value, when initialized (meaningless otherwise).
    pub open spec fn value(self) -> V
        recommends
            self.is_init(),
    {
        self.opt_value().value()
    }

    /// Address coherence: `va` is the direct map of the physical page, both
    /// directions agree, and the page is 4K-aligned. The *value* is intentionally
    /// unconstrained here (init/uninit and contents are tracked separately).
    pub open spec fn wf(self) -> bool {
        &&& self.va() == direct_map(self.pa())
        &&& reverse_direct_map(self.va()) == self.pa()
        &&& pa_page_aligned(self.pa())
    }

    /// Give up access and reclaim the underlying physical frame (contents
    /// forgotten). Inverse of `FramePerm::into_typed`.
    pub axiom fn into_frame(tracked self) -> (tracked frame: FramePerm)
        ensures
            frame.is_frame(self.pfn(), 1),
    ;
}

// --- trusted access primitives: the entire `unsafe` surface of Layer 1 ---
/// Borrow the page's contents immutably.
#[verifier::external_body]
pub fn page_borrow<'a, V>(va: VA, Tracked(perm): Tracked<&'a PagePerm<V>>) -> (r: &'a V)
    requires
        perm.wf(),
        perm.is_init(),
        va == perm.va(),
    ensures
        *r == perm.value(),
{
    // SAFETY: `perm` witnesses initialized ownership of the `V` at `va`.
    unsafe { &*(va.0 as *const V) }
}

/// Borrow the page's contents mutably. The returned `&mut V` is tied to the
/// `&mut` borrow of the permission, and the permission tracks the final value.
/// This is the handle through which verified code manipulates a page in place.
#[verifier::external_body]
pub fn page_borrow_mut<'a, V>(va: VA, Tracked(perm): Tracked<&'a mut PagePerm<V>>) -> (r: &'a mut V)
    requires
        old(perm).wf(),
        old(perm).is_init(),
        va == old(perm).va(),
    ensures
        final(perm).va() == old(perm).va(),
        final(perm).pa() == old(perm).pa(),
        final(perm).wf(),
        final(perm).is_init(),
        *r == old(perm).value(),
        final(perm).value() == *final(r),
{
    // SAFETY: the exclusive `perm` witnesses sole initialized ownership at `va`.
    unsafe { &mut *(va.0 as *mut V) }
}

/// Read the whole value out by copy.
#[verifier::external_body]
pub fn page_read<V: Copy>(va: VA, Tracked(perm): Tracked<&PagePerm<V>>) -> (v: V)
    requires
        perm.wf(),
        perm.is_init(),
        va == perm.va(),
    ensures
        v == perm.value(),
{
    // SAFETY: `perm` witnesses initialized ownership of the `V` at `va`.
    unsafe { *(va.0 as *const V) }
}

/// Overwrite the whole value; the permission tracks the new value. Valid whether
/// or not the page was previously initialized: the old contents, if any, are
/// forgotten without being dropped (page-table pages are plain old data).
#[verifier::external_body]
pub fn page_write<V>(va: VA, Tracked(perm): Tracked<&mut PagePerm<V>>, v: V)
    requires
        old(perm).wf(),
        va == old(perm).va(),
    ensures
        final(perm).va() == old(perm).va(),
        final(perm).pa() == old(perm).pa(),
        final(perm).wf(),
        final(perm).opt_value() == MemContents::Init(v),
{
    // SAFETY: the exclusive `perm` witnesses sole ownership at `va`.
    unsafe {
        core::ptr::write(va.0 as *mut V, v);
    }
}

/// Move the value out, leaving the page uninitialized.
#[verifier::external_body]
pub fn page_take<V>(va: VA, Tracked(perm): Tracked<&mut PagePerm<V>>) -> (v: V)
    requires
        old(perm).wf(),
        old(perm).is_init(),
        va == old(perm).va(),
    ensures
        final(perm).va() == old(perm).va(),
        final(perm).pa() == old(perm).pa(),
        final(perm).wf(),
        final(perm).is_uninit(),
        v == old(perm).value(),
{
    // SAFETY: initialized ownership lets us move the value out.
    unsafe { core::ptr::read(va.0 as *const V) }
}

// --- trusted allocate / free, via the shared stub page allocator ---
/// Allocate one zeroed 4K page from the (stub) page allocator and return its
/// access addresses plus the owning permission. The page is born zero-initialized
/// (`V::zeroed()`); no page-sized value is moved in. No dealloc token is minted:
/// the returned `PagePerm` *is* the right to later free the page. This rests on
/// the same `stubs::alloc_zeroed_page` the page-table source uses.
#[verifier::external_body]
pub fn page_alloc_zeroed<V: ZeroInit>() -> (r: Result<(VA, PA, Tracked<PagePerm<V>>), SvsmError>)
    ensures
        r matches Ok((va, pa, perm)) ==> {
            &&& perm@.wf()
            &&& perm@.va() == va
            &&& perm@.pa() == pa
            &&& perm@.opt_value() == MemContents::Init(V::zeroed())
        },
{
    let vaddr = match alloc_zeroed_page() {
        Some(v) => v,
        None => return Err(SvsmError::Mem),
    };
    let paddr = virt_to_phys(vaddr);
    Ok((VA(vaddr.bits()), PA(paddr.bits()), Tracked::assume_new()))
}

/// Free a page-allocator page, consuming the only authority that can access it.
/// Consuming the `PagePerm` is what guarantees no live reference remains, so no
/// separate deallocation token is needed.
#[verifier::external_body]
pub fn page_free<V>(va: VA, Tracked(perm): Tracked<PagePerm<V>>)
    requires
        perm.wf(),
        va == perm.va(),
{
    // SAFETY: consuming `perm` proves no other access exists; the page came from
    // `page_alloc_zeroed`, i.e. `stubs::alloc_zeroed_page`.
    free_page(VirtAddr::from(va.0));
}

// =====================================================================
// Verified demo: the linear API threads end-to-end
// =====================================================================
//
// This is a *verified* (not trusted) function: it exercises alloc -> read ->
// write -> borrow_mut/in-place mutate -> read -> free, and the asserts are
// discharged purely from the permission contracts. It is the proof that the
// fundamental layer is usable and sound.
pub fn perm_demo() {
    let (va, _pa, mut perm) = match page_alloc_zeroed::<u64>() {
        Ok(t) => t,
        Err(_) => return,
    };

    // A freshly allocated page is zero-initialized.
    let a = page_read::<u64>(va, Tracked(perm.borrow()));
    assert(a == 0);

    // Overwrite and read back.
    page_write::<u64>(va, Tracked(perm.borrow_mut()), 9);
    let b = page_read::<u64>(va, Tracked(perm.borrow()));
    assert(b == 9);

    // Mutate in place through a real `&mut V`, then read back.
    let m = page_borrow_mut::<u64>(va, Tracked(perm.borrow_mut()));
    *m = 11;
    let c = page_read::<u64>(va, Tracked(perm.borrow()));
    assert(c == 11);

    // Reclaim the page: consumes `perm`, so no use-after-free is possible.
    page_free::<u64>(va, perm);
}

} // verus!
