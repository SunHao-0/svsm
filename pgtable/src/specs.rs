// SPDX-License-Identifier: MIT OR Apache-2.0
//
// A Verus model of the x86-64 page table, for verifying `crate::pagetable`.
//
// Compiled only under verification (`verus_only`).
//
// The MMU is trusted: from its perspective the page table is a TREE (a graph
// over physical frames; the self-map makes it cyclic, but every walk is bounded
// by the paging level). So the canonical object is that tree, and translation is
// what the MMU computes by walking it. The implementation's concrete
// `PTPage`/`PTEntry` memory maps directly onto this tree, one `PTNode` per frame.
//
// The file is organized in three layers:
//
//   (1) CONCEPTUAL MAP - the tree the MMU sees (`PTMem`), the walk it performs
//       (`walk`), and the structural well-formedness (`wf`). All translation and
//       permission combination live here.
//
//   (2) PERMISSIONS - a `PointsTo`-style ownership token (`PointsToNode`) that,
//       like vstd's `PointsTo<V>`, tracks BOTH the access right AND the node's
//       value (`value() : PTNode`). A set of these tokens *is* a `PTMem`
//       (`perms_view`). A small trusted memory API (`pte_read`/`pte_write`/
//       `node_alloc`/`node_free`) lets `pagetable.rs` drop all `unsafe`.
//
//   (3) PROPERTIES - region typing, the A/D ownership discipline (struct bits are
//       software-exclusive; A/D are co-owned with the MMU and monotone), and the
//       confidentiality goal.
//
// Trusted surface (audited once, replaces all page-table `unsafe`): the external
// type declarations, `vaddr_maps_to`, `pte_decode`, and the four memory API
// functions. Everything else is ordinary verified code.

use crate::address::{Address, PhysAddr, VirtAddr};
use crate::pagetable::{PTEntry, PTEntryFlags, PTPage, PageFrame, make_private_address};
use crate::stubs::{PageBox, SvsmError, phys_to_virt};
use core::marker::PhantomData;
use core::ptr::NonNull;
use vstd::prelude::*;
use zerocopy::FromZeros;

verus! {

// =====================================================================
// APointsTo - an address-keyed ownership permission (the "raw PointsTo")
// =====================================================================
//
// Lower-level than vstd's `PointsTo<T>`: the caller is handed the RAW address
// (`VA`/`PA` wrap a `usize`) so it can do address arithmetic (build PTE bits,
// compute self-map addresses), while the tracked `APointsTo<T>` carries the
// ownership and the tracked value. Keying by address + a trusted `ptv`
// (phys->virt) relation sidesteps pointer provenance, which is what makes
// reconstructing a node from a physical address verifiable.

/// A physical address of a `T`.
#[allow(missing_debug_implementations)]
pub struct PA<T> {
    pub addr: usize,
    pub _pd: PhantomData<T>,
}

/// A virtual address of a `T`.
#[allow(missing_debug_implementations)]
pub struct VA<T> {
    pub addr: usize,
    pub _pd: PhantomData<T>,
}

/// Trusted physical->virtual mapping (the kernel direct map). Injective on owned
/// pages, so a `PA` denotes a unique `VA`.
pub uninterp spec fn ptv(pa: usize) -> usize;

/// Ownership permission for the `T` stored at a physical address. Tracks the
/// address identity and the value. Fields private: only `alloc_page` mints one.
#[allow(missing_debug_implementations)]
pub tracked struct APointsTo<T> {
    addr_: usize,
    value_: T,
}

impl<T> APointsTo<T> {
    /// Physical address of the owned `T`.
    pub closed spec fn pa(self) -> usize {
        self.addr_
    }

    /// Virtual address of the owned `T` (its unique direct-map address).
    pub closed spec fn va(self) -> usize {
        ptv(self.addr_)
    }

    /// The tracked value.
    pub closed spec fn value(self) -> T {
        self.value_
    }
}

/// Allocate a fresh zeroed page from the kernel heap, returning its virtual
/// address and the ownership permission. No `unsafe` for the caller.
/// (`FromZeros` triggers a benign "external trait" warning for now.)
#[verifier::external_body]
pub fn alloc_page<T: FromZeros + 'static>() -> (r: Result<(VA<T>, Tracked<APointsTo<T>>), SvsmError>)
    ensures
        r matches Ok((va, perm)) ==> va.addr == perm@.va(),
{
    let pb: PageBox<T> = PageBox::try_new_zeroed()?;
    let vaddr = pb.vaddr();
    let _leaked: &'static mut T = PageBox::leak(pb);
    Ok((VA { addr: vaddr.bits(), _pd: PhantomData }, Tracked::assume_new()))
}

/// Borrow the content immutably through a virtual address that maps to the owned
/// page. Replaces the `unsafe { &*vaddr.as_ptr() }` reconstruction.
#[verifier::external_body]
pub fn va_borrow<'a, T>(va: VA<T>, Tracked(perm): Tracked<&'a APointsTo<T>>) -> (r: &'a T)
    requires
        va.addr == perm.va(),
    ensures
        *r == perm.value(),
{
    // SAFETY: `perm` witnesses ownership of the `T` at `va` (= ptv(perm.pa())).
    unsafe { &*(va.addr as *const T) }
}

/// Borrow the content mutably. The returned `&mut T` is tied to the `&mut`
/// borrow of the permission, and the permission tracks the final content.
/// Replaces `unsafe { &mut *vaddr.as_mut_ptr() }`.
#[verifier::external_body]
pub fn va_borrow_mut<'a, T>(va: VA<T>, Tracked(perm): Tracked<&'a mut APointsTo<T>>) -> (r: &'a mut T)
    requires
        va.addr == old(perm).va(),
    ensures
        *r == old(perm).value(),
        final(perm).pa() == old(perm).pa(),
        final(perm).value() == *r,
{
    // SAFETY: the exclusive `perm` witnesses sole ownership of the `T` at `va`.
    unsafe { &mut *(va.addr as *mut T) }
}

// --- the same, keyed on the PHYSICAL address (the page-table code reaches a
// --- child node by the PA stored in its parent entry) -----------------------

/// Borrow the content immutably through the physical address. `ptv` resolves it
/// to the page's direct-map virtual address.
#[verifier::external_body]
pub fn pa_borrow<'a, T>(pa: PA<T>, Tracked(perm): Tracked<&'a APointsTo<T>>) -> (r: &'a T)
    requires
        pa.addr == perm.pa(),
    ensures
        *r == perm.value(),
{
    // SAFETY: `perm` witnesses ownership of the `T` at physical `pa`.
    let va = phys_to_virt(PhysAddr::from(pa.addr));
    unsafe { &*(va.bits() as *const T) }
}

/// Borrow the content mutably through the physical address.
#[verifier::external_body]
pub fn pa_borrow_mut<'a, T>(pa: PA<T>, Tracked(perm): Tracked<&'a mut APointsTo<T>>) -> (r: &'a mut T)
    requires
        pa.addr == old(perm).pa(),
    ensures
        *r == old(perm).value(),
        final(perm).pa() == old(perm).pa(),
        final(perm).value() == *r,
{
    // SAFETY: the exclusive `perm` witnesses sole ownership of the `T` at `pa`.
    let va = phys_to_virt(PhysAddr::from(pa.addr));
    unsafe { &mut *(va.bits() as *mut T) }
}

// --- whole-value read / write (value tracking, like vstd PointsTo) ----------

/// Read the whole value out by copy.
#[verifier::external_body]
pub fn pa_read<T: Copy>(pa: PA<T>, Tracked(perm): Tracked<&APointsTo<T>>) -> (v: T)
    requires
        pa.addr == perm.pa(),
    ensures
        v == perm.value(),
{
    let va = phys_to_virt(PhysAddr::from(pa.addr));
    // SAFETY: `perm` witnesses ownership of the `T` at `pa`.
    unsafe { *(va.bits() as *const T) }
}

/// Overwrite the whole value; the permission tracks the new value.
#[verifier::external_body]
pub fn pa_write<T>(pa: PA<T>, Tracked(perm): Tracked<&mut APointsTo<T>>, v: T)
    requires
        pa.addr == old(perm).pa(),
    ensures
        final(perm).pa() == old(perm).pa(),
        final(perm).value() == v,
{
    let va = phys_to_virt(PhysAddr::from(pa.addr));
    // SAFETY: the exclusive `perm` witnesses sole ownership of the `T` at `pa`.
    unsafe {
        *(va.bits() as *mut T) = v;
    }
}

// =====================================================================
// (0) Primitives
// =====================================================================

/// Virtual page number (`vaddr >> 12`).
pub type VPage = nat;

/// Physical frame number (`paddr >> 12`); also the identity of a `PTNode`.
pub type PFN = nat;

/// Entries per node, and the top paging level (PML4 = level 3).
pub spec const ENTRIES: nat = 512;

pub spec const ROOT_LEVEL: nat = 3;

/// Top-level (PML4) indices that partition the address space (`address_space.rs`).
pub spec const IDX_PERTASK: nat = 508;

pub spec const IDX_SELFMAP: nat = 493;

pub spec const IDX_PERCPU: nat = 510;

pub spec const IDX_SHARED: nat = 511;

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

// =====================================================================
// (1) The conceptual map: the tree the MMU walks
// =====================================================================

/// One decoded page-table entry - the information the MMU extracts from the
/// 8-byte word. The fields split by owner:
///   * STRUCTURAL (software-written): present, leaf, target, w, user, nx, global, enc
///   * STATUS (co-owned with the MMU, monotone): accessed, dirty
#[allow(missing_debug_implementations)]
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
#[allow(missing_debug_implementations)]
pub struct PTNode {
    pub e: Map<nat, Entry>,
}

/// The page-table memory the MMU sees: the frames that are nodes, their decoded
/// contents, and the paging level each node sits at.
#[allow(missing_debug_implementations)]
pub struct PTMem {
    pub nodes: Map<PFN, PTNode>,
    pub level: Map<PFN, nat>,
}

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

// --- architecture-parameterized permission combination ---------------
//
// The effective permission is combined over EVERY entry on the walk (parents +
// leaf). The rule is architecture specific: x86 intersects (AND), an ARM-like
// arch unions (OR). The model never bakes in leaf-only semantics.

#[derive(PartialEq, Eq, Structural, Debug)]
pub enum Arch {
    X86,
    ArmLike,
}

pub open spec fn perm_identity(arch: Arch) -> Perm {
    match arch {
        Arch::X86 => Perm { r: true, w: true, x: true, user: true },
        Arch::ArmLike => Perm { r: false, w: false, x: false, user: false },
    }
}

pub open spec fn combine_step(arch: Arch, acc: Perm, e: Entry) -> Perm {
    match arch {
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

/// The MMU walk from `node` at `level` for page `vpn`, accumulating permission.
/// Bounded by `level`, so it terminates even though the self-map makes the graph
/// cyclic.
pub open spec fn walk_from(
    arch: Arch,
    mem: PTMem,
    node: PFN,
    level: nat,
    vpn: VPage,
    acc: Perm,
) -> Option<Walk>
    decreases level,
{
    if !mem.nodes.dom().contains(node) {
        None
    } else {
        let e = mem.nodes[node].e[pt_index(vpn, level)];
        if !e.present {
            None
        } else {
            let acc2 = combine_step(arch, acc, e);
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
                walk_from(arch, mem, e.target, (level - 1) as nat, vpn, acc2)
            }
        }
    }
}

/// Translate `vpn` from page-table root frame `root` (i.e. CR3).
pub open spec fn walk(arch: Arch, mem: PTMem, root: PFN, vpn: VPage) -> Option<Walk> {
    walk_from(arch, mem, root, ROOT_LEVEL, vpn, perm_identity(arch))
}

// --- structural well-formedness --------------------------------------

/// The recursive self-map slot: the root's entry that points back to the root.
pub open spec fn is_self_map(mem: PTMem, n: PFN, idx: nat) -> bool {
    mem.level[n] == ROOT_LEVEL && idx == IDX_SELFMAP
}

pub open spec fn node_wf(mem: PTMem, n: PFN) -> bool {
    forall|idx: nat| #![trigger mem.nodes[n].e[idx]]
        (idx < ENTRIES && mem.nodes[n].e.dom().contains(idx) && mem.nodes[n].e[idx].present) ==> {
            let e = mem.nodes[n].e[idx];
            if e.leaf {
                // Leaves only at levels 0..=2, and the base frame is aligned.
                &&& mem.level.dom().contains(n)
                &&& mem.level[n] <= 2
                &&& e.target % span(mem.level[n]) == 0
            } else {
                // Interior links resolve one level down - except the self-map,
                // which points back at the (same-level) root.
                &&& mem.nodes.dom().contains(e.target)
                &&& mem.level.dom().contains(n)
                &&& mem.level.dom().contains(e.target)
                &&& if is_self_map(mem, n, idx) {
                    e.target == n
                } else {
                    mem.level[n] >= 1 && mem.level[e.target] == mem.level[n] - 1
                }
            }
        }
}

/// Every node has its full 512 entries and obeys `node_wf`. Strictly decreasing
/// interior levels (self-map aside) make the translation graph acyclic.
pub open spec fn wf(mem: PTMem) -> bool {
    forall|n: PFN| #[trigger]
        mem.nodes.dom().contains(n) ==> (forall|i: nat| mem.nodes[n].e.dom().contains(i) <==> i
            < ENTRIES) && node_wf(mem, n)
}

// --- entry-level updates (the abstract effect of pagetable.rs writes) ---

pub open spec fn set_entry(mem: PTMem, n: PFN, idx: nat, e: Entry) -> PTMem {
    PTMem { nodes: mem.nodes.insert(n, PTNode { e: mem.nodes[n].e.insert(idx, e) }), ..mem }
}

// --- the permissive-interior / leaf-only bridge ----------------------
//
// SVSM builds every interior entry PRESENT|WRITABLE|USER (NX clear) - see
// `alloc_pte_lvl{1,2,3}`. Under x86, such permissive interiors do not restrict,
// so the combined walk permission is decided by the leaf alone. The two
// algebraic facts below are the heart of that argument.

pub open spec fn permissive(e: Entry) -> bool {
    e.present && e.w && e.user && !e.nx
}

/// A permissive interior entry leaves the x86 identity accumulator unchanged.
pub proof fn lemma_permissive_keeps_top(e: Entry)
    requires
        permissive(e),
    ensures
        combine_step(Arch::X86, perm_identity(Arch::X86), e) == perm_identity(Arch::X86),
{
}

/// With the identity accumulator, the leaf alone decides the permission.
pub proof fn lemma_top_combine_is_leaf_only(e: Entry)
    ensures
        combine_step(Arch::X86, perm_identity(Arch::X86), e) == leaf_only_perm(e),
{
}

// =====================================================================
// (2) Permissions: a value-tracking PointsTo for a node
// =====================================================================
//
// `PTEntry` and `VirtAddr` are defined in verus-neutralized vendored modules, so
// the verifier sees them as opaque. Declare them as opaque datatypes so they may
// appear in spec signatures.

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(missing_debug_implementations)]
pub struct ExPTEntry(PTEntry);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(missing_debug_implementations)]
pub struct ExVirtAddr(VirtAddr);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(missing_debug_implementations)]
pub struct ExPhysAddr(PhysAddr);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(missing_debug_implementations)]
pub struct ExSvsmError(SvsmError);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(missing_debug_implementations)]
pub struct ExPageFrame(PageFrame);

/// MMU translation relation: virtual address `va` denotes (the base of) physical
/// node `pfn`. A node's `PageBox` VA and its self-map VA both satisfy this for
/// the node's `pfn` - that is the aliasing fact.
pub uninterp spec fn vaddr_maps_to(va: VirtAddr, pfn: PFN) -> bool;

/// Decode a concrete `PTEntry`'s bits into the abstract `Entry`.
pub uninterp spec fn pte_decode(e: PTEntry) -> Entry;

/// Ownership permission for one page-table node. Like vstd's `PointsTo<V>`, it
/// tracks both the access right and the node's VALUE (`value()`). Fields are
/// private so the token cannot be forged outside this trusted module.
#[allow(missing_debug_implementations)]
pub tracked struct PointsToNode {
    pfn_: PFN,
    value_: PTNode,
}

impl PointsToNode {
    /// Physical frame / identity of this node (its key in a `PTMem`).
    pub closed spec fn pfn(self) -> PFN {
        self.pfn_
    }

    /// The node's tracked contents - the bridge to the conceptual map.
    pub closed spec fn value(self) -> PTNode {
        self.value_
    }

    /// Well-formed: the content map has exactly the 512 entry indices.
    pub closed spec fn wf(self) -> bool {
        forall|i: nat| self.value_.e.dom().contains(i) <==> i < ENTRIES
    }
}

/// A handle to a node: the virtual address used to access it (the `PointsTo`
/// analog's pointer - it carries no ownership, only the address).
#[allow(missing_debug_implementations)]
pub struct NodePtr {
    pub vaddr: VirtAddr,
}

/// View a set of held node permissions (plus the level bookkeeping the impl
/// maintains) as the conceptual `PTMem`. This is the object the refinement proof
/// relates the implementation's permission set to: `mem.nodes[p] == perms[p].value()`.
pub open spec fn perms_view(perms: Map<PFN, PointsToNode>, level: Map<PFN, nat>) -> PTMem {
    PTMem {
        nodes: Map::new(|p: PFN| perms.dom().contains(p), |p: PFN| perms[p].value()),
        level,
    }
}

// --- trusted memory API (encapsulates ALL page-table `unsafe`) -------

/// Read entry `idx`. Replaces `unsafe PTEntry::read_pte` / `from_vaddr` indexing.
#[verifier::external_body]
pub fn pte_read(p: &NodePtr, idx: usize, Tracked(perm): Tracked<&PointsToNode>) -> (r: PTEntry)
    requires
        perm.wf(),
        vaddr_maps_to(p.vaddr, perm.pfn()),
        idx < 512,
    ensures
        pte_decode(r) == perm.value().e[idx as nat],
{
    // SAFETY: `perm` witnesses ownership of the node at `p.vaddr`; `idx < 512`
    // keeps the read in bounds.
    let page: &PTPage = unsafe { &*p.vaddr.as_ptr::<PTPage>() };
    page[idx]
}

/// Write entry `idx`. Replaces the `&mut`-aliased writes behind `PTEntry::set`/
/// `clear` reached via `from_vaddr`. Tracks the new value precisely.
#[verifier::external_body]
pub fn pte_write(p: &NodePtr, idx: usize, e: PTEntry, Tracked(perm): Tracked<&mut PointsToNode>)
    requires
        old(perm).wf(),
        vaddr_maps_to(p.vaddr, old(perm).pfn()),
        idx < 512,
    ensures
        final(perm).wf(),
        final(perm).pfn() == old(perm).pfn(),
        final(perm).value() == (PTNode {
            e: old(perm).value().e.insert(idx as nat, pte_decode(e)),
        }),
{
    // SAFETY: the exclusive `perm` witnesses sole ownership of the node at
    // `p.vaddr`; `idx < 512` keeps the write in bounds.
    let page: &mut PTPage = unsafe { &mut *p.vaddr.as_mut_ptr::<PTPage>() };
    page[idx] = e;
}

/// Allocate a fresh zeroed node, minting its ownership permission. Replaces
/// `PTPage::alloc`. The new node is empty (no present entries).
#[verifier::external_body]
pub fn node_alloc() -> (r: Result<(NodePtr, Tracked<PointsToNode>), SvsmError>)
    ensures
        r matches Ok((ptr, perm)) ==> {
            &&& perm@.wf()
            &&& vaddr_maps_to(ptr.vaddr, perm@.pfn())
            &&& forall|i: nat| i < 512 ==> !(#[trigger] perm@.value().e[i]).present
        },
{
    let pb: PageBox<PTPage> = PageBox::try_new_zeroed()?;
    let vaddr = pb.vaddr();
    let _leaked: &'static mut PTPage = PageBox::leak(pb);
    Ok((NodePtr { vaddr }, Tracked::assume_new()))
}

/// Free a node, consuming its permission. Replaces `unsafe PTPage::free`. Sound
/// only with the (exclusive) permission in hand.
#[verifier::external_body]
pub fn node_free(p: NodePtr, Tracked(perm): Tracked<PointsToNode>)
    requires
        vaddr_maps_to(p.vaddr, perm.pfn()),
{
    // SAFETY: consuming `perm` proves no other reference exists; the handle came
    // from `node_alloc`, so this frees exactly that allocation.
    let ptr = p.vaddr.as_mut_ptr::<PTPage>();
    let nn = unsafe { NonNull::new_unchecked(ptr) };
    let _ = unsafe { PageBox::from_raw(nn) };
}

// --- trusted PTE decode / encode / navigation accessors -------------
// These let verified code branch on, build, and navigate through concrete
// `PTEntry`s while staying tied to `pte_decode`. They wrap the architectural
// PTE operations; each is trusted to agree with `pte_decode`.

/// Is the entry present?
#[verifier::external_body]
pub fn entry_present(e: PTEntry) -> (b: bool)
    ensures
        b == pte_decode(e).present,
{
    e.present()
}

/// Is the entry a huge/leaf entry (HUGE bit set)? Note: a level-0 PTE is a leaf
/// positionally even though this is `false`; the walk uses `level == 0 || leaf`.
#[verifier::external_body]
pub fn entry_huge(e: PTEntry) -> (b: bool)
    ensures
        b == pte_decode(e).leaf,
{
    e.huge()
}

/// The frame number stored in the entry (child table or mapped frame).
#[verifier::external_body]
pub fn entry_target_frame(e: PTEntry) -> (f: usize)
    ensures
        f as nat == pte_decode(e).target,
{
    e.address().bits() >> 12
}

/// Handle to the child node a present interior entry points at. Replaces
/// `from_entry`/`from_vaddr`: the `phys_to_virt` conversion is what convinces the
/// verifier (`vaddr_maps_to`) that this address denotes the child node.
#[verifier::external_body]
pub fn entry_child(e: PTEntry) -> (p: NodePtr)
    ensures
        vaddr_maps_to(p.vaddr, pte_decode(e).target),
{
    NodePtr { vaddr: phys_to_virt(e.address()) }
}

/// Build a private 4 KiB leaf PTE for `frame`. A/D are pre-set (pinned), so the
/// MMU never writes back (see `ad_pinned`).
#[verifier::external_body]
pub fn make_4k_leaf(frame: usize, writable: bool) -> (e: PTEntry)
    ensures
        pte_decode(e) == (Entry {
            present: true,
            leaf: false,
            target: frame as nat,
            w: writable,
            user: false,
            nx: true,
            global: true,
            enc: true,
            accessed: true,
            dirty: writable,
        }),
{
    let mut flags = PTEntryFlags::PRESENT | PTEntryFlags::GLOBAL | PTEntryFlags::NX
        | PTEntryFlags::ACCESSED;
    if writable {
        flags = flags | PTEntryFlags::WRITABLE | PTEntryFlags::DIRTY;
    }
    let pa = make_private_address(PhysAddr::from(frame << 12));
    let mut e = PTEntry::new_zeroed();
    e.set_unrestricted(pa, flags);
    e
}

/// A cleared (not-present) entry, for unmap.
#[verifier::external_body]
pub fn absent_entry() -> (e: PTEntry)
    ensures
        !pte_decode(e).present,
{
    PTEntry::new_zeroed()
}

/// The paging level of a `PageFrame` (0 = 4K, 1 = 2M, 2 = 1G).
pub uninterp spec fn pageframe_level(pf: PageFrame) -> nat;

// Trusted constructors for the opaque `PageFrame` (Verus cannot build an
// external datatype directly). The values are identical to the enum variants.
#[verifier::external_body]
pub fn page_frame_4k(pa: PhysAddr) -> (r: PageFrame)
    ensures
        pageframe_level(r) == 0nat,
{
    PageFrame::Size4K(pa)
}

#[verifier::external_body]
pub fn page_frame_2m(pa: PhysAddr) -> (r: PageFrame)
    ensures
        pageframe_level(r) == 1nat,
{
    PageFrame::Size2M(pa)
}

#[verifier::external_body]
pub fn page_frame_1g(pa: PhysAddr) -> (r: PageFrame)
    ensures
        pageframe_level(r) == 2nat,
{
    PageFrame::Size1G(pa)
}

/// Trusted `PhysAddr + usize` (the page offset add). Result is unconstrained;
/// it only affects the returned address, not the mapped/unmapped verdict.
#[verifier::external_body]
pub fn phys_add(a: PhysAddr, b: usize) -> PhysAddr {
    a + b
}

/// Connect the permission set to the conceptual map: a held node's value is
/// exactly its `PTMem` content.
pub proof fn lemma_perms_view_node(perms: Map<PFN, PointsToNode>, level: Map<PFN, nat>, p: PFN)
    requires
        perms.dom().contains(p),
    ensures
        perms_view(perms, level).nodes.dom().contains(p),
        perms_view(perms, level).nodes[p] == perms[p].value(),
{
}

// =====================================================================
// (3) Properties
// =====================================================================

// --- region typing ---------------------------------------------------

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

/// The attribute policy each region's translations must satisfy. This is where
/// User / PerTask / PerCpu / Shared genuinely differ.
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

/// Every translation respects its region's policy.
pub open spec fn region_typed(arch: Arch, mem: PTMem, root: PFN) -> bool {
    forall|vpn: VPage| #![trigger walk(arch, mem, root, vpn)]
        walk(arch, mem, root, vpn) is Some ==> region_walk_ok(
            region_of(vpn),
            walk(arch, mem, root, vpn)->Some_0,
        )
}

// --- the A/D ownership discipline ------------------------------------
//
// Structural bits are software-exclusive. A/D are co-owned with the MMU and
// monotone: any reachable walker may raise them; software lowers them only with
// exclusive (post-flush) ownership. SVSM sidesteps this by PINNING A/D at publish
// time, so the MMU's writes become no-ops and `&mut PageTable` is sound again.

pub open spec fn entry_pinned(e: Entry) -> bool {
    e.present ==> (e.accessed && (e.w ==> e.dirty))
}

pub open spec fn ad_pinned(mem: PTMem) -> bool {
    forall|n: PFN, i: nat| #![trigger mem.nodes[n].e[i]]
        (mem.nodes.dom().contains(n) && i < ENTRIES && mem.nodes[n].e.dom().contains(i))
            ==> entry_pinned(mem.nodes[n].e[i])
}

/// The MMU raising the ACCESSED bit on entry `(n, idx)`.
pub open spec fn hw_set_accessed(mem: PTMem, n: PFN, idx: nat) -> PTMem {
    set_entry(mem, n, idx, Entry { accessed: true, ..mem.nodes[n].e[idx] })
}

/// Inserting a key's current value is a no-op (helper).
pub proof fn lemma_insert_same<K, V>(m: Map<K, V>, k: K)
    requires
        m.dom().contains(k),
    ensures
        m.insert(k, m[k]) == m,
{
    assert(m.insert(k, m[k]) =~= m);
}

/// THE `&mut PageTable` JUSTIFICATION. Under the pinned-A/D invariant the MMU's
/// only permitted write (raise ACCESSED) leaves the memory unchanged, so the sole
/// concurrent writer is neutralized and exclusive reasoning is sound.
pub proof fn lemma_ad_pin_accessed_noop(mem: PTMem, n: PFN, idx: nat)
    requires
        ad_pinned(mem),
        mem.nodes.dom().contains(n),
        mem.nodes[n].e.dom().contains(idx),
        idx < ENTRIES,
        mem.nodes[n].e[idx].present,
    ensures
        hw_set_accessed(mem, n, idx) == mem,
{
    let node = mem.nodes[n];
    let e = node.e[idx];
    assert(entry_pinned(e));
    assert(e.accessed);
    let e2 = Entry { accessed: true, ..e };
    assert(e2 == e);
    lemma_insert_same(node.e, idx);
    assert(node.e.insert(idx, e2) == node.e);
    assert(PTNode { e: node.e.insert(idx, e2) } == node);
    lemma_insert_same(mem.nodes, n);
}

// --- confidentiality goal --------------------------------------------

/// Frames covered by a translation.
pub open spec fn walk_frames(w: Walk) -> Set<PFN> {
    Set::new(|f: PFN| w.frame <= f < w.frame + w.size.pages())
}

/// Top-level confidentiality property: every translation reads a page as
/// host-shared (`enc == false`) iff its frames are in the software's
/// `host_shared` set. (Multi-CPU + stale-TLB reasoning is a higher system layer
/// built on `walk`; this states the per-page-table invariant it relies on.)
pub open spec fn confidential(arch: Arch, mem: PTMem, root: PFN, host_shared: Set<PFN>) -> bool {
    forall|vpn: VPage| #![trigger walk(arch, mem, root, vpn)]
        walk(arch, mem, root, vpn) is Some ==> {
            let w = walk(arch, mem, root, vpn)->Some_0;
            (!w.enc) <==> walk_frames(w).subset_of(host_shared)
        }
}

// =====================================================================
// (3b) Self-map model - for verifying `PageTable::virt_to_frame`
// =====================================================================
//
// `virt_to_frame` reads the paging hierarchy top-down through the recursive
// self-map (idx 493): `read_pte` at the self-map address of level `L` returns
// exactly the entry the MMU walk reads at level `L`. We model that as trusted
// evidence (`SelfMapView`) plus a `read_pte` contract, and prove `virt_to_frame`
// returns the same result as `walk`.

/// The node reached by descending from `root` (level 3) to `level` for `vpn`,
/// following present interior entries.
pub open spec fn node_at(mem: PTMem, root: PFN, vpn: VPage, level: nat) -> Option<PFN>
    decreases ROOT_LEVEL - level,
{
    if level >= ROOT_LEVEL {
        Some(root)
    } else {
        match node_at(mem, root, vpn, level + 1) {
            Some(parent) => {
                if mem.nodes.dom().contains(parent) {
                    let e = mem.nodes[parent].e[pt_index(vpn, level + 1)];
                    if e.present && !e.leaf {
                        Some(e.target)
                    } else {
                        None
                    }
                } else {
                    None
                }
            },
            None => None,
        }
    }
}

/// The entry the walk reads at `level` for `vpn`.
pub open spec fn entry_at(mem: PTMem, root: PFN, vpn: VPage, level: nat) -> Option<Entry> {
    match node_at(mem, root, vpn, level) {
        Some(n) => if mem.nodes.dom().contains(n) {
            Some(mem.nodes[n].e[pt_index(vpn, level)])
        } else {
            None
        },
        None => None,
    }
}

/// Trusted evidence that page table `mem` rooted at `root` is installed and
/// self-mapped. Read-only, shareable.
#[allow(missing_debug_implementations)]
pub tracked struct SelfMapView {
    mem_: PTMem,
    root_: PFN,
}

impl SelfMapView {
    pub closed spec fn mem(self) -> PTMem {
        self.mem_
    }

    pub closed spec fn root(self) -> PFN {
        self.root_
    }

    pub open spec fn wf(self) -> bool {
        &&& wf(self.mem())
        &&& self.mem().nodes.dom().contains(self.root())
        &&& self.mem().level.dom().contains(self.root())
        &&& self.mem().level[self.root()] == ROOT_LEVEL
    }
}

/// The page number a virtual address belongs to (`vaddr >> 12`).
pub uninterp spec fn vpn_of(va: VirtAddr) -> VPage;

/// Trusted self-map read: reading the PTE at the self-map address `addr` for the
/// level-`level` entry of `vpn` returns that entry. Replaces the `unsafe`
/// `PTEntry::read_pte`. The caller passes the ghost `(vpn, level)` it computed
/// the address for; `node_at(..) is Some` says the path to that node exists.
#[verifier::external_body]
pub fn read_pte(
    addr: VirtAddr,
    Tracked(sm): Tracked<&SelfMapView>,
    Ghost(vpn): Ghost<VPage>,
    Ghost(level): Ghost<nat>,
) -> (r: PTEntry)
    requires
        sm.wf(),
        level <= ROOT_LEVEL,
        node_at(sm.mem(), sm.root(), vpn, level) is Some,
        sm.mem().nodes.dom().contains(node_at(sm.mem(), sm.root(), vpn, level)->Some_0),
    ensures
        pte_decode(r) == entry_at(sm.mem(), sm.root(), vpn, level)->Some_0,
{
    // SAFETY: `sm` witnesses that the page table is installed and self-mapped,
    // and `addr` is the self-map address of the level-`level` entry of `vpn`, so
    // this read returns that entry.
    unsafe { *addr.as_ptr::<PTEntry>() }
}

/// Specification of `virt_to_frame`'s result: descend top-down from level 3,
/// stop at the first present leaf (or level-0 page), giving its level. `None`
/// if the page is not mapped.
pub open spec fn vtf_level(mem: PTMem, root: PFN, vpn: VPage) -> Option<nat> {
    let e3 = entry_at(mem, root, vpn, 3);
    let e2 = entry_at(mem, root, vpn, 2);
    let e1 = entry_at(mem, root, vpn, 1);
    let e0 = entry_at(mem, root, vpn, 0);
    if e3 is None || !e3->Some_0.present {
        None
    } else if e2 is None || !e2->Some_0.present {
        None
    } else if e2->Some_0.leaf {
        Some(2nat)
    } else if e1 is None || !e1->Some_0.present {
        None
    } else if e1->Some_0.leaf {
        Some(1nat)
    } else if e0 is Some && e0->Some_0.present {
        Some(0nat)
    } else {
        None
    }
}

/// The walk reaches the root at the top level.
pub proof fn lemma_node_at_root(mem: PTMem, root: PFN, vpn: VPage)
    ensures
        node_at(mem, root, vpn, ROOT_LEVEL) == Some(root),
{
}

/// A present level-3 (PML4) entry is never a leaf (no 512 GB pages), so the walk
/// descends. Needs the root to actually sit at the top level.
pub proof fn lemma_root_entry_interior(mem: PTMem, root: PFN, vpn: VPage)
    requires
        wf(mem),
        mem.nodes.dom().contains(root),
        mem.level.dom().contains(root),
        mem.level[root] == ROOT_LEVEL,
        entry_at(mem, root, vpn, ROOT_LEVEL) is Some,
        entry_at(mem, root, vpn, ROOT_LEVEL)->Some_0.present,
    ensures
        !entry_at(mem, root, vpn, ROOT_LEVEL)->Some_0.leaf,
{
    lemma_node_at_root(mem, root, vpn);
    let idx = pt_index(vpn, ROOT_LEVEL);
    assert(node_wf(mem, root));
    assert(mem.nodes[root].e[idx].present);
}

/// One descent step: from a node with a present interior entry, the next level's
/// node exists and is in the store.
pub proof fn lemma_walk_step(mem: PTMem, root: PFN, vpn: VPage, level: nat)
    requires
        wf(mem),
        1 <= level <= ROOT_LEVEL,
        node_at(mem, root, vpn, level) is Some,
        mem.nodes.dom().contains(node_at(mem, root, vpn, level)->Some_0),
        entry_at(mem, root, vpn, level)->Some_0.present,
        !entry_at(mem, root, vpn, level)->Some_0.leaf,
    ensures
        node_at(mem, root, vpn, (level - 1) as nat) is Some,
        mem.nodes.dom().contains(node_at(mem, root, vpn, (level - 1) as nat)->Some_0),
{
    let n = node_at(mem, root, vpn, level)->Some_0;
    let idx = pt_index(vpn, level);
    let e = mem.nodes[n].e[idx];
    assert(entry_at(mem, root, vpn, level)->Some_0 == e);
    assert(node_wf(mem, n));
    // node_at(level-1) unfolds via node_at((level-1)+1) == node_at(level) == Some(n).
    assert(node_at(mem, root, vpn, (level - 1) as nat) == Some(e.target));
    // e is a present interior entry, so node_wf gives e.target in the store
    // (level-decrease branch) or e.target == n (self-map branch); n is in the store.
    assert(mem.nodes.dom().contains(e.target));
}

} // verus!
