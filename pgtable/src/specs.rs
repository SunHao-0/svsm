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
//   (2) PERMISSIONS - a page-allocator permission (`Page<T>`) tying together a
//       PFN, a raw PPtr, the tracked value, and the deallocation right. A
//       page-table specialization (`PTPagePerm`) records each node's decoded
//       value and level; the root table owns all live node permissions in
//       `PageTablePerms`. A small trusted memory API (`pte_read`/`pte_write`/
//       `pt_page_alloc`/`pt_page_free`) lets `pagetable.rs` drop all page-table
//       `unsafe`.
//
//   (3) PROPERTIES - region typing, the A/D ownership discipline (struct bits are
//       software-exclusive; A/D are co-owned with the MMU and monotone), and the
//       confidentiality goal.
//
// Trusted surface (audited once, replaces all page-table `unsafe`): the external
// type declarations, direct-map relations, `pte_decode`, and the memory API
// functions. Everything else is ordinary verified code.

use crate::address::{Address, PhysAddr, VirtAddr};
use crate::pagetable::{
    PTEntry, PTEntryFlags, PTPage, PageFrame, make_private_address, make_shared_address,
};
use crate::stubs::{PageBox, SvsmError, phys_to_virt, virt_to_phys};
use core::marker::PhantomData;
use core::ptr::NonNull;
use vstd::prelude::*;
use zerocopy::FromZeros;

verus! {

// =====================================================================
// Page permissions: PFN identity + PPtr access handle
// =====================================================================
//
// This is the page-table-specialized analogue of vstd's `PPtr`/`PointsTo`.
// The executable code may carry raw integers around: a PFN is what is encoded in
// a PTE, and a PPtr is just the direct-map virtual address used to access the
// page. Neither integer has authority by itself. The tracked `Page<T>` token is
// the authority connecting the PFN, the PPtr, the tracked value, and the right to
// eventually return the page to the page allocator.

pub spec const PAGE_SIZE: nat = 4096;

/// Physical frame number as an executable value. The conceptual MMU model below
/// uses `PFN = nat`; executable PFNs are related with `pfn as nat`.
pub open spec fn pfn_pa(pfn: usize) -> nat {
    (pfn as nat) * PAGE_SIZE
}

/// Trusted direct-map relation. This intentionally talks about raw integers: a
/// `PPtr<T>` is an address, not a Rust reference or provenance-carrying pointer.
pub uninterp spec fn direct_map_addr(pa: nat) -> usize;

pub uninterp spec fn reverse_direct_map_addr(va: usize) -> nat;

pub open spec fn pptr_matches_pfn<T>(pptr: PPtr<T>, pfn: usize) -> bool {
    &&& pptr.addr() == direct_map_addr(pfn_pa(pfn))
    &&& reverse_direct_map_addr(pptr.addr()) == pfn_pa(pfn)
}

/// A typed raw virtual address. It carries no ownership and can only be used to
/// access memory together with a matching tracked `Page<T>`.
#[allow(missing_debug_implementations)]
pub struct PPtr<T> {
    pub addr: usize,
    pub _pd: PhantomData<T>,
}

impl<T> Copy for PPtr<T> {}

impl<T> Clone for PPtr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> PPtr<T> {
    pub closed spec fn addr(self) -> usize {
        self.addr
    }
}

/// Deallocation authority for one page-allocator page. Kept private inside
/// `Page<T>` so freeing requires consuming the same permission that allowed
/// access.
#[allow(missing_debug_implementations)]
pub tracked struct PageDealloc<T> {
    pfn_: usize,
    pptr_: PPtr<T>,
}

impl<T> PageDealloc<T> {
    pub closed spec fn pfn(self) -> usize {
        self.pfn_
    }

    pub closed spec fn pptr(self) -> PPtr<T> {
        self.pptr_
    }

    pub closed spec fn wf(self) -> bool {
        pptr_matches_pfn(self.pptr(), self.pfn())
    }
}

/// Ownership permission for one page-allocator page.
#[allow(missing_debug_implementations)]
pub tracked struct Page<T> {
    pfn_: usize,
    pptr_: PPtr<T>,
    value_: T,
    dealloc_: PageDealloc<T>,
}

impl<T> Page<T> {
    /// Physical frame / stable identity of this allocation.
    pub closed spec fn pfn(self) -> usize {
        self.pfn_
    }

    /// Raw direct-map pointer through which the page may be accessed.
    pub closed spec fn pptr(self) -> PPtr<T> {
        self.pptr_
    }

    /// The tracked value.
    pub closed spec fn value(self) -> T {
        self.value_
    }

    pub closed spec fn dealloc(self) -> PageDealloc<T> {
        self.dealloc_
    }

    /// The PFN, PPtr and deallocation token all describe the same page.
    pub closed spec fn wf(self) -> bool {
        &&& pptr_matches_pfn(self.pptr(), self.pfn())
        &&& self.dealloc().pfn() == self.pfn()
        &&& self.dealloc().pptr().addr() == self.pptr().addr()
        &&& self.dealloc().wf()
    }

    pub closed spec fn update_value(self, value: T) -> Page<T> {
        Page {
            pfn_: self.pfn_,
            pptr_: self.pptr_,
            value_: value,
            dealloc_: self.dealloc_,
        }
    }
}

/// Borrow the content immutably through a matching PPtr/Page pair.
#[verifier::external_body]
pub fn pptr_borrow<'a, T>(pptr: PPtr<T>, Tracked(perm): Tracked<&'a Page<T>>) -> (r: &'a T)
    requires
        perm.wf(),
        pptr.addr() == perm.pptr().addr(),
    ensures
        *r == perm.value(),
{
    // SAFETY: `perm` witnesses ownership of the `T` at `pptr`.
    unsafe { &*(pptr.addr as *const T) }
}

/// Borrow the content mutably. The returned `&mut T` is tied to the `&mut`
/// borrow of the permission, and the permission tracks the final content.
#[verifier::external_body]
pub fn pptr_borrow_mut<'a, T>(pptr: PPtr<T>, Tracked(perm): Tracked<&'a mut Page<T>>) -> (r: &'a mut T)
    requires
        old(perm).wf(),
        pptr.addr() == old(perm).pptr().addr(),
    ensures
        *r == old(perm).value(),
        final(perm).wf(),
        final(perm).pfn() == old(perm).pfn(),
        final(perm).pptr().addr() == old(perm).pptr().addr(),
        final(perm).value() == *r,
{
    // SAFETY: the exclusive `perm` witnesses sole ownership of the `T` at `pptr`.
    unsafe { &mut *(pptr.addr as *mut T) }
}

/// Read the whole value out by copy.
#[verifier::external_body]
pub fn pptr_read<T: Copy>(pptr: PPtr<T>, Tracked(perm): Tracked<&Page<T>>) -> (v: T)
    requires
        perm.wf(),
        pptr.addr() == perm.pptr().addr(),
    ensures
        v == perm.value(),
{
    // SAFETY: `perm` witnesses ownership of the `T` at `pptr`.
    unsafe { *(pptr.addr as *const T) }
}

/// Overwrite the whole value; the permission tracks the new value.
#[verifier::external_body]
pub fn pptr_write<T>(pptr: PPtr<T>, Tracked(perm): Tracked<&mut Page<T>>, v: T)
    requires
        old(perm).wf(),
        pptr.addr() == old(perm).pptr().addr(),
    ensures
        final(perm).wf(),
        final(perm).pfn() == old(perm).pfn(),
        final(perm).pptr().addr() == old(perm).pptr().addr(),
        final(perm).value() == v,
{
    // SAFETY: the exclusive `perm` witnesses sole ownership of the `T` at `pptr`.
    unsafe {
        *(pptr.addr as *mut T) = v;
    }
}

/// Free a page-allocator page, consuming the only authority that can access it.
#[verifier::external_body]
pub fn free_page<T>(pptr: PPtr<T>, pfn: usize, Tracked(perm): Tracked<Page<T>>)
    requires
        perm.wf(),
        pfn == perm.pfn(),
        pptr.addr() == perm.pptr().addr(),
{
    let ptr = pptr.addr as *mut T;
    let nn = unsafe { NonNull::new_unchecked(ptr) };
    let _ = unsafe { PageBox::from_raw(nn) };
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
            if mem.level[n] == 0 || e.leaf {
                // Level-0 entries are 4K leaves even though x86 does not set
                // the HUGE bit there. Huge leaves may additionally appear at
                // levels 1 and 2. In all leaf cases, the base frame is aligned
                // to the page size selected by the current level.
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
// (2) Permissions: root-owned page-table page capabilities
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
pub struct ExPTPage(PTPage);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(missing_debug_implementations)]
pub struct ExPTEntryFlags(PTEntryFlags);

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

#[verifier::external_body]
pub fn svsm_mem_error() -> SvsmError {
    SvsmError::Mem
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(missing_debug_implementations)]
pub struct ExPageFrame(PageFrame);

/// Decode a concrete `PTEntry`'s bits into the abstract `Entry`.
pub uninterp spec fn pte_decode(e: PTEntry) -> Entry;

/// A raw access handle for the concrete `PTPage` backing a logical `PTNode`.
/// The handle is only an address. It can read/write entries only with a matching
/// `PTPagePerm`.
#[allow(missing_debug_implementations)]
pub struct PTPagePtr {
    pub pptr: PPtr<PTNode>,
}

impl Copy for PTPagePtr {}

impl Clone for PTPagePtr {
    fn clone(&self) -> Self {
        *self
    }
}

impl PTPagePtr {
    pub closed spec fn addr(self) -> usize {
        self.pptr.addr()
    }
}

/// Ownership permission for one live page-table node.
///
/// `page_` is a page-allocator permission whose value is the decoded logical
/// `PTNode`. `level_` records where the node sits in the paging tree, which is
/// necessary to prove parent-child links decrease levels and huge-page leaves are
/// aligned correctly.
#[allow(missing_debug_implementations)]
pub tracked struct PTPagePerm {
    page_: Page<PTNode>,
    level_: nat,
}

impl PTPagePerm {
    pub closed spec fn page(self) -> Page<PTNode> {
        self.page_
    }

    /// Physical frame / identity of this node.
    pub closed spec fn pfn(self) -> usize {
        self.page().pfn()
    }

    pub closed spec fn pptr(self) -> PPtr<PTNode> {
        self.page().pptr()
    }

    pub closed spec fn value(self) -> PTNode {
        self.page().value()
    }

    pub closed spec fn level(self) -> nat {
        self.level_
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.page().wf()
        &&& self.level() <= ROOT_LEVEL
        &&& self.value().wf()
    }

    pub closed spec fn update_value(self, value: PTNode) -> PTPagePerm {
        PTPagePerm { page_: self.page().update_value(value), level_: self.level_ }
    }
}

/// All live page-table-page permissions owned by one root table. This is the
/// tracked state that verified page-table operations should thread through.
#[allow(missing_debug_implementations)]
pub tracked struct PageTablePerms {
    root_: PFN,
    pages_: Map<PFN, PTPagePerm>,
}

impl PageTablePerms {
    pub closed spec fn root(self) -> PFN {
        self.root_
    }

    pub closed spec fn pages(self) -> Map<PFN, PTPagePerm> {
        self.pages_
    }

    /// View the held permissions as the conceptual page-table memory.
    pub open spec fn mem(self) -> PTMem {
        PTMem {
            nodes: Map::new(
                |p: PFN| self.pages().dom().contains(p),
                |p: PFN| self.pages()[p].value(),
            ),
            level: Map::new(
                |p: PFN| self.pages().dom().contains(p),
                |p: PFN| self.pages()[p].level(),
            ),
        }
    }

    /// The root permission set invariant. The map key is the abstract PFN; each
    /// token also carries the executable PFN returned by the allocator, and these
    /// must agree.
    pub open spec fn wf(self) -> bool {
        &&& self.pages().dom().contains(self.root())
        &&& self.pages()[self.root()].level() == ROOT_LEVEL
        &&& forall|p: PFN| #[trigger] self.pages().dom().contains(p) ==> {
            &&& self.pages()[p].wf()
            &&& self.pages()[p].pfn() as nat == p
        }
        &&& wf(self.mem())
        &&& ad_pinned(self.mem())
    }

    /// The access handle for the root node. Lets `PageTable.inv()` anchor its
    /// stored root PPtr to the permission map without a trusted accessor.
    pub open spec fn root_pptr(self) -> PPtr<PTNode> {
        self.pages()[self.root()].pptr()
    }

    /// The currently published entry `(parent, idx)` points at `child`.
    pub open spec fn interior_link(self, parent: PFN, idx: nat, child: PFN) -> bool {
        &&& self.pages().dom().contains(parent)
        &&& self.pages().dom().contains(child)
        &&& idx < ENTRIES
        &&& self.pages()[parent].value().e.dom().contains(idx)
        &&& self.pages()[parent].value().e[idx].present
        &&& !self.pages()[parent].value().e[idx].leaf
        &&& self.pages()[parent].value().e[idx].target == child
        &&& if parent == self.root() && idx == IDX_SELFMAP {
            child == parent && self.pages()[child].level() == self.pages()[parent].level()
        } else {
            self.pages()[parent].level() >= 1
                && self.pages()[child].level() == self.pages()[parent].level() - 1
        }
    }

    /// A PTE decoded as an interior entry can be dereferenced only if the
    /// corresponding page permission is live in this root's permission map.
    pub open spec fn interior_entry_has_perm(self, e: Entry) -> bool {
        e.present && !e.leaf ==> self.pages().dom().contains(e.target)
    }

    /// No published interior entry points at `child`. This is the condition the
    /// unmap path needs before removing and freeing a page-table page permission.
    pub open spec fn detached(self, child: PFN) -> bool {
        forall|p: PFN, i: nat| #![trigger self.pages()[p].value().e[i]]
            (self.pages().dom().contains(p)
                && i < ENTRIES
                && self.pages()[p].value().e.dom().contains(i)
                && self.pages()[p].value().e[i].present
                && !self.pages()[p].value().e[i].leaf)
                ==> self.pages()[p].value().e[i].target != child
    }

    pub open spec fn can_free(self, child: PFN) -> bool {
        &&& child != self.root()
        &&& self.pages().dom().contains(child)
        &&& self.detached(child)
    }

    /// Preconditions for the atomic "insert child permission + publish parent
    /// PTE" step used by allocation-on-walk code.
    pub open spec fn can_publish_child(
        self,
        parent: PFN,
        idx: nat,
        child: PFN,
        child_perm: PTPagePerm,
        e: Entry,
    ) -> bool {
        &&& self.wf()
        &&& self.pages().dom().contains(parent)
        &&& !self.pages().dom().contains(child)
        &&& idx < ENTRIES
        &&& self.pages()[parent].level() >= 1
        &&& child_perm.wf()
        &&& child_perm.pfn() as nat == child
        &&& child_perm.level() == self.pages()[parent].level() - 1
        &&& child_perm.value().empty()
        &&& e.present
        &&& !e.leaf
        &&& e.target == child
        &&& permissive(e)
        &&& entry_pinned(e)
    }

    pub closed spec fn publish_child(
        self,
        parent: PFN,
        idx: nat,
        child: PFN,
        child_perm: PTPagePerm,
        e: Entry,
    ) -> PageTablePerms {
        self.insert_page(child, child_perm).update_entry(parent, idx, e)
    }

    /// Conditions under which overwriting one PTE preserves the root-owned
    /// permission-map invariant. This captures the page-table write discipline:
    /// absent entries are always safe, level-0 entries are 4K leaves, huge leaves
    /// must be aligned to their level, and interior entries may only target live
    /// child permissions at the next lower level.
    pub open spec fn can_set_entry(self, node: PFN, idx: nat, e: Entry) -> bool {
        &&& self.wf()
        &&& self.pages().dom().contains(node)
        &&& idx < ENTRIES
        &&& if e.present {
            &&& entry_pinned(e)
            &&& if self.pages()[node].level() == 0 || e.leaf {
                &&& self.pages()[node].level() <= 2
                &&& e.target % span(self.pages()[node].level()) == 0
            } else {
                &&& self.pages().dom().contains(e.target)
                &&& if node == self.root() && idx == IDX_SELFMAP {
                    e.target == node
                        && self.pages()[e.target].level() == self.pages()[node].level()
                } else {
                    self.pages()[node].level() >= 1
                        && self.pages()[e.target].level() == self.pages()[node].level() - 1
                }
            }
        } else {
            true
        }
    }

    pub closed spec fn update_entry(self, p: PFN, idx: nat, e: Entry) -> PageTablePerms {
        let old_perm = self.pages_[p];
        let new_node = old_perm.value().update(idx, e);
        let new_perm = old_perm.update_value(new_node);
        PageTablePerms { root_: self.root_, pages_: self.pages_.insert(p, new_perm) }
    }

    pub closed spec fn insert_page(self, p: PFN, perm: PTPagePerm) -> PageTablePerms {
        PageTablePerms { root_: self.root_, pages_: self.pages_.insert(p, perm) }
    }

    pub closed spec fn remove_page(self, p: PFN) -> PageTablePerms {
        PageTablePerms { root_: self.root_, pages_: self.pages_.remove(p) }
    }
}

// --- trusted memory API (encapsulates ALL page-table `unsafe`) -------

/// Read entry `idx`. Replaces `unsafe PTEntry::read_pte` / `from_vaddr` indexing.
#[verifier::external_body]
pub fn pte_read(p: &PTPagePtr, idx: usize, Tracked(perm): Tracked<&PTPagePerm>) -> (r: PTEntry)
    requires
        perm.wf(),
        p.addr() == perm.pptr().addr(),
        idx < 512,
    ensures
        pte_decode(r) == perm.value().e[idx as nat],
{
    // SAFETY: `perm` witnesses ownership of the node at `p.pptr`; `idx < 512`
    // keeps the read in bounds.
    let page: &PTPage = unsafe { &*(p.pptr.addr as *const PTPage) };
    page[idx]
}

/// Write entry `idx`. Replaces the `&mut`-aliased writes behind `PTEntry::set`/
/// `clear` reached via `from_vaddr`. Tracks the new value precisely.
#[verifier::external_body]
pub fn pte_write(p: &PTPagePtr, idx: usize, e: PTEntry, Tracked(perm): Tracked<&mut PTPagePerm>)
    requires
        old(perm).wf(),
        p.addr() == old(perm).pptr().addr(),
        idx < 512,
    ensures
        final(perm).wf(),
        final(perm).pfn() == old(perm).pfn(),
        final(perm).pptr().addr() == old(perm).pptr().addr(),
        final(perm).level() == old(perm).level(),
        final(perm).value() == old(perm).value().update(idx as nat, pte_decode(e)),
{
    // SAFETY: the exclusive `perm` witnesses sole ownership of the node at
    // `p.pptr`; `idx < 512` keeps the write in bounds.
    let page: &mut PTPage = unsafe { &mut *(p.pptr.addr as *mut PTPage) };
    page[idx] = e;
}

/// Read entry `idx` through the root-owned permission map. This is the operation
/// verified walks should use once they know the PFN of the current node.
#[verifier::external_body]
pub fn pt_read_entry(
    p: &PTPagePtr,
    Ghost(node): Ghost<PFN>,
    idx: usize,
    Tracked(perms): Tracked<&PageTablePerms>,
) -> (r: PTEntry)
    requires
        perms.wf(),
        perms.pages().dom().contains(node),
        p.addr() == perms.pages()[node].pptr().addr(),
        idx < 512,
    ensures
        pte_decode(r) == perms.pages()[node].value().e[idx as nat],
{
    // SAFETY: `perms` owns the node permission keyed by `node`, and `p` is its
    // matching PPtr.
    let page: &PTPage = unsafe { &*(p.pptr.addr as *const PTPage) };
    page[idx]
}

/// Atomically write one PTE and update the root-owned logical permission map.
/// This is the key bridge for verified map/unmap code: the concrete store and
/// the tracked `PTMem` view move together.
#[verifier::external_body]
pub fn pt_write_entry(
    p: &PTPagePtr,
    Ghost(node): Ghost<PFN>,
    idx: usize,
    e: PTEntry,
    Tracked(perms): Tracked<&mut PageTablePerms>,
)
    requires
        old(perms).can_set_entry(node, idx as nat, pte_decode(e)),
        p.addr() == old(perms).pages()[node].pptr().addr(),
        idx < 512,
    ensures
        *final(perms) == old(perms).update_entry(node, idx as nat, pte_decode(e)),
        final(perms).wf(),
        final(perms).root() == old(perms).root(),
        final(perms).root_pptr().addr() == old(perms).root_pptr().addr(),
{
    // SAFETY: `perms` owns the node permission keyed by `node`, and
    // `can_set_entry` states that publishing this decoded entry preserves all
    // root-owned page-table invariants.
    let page: &mut PTPage = unsafe { &mut *(p.pptr.addr as *mut PTPage) };
    page[idx] = e;
}

/// Atomically insert a freshly allocated child permission and publish the parent
/// entry that points at it.
#[verifier::external_body]
pub fn pt_publish_child(
    p: &PTPagePtr,
    Ghost(parent): Ghost<PFN>,
    idx: usize,
    e: PTEntry,
    Ghost(child): Ghost<PFN>,
    Tracked(child_perm): Tracked<PTPagePerm>,
    Tracked(perms): Tracked<&mut PageTablePerms>,
)
    requires
        old(perms).can_publish_child(parent, idx as nat, child, child_perm, pte_decode(e)),
        p.addr() == old(perms).pages()[parent].pptr().addr(),
        idx < 512,
    ensures
        *final(perms) == old(perms).publish_child(parent, idx as nat, child, child_perm, pte_decode(e)),
        final(perms).wf(),
        final(perms).pages().dom().contains(child),
        final(perms).pages()[child].level() == old(perms).pages()[parent].level() - 1,
        final(perms).pages()[child].pptr().addr() == child_perm.pptr().addr(),
        final(perms).pages()[parent].value().e[idx as nat] == pte_decode(e),
        final(perms).root() == old(perms).root(),
        final(perms).root_pptr().addr() == old(perms).root_pptr().addr(),
{
    // SAFETY: `perms` owns the parent node, and the consumed `child_perm` proves
    // the allocated child page is live before the parent PTE is published.
    let page: &mut PTPage = unsafe { &mut *(p.pptr.addr as *mut PTPage) };
    page[idx] = e;
}

/// Allocate a page-table page fresh with respect to a root permission map.
#[verifier::external_body]
pub fn pt_page_alloc_fresh(
    level: usize,
    Tracked(perms): Tracked<&PageTablePerms>,
) -> (r: Result<(PTPagePtr, usize, Tracked<PTPagePerm>), SvsmError>)
    requires
        perms.wf(),
        level <= 3,
    ensures
        r matches Ok((ptr, pfn, perm)) ==> {
            &&& perm@.wf()
            &&& perm@.pfn() == pfn
            &&& perm@.pptr().addr() == ptr.addr()
            &&& perm@.level() == level as nat
            &&& perm@.value().empty()
            &&& !perms.pages().dom().contains(pfn as nat)
        },
{
    let pb: PageBox<PTPage> = PageBox::try_new_zeroed()?;
    let vaddr = pb.vaddr();
    let paddr = virt_to_phys(vaddr);
    let pfn = paddr.bits() >> 12;
    let _leaked: &'static mut PTPage = PageBox::leak(pb);
    Ok((
        PTPagePtr { pptr: PPtr { addr: vaddr.bits(), _pd: PhantomData } },
        pfn,
        Tracked::assume_new(),
    ))
}

/// Allocate the root page-table page and mint the root-owned permission map.
/// The concrete root page is represented in `PageTable` by the returned PPtr;
/// the permission map owns the actual page-table-page authority.
#[verifier::external_body]
pub fn pt_root_alloc() -> (r: Result<(PTPagePtr, usize, Tracked<PageTablePerms>), SvsmError>)
    ensures
        r matches Ok((ptr, pfn, perms)) ==> {
            &&& perms@.wf()
            &&& perms@.root() == pfn as nat
            &&& perms@.pages().dom().contains(pfn as nat)
            &&& perms@.pages()[pfn as nat].pptr().addr() == ptr.addr()
            &&& perms@.pages()[pfn as nat].level() == ROOT_LEVEL
        },
{
    let pb: PageBox<PTPage> = PageBox::try_new_zeroed()?;
    let vaddr = pb.vaddr();
    let paddr = virt_to_phys(vaddr);
    let pfn = paddr.bits() >> 12;
    let root = PageBox::leak(pb);

    let flags = PTEntryFlags::PRESENT
        | PTEntryFlags::WRITABLE
        | PTEntryFlags::ACCESSED
        | PTEntryFlags::DIRTY
        | PTEntryFlags::NX;
    root[493].set(make_private_address(paddr), flags);

    Ok((
        PTPagePtr { pptr: PPtr { addr: vaddr.bits(), _pd: PhantomData } },
        pfn,
        Tracked::assume_new(),
    ))
}

/// Free a node, consuming its permission. The parent entry pointing at this PFN
/// must have been cleared before the caller removes the permission from
/// `PageTablePerms`.
#[verifier::external_body]
pub fn pt_page_free(p: PTPagePtr, pfn: usize, Tracked(perm): Tracked<PTPagePerm>)
    requires
        perm.wf(),
        pfn == perm.pfn(),
        p.addr() == perm.pptr().addr(),
{
    // SAFETY: consuming `perm` proves no other reference exists; the handle came
    // from `pt_page_alloc`, so this frees exactly that allocation.
    let ptr = p.pptr.addr as *mut PTPage;
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

/// Handle to the child node a present interior entry points at. The raw PFN
/// decoded from the PTE is not enough to access memory; the root-owned permission
/// map must contain the matching `PTPagePerm`.
#[verifier::external_body]
pub fn entry_child(e: PTEntry, Tracked(perms): Tracked<&PageTablePerms>) -> (p: PTPagePtr)
    requires
        perms.wf(),
        pte_decode(e).present,
        !pte_decode(e).leaf,
    ensures
        perms.pages().dom().contains(pte_decode(e).target),
        p.addr() == perms.pages()[pte_decode(e).target].pptr().addr(),
{
    PTPagePtr {
        pptr: PPtr { addr: phys_to_virt(e.address()).bits(), _pd: PhantomData },
    }
}

#[verifier::external_body]
pub proof fn lemma_interior_child_level(
    perms: PageTablePerms,
    parent: PFN,
    idx: nat,
    e: Entry,
)
    requires
        perms.wf(),
        perms.pages().dom().contains(parent),
        idx < ENTRIES,
        perms.pages()[parent].value().e[idx] == e,
        e.present,
        !e.leaf,
        !(parent == perms.root() && idx == IDX_SELFMAP),
    ensures
        perms.pages().dom().contains(e.target),
        perms.pages()[parent].level() >= 1,
        perms.pages()[e.target].level() == perms.pages()[parent].level() - 1,
{
}

/// The page-table index of `vaddr` at paging `level` (0=PT .. 3=PML4).
/// Trusted wrapper over `VirtAddr::to_pgtbl_idx`; only the `< 512` bound is
/// needed to discharge the `idx < ENTRIES` side conditions of the memory API.
#[verifier::external_body]
pub fn pt_index_exec(vaddr: VirtAddr, level: usize) -> (r: usize)
    requires
        level <= 3,
    ensures
        r < 512,
{
    (vaddr.bits() >> (12 + level * 9)) & 0x1ff
}

/// The executable level-3 self-map index, tied to the spec constant
/// `IDX_SELFMAP` so verified code can exclude the self-map slot.
pub fn idx_selfmap() -> (r: usize)
    ensures
        r as nat == IDX_SELFMAP,
{
    493
}

pub open spec fn entry_absent() -> Entry {
    Entry {
        present: false,
        leaf: false,
        target: 0,
        w: false,
        user: false,
        nx: false,
        global: false,
        enc: false,
        accessed: false,
        dirty: false,
    }
}

pub open spec fn entry_interior(child: usize) -> Entry {
    Entry {
        present: true,
        leaf: false,
        target: child as nat,
        w: true,
        user: true,
        nx: false,
        global: false,
        enc: true,
        accessed: true,
        dirty: true,
    }
}

pub uninterp spec fn entry_map_4k(paddr: PhysAddr, flags: PTEntryFlags, shared: bool) -> Entry;

pub open spec fn valid_map_4k_entry(e: Entry) -> bool {
    &&& e.present
    &&& !e.leaf
    &&& entry_pinned(e)
    &&& e.target % span(0) == 0
}

/// Build an interior page-table PTE pointing at a child page-table page.
#[verifier::external_body]
pub fn make_interior_pte(child_pfn: usize) -> (e: PTEntry)
    ensures
        pte_decode(e) == entry_interior(child_pfn),
        permissive(entry_interior(child_pfn)),
        entry_pinned(entry_interior(child_pfn)),
{
    let mut e = PTEntry::new_zeroed();
    let flags = PTEntryFlags::PRESENT
        | PTEntryFlags::WRITABLE
        | PTEntryFlags::USER
        | PTEntryFlags::ACCESSED
        | PTEntryFlags::DIRTY;
    e.set(make_private_address(PhysAddr::from(child_pfn << 12)), flags);
    e
}

/// Build the concrete 4K leaf PTE used by `map_4k`. The ACCESSED and DIRTY bits
/// are forced on so the published leaf is A/D-pinned (`entry_pinned`) regardless
/// of the caller's `flags`. This keeps the whole table A/D-pinned, which is what
/// makes the MMU's only concurrent write (raising ACCESSED) a no-op and hence
/// `&mut PageTable` sound (see `lemma_ad_pin_accessed_noop`).
#[verifier::external_body]
pub fn make_map_4k_leaf(paddr: PhysAddr, flags: PTEntryFlags, shared: bool) -> (e: PTEntry)
    ensures
        pte_decode(e) == entry_map_4k(paddr, flags, shared),
        valid_map_4k_entry(entry_map_4k(paddr, flags, shared)),
{
    let addr = if !shared {
        make_private_address(paddr)
    } else {
        make_shared_address(paddr)
    };
    let flags = flags | PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY;
    let mut e = PTEntry::new_zeroed();
    e.set(addr, flags);
    e
}

pub uninterp spec fn entry_map_2m(paddr: PhysAddr, flags: PTEntryFlags, shared: bool) -> Entry;

/// A valid 2M huge leaf lives at level 1: it is a present, A/D-pinned leaf whose
/// target frame is aligned to the 2M span (`span(1) == 512` 4K frames).
pub open spec fn valid_map_2m_entry(e: Entry) -> bool {
    &&& e.present
    &&& e.leaf
    &&& entry_pinned(e)
    &&& e.target % span(1) == 0
}

/// Build the concrete 2M huge leaf PTE used by `map_2m`. Like `make_map_4k_leaf`,
/// the HUGE/ACCESSED/DIRTY bits are forced on so the published leaf is A/D-pinned.
/// The 2M-alignment of `paddr` is a caller obligation (guarded at runtime); under
/// it, the encoded target frame is 512-aligned (`valid_map_2m_entry`).
#[verifier::external_body]
pub fn make_map_2m_leaf(paddr: PhysAddr, flags: PTEntryFlags, shared: bool) -> (e: PTEntry)
    ensures
        pte_decode(e) == entry_map_2m(paddr, flags, shared),
        valid_map_2m_entry(entry_map_2m(paddr, flags, shared)),
{
    let addr = if !shared {
        make_private_address(paddr)
    } else {
        make_shared_address(paddr)
    };
    let flags = flags | PTEntryFlags::HUGE | PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY;
    let mut e = PTEntry::new_zeroed();
    e.set(addr, flags);
    e
}

/// A cleared (not-present) entry, for unmap.
#[verifier::external_body]
pub fn absent_entry() -> (e: PTEntry)
    ensures
        pte_decode(e) == entry_absent(),
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
pub proof fn lemma_page_table_perms_mem_node(perms: PageTablePerms, p: PFN)
    requires
        perms.pages().dom().contains(p),
    ensures
        perms.mem().nodes.dom().contains(p),
        perms.mem().nodes[p] == perms.pages()[p].value(),
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
#[verifier::external_body]
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
