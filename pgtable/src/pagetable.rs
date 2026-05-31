// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::BIT_MASK;
use crate::address::{Address, PhysAddr, VirtAddr};
use crate::memory_region::MemoryRegion;
use crate::stubs::{
    PageBox, SvsmError, flush_tlb_global_sync, phys_to_virt, virt_to_phys, write_cr3,
};
use crate::types::{PAGE_SIZE, PAGE_SIZE_1G, PAGE_SIZE_2M, PageSize};
use bitflags::bitflags;
use core::ops::{Index, IndexMut};
use core::ptr::NonNull;
use cpuarch::x86::CR0Flags;
use cpuarch::x86::CR4Flags;
use cpuarch::x86::EFERFlags;
use zerocopy::FromBytes;
use zerocopy::FromZeros;

#[cfg(verus_only)]
use crate::specs::{
    IDX_SELFMAP, PFN, PTPagePtr, PageTablePerms, ROOT_LEVEL, absent_entry, entry_child, entry_huge,
    entry_present, idx_selfmap, lemma_interior_child_level, make_interior_pte, make_map_2m_leaf,
    make_map_4k_leaf, pt_index_exec, pt_page_alloc_fresh, pt_publish_child, pt_read_entry,
    pt_root_alloc, pt_write_entry, pte_decode, svsm_mem_error,
};
#[cfg(verus_only)]
use vstd::prelude::*;

/// Number of entries in a page table (4KB/8B).
pub const ENTRY_COUNT: usize = 512;

// Page-table self-map constants (inlined from kernel/src/mm/address_space.rs).

/// Computes the canonical virtual base address for a top-level (PML4) index.
pub const fn virt_from_idx(idx: usize) -> VirtAddr {
    VirtAddr::new(idx << ((3 * 9) + 12))
}

/// Level-3 (PML4) index for the shared half of the address space.
pub const PGTABLE_LVL3_IDX_SHARED: usize = 511;

/// Level-3 (PML4) index used for the page-table self-map.
pub const PGTABLE_LVL3_IDX_PTE_SELFMAP: usize = 493;

/// Virtual base address of the page-table self-map.
pub const SVSM_PTE_BASE: VirtAddr = virt_from_idx(PGTABLE_LVL3_IDX_PTE_SELFMAP);

const PHYS_ADDR_SIZE: usize = 48;

/// Returns the private encrypt mask value.
pub fn private_pte_mask() -> usize {
    todo!()
}

/// Returns the shared encrypt mask value.
fn shared_pte_mask() -> usize {
    todo!()
}

/// Returns the exclusive end of the physical address space.
pub fn max_phys_addr() -> PhysAddr {
    todo!()
}

/// Returns the supported flags considering the feature mask (all flags here).
fn supported_flags(flags: PTEntryFlags) -> PTEntryFlags {
    todo!()
}

/// Set address as shared via mask.
pub fn make_shared_address(paddr: PhysAddr) -> PhysAddr {
    (strip_confidentiality_bits(paddr).bits() | shared_pte_mask()).into()
}

/// Set address as private via mask.
pub fn make_private_address(paddr: PhysAddr) -> PhysAddr {
    (strip_shared_address_bits(paddr).bits() | private_pte_mask()).into()
}

// Returns true if the address is shared.
fn is_shared(paddr: PhysAddr) -> bool {
    paddr == make_shared_address(paddr)
}

fn strip_confidentiality_bits(paddr: PhysAddr) -> PhysAddr {
    (paddr.bits() & !private_pte_mask()).into()
}

fn strip_shared_address_bits(paddr: PhysAddr) -> PhysAddr {
    (paddr.bits() & !shared_pte_mask()).into()
}

bitflags! {
    #[derive(Copy, Clone, Debug, Default)]
    pub struct PTEntryFlags: u64 {
        const PRESENT       = 1 << 0;
        const WRITABLE      = 1 << 1;
        const USER      = 1 << 2;
        const ACCESSED      = 1 << 5;
        const DIRTY     = 1 << 6;
        const HUGE      = 1 << 7;
        const GLOBAL        = 1 << 8;
        const NX        = 1 << 63;
    }
}

impl PTEntryFlags {
    pub fn exec() -> Self {
        Self::PRESENT | Self::GLOBAL | Self::ACCESSED
    }

    pub fn data() -> Self {
        Self::PRESENT | Self::GLOBAL | Self::WRITABLE | Self::NX | Self::ACCESSED | Self::DIRTY
    }

    pub fn data_ro() -> Self {
        Self::PRESENT | Self::GLOBAL | Self::NX | Self::ACCESSED
    }

    pub fn task_exec() -> Self {
        Self::PRESENT | Self::ACCESSED
    }

    pub fn task_data() -> Self {
        Self::PRESENT | Self::WRITABLE | Self::NX | Self::ACCESSED | Self::DIRTY
    }

    pub fn task_data_ro() -> Self {
        Self::PRESENT | Self::NX | Self::ACCESSED
    }
}

/// Represents a page table entry.
#[repr(C)]
#[derive(Copy, Clone, Debug, FromBytes)]
pub struct PTEntry(PhysAddr);

impl PTEntry {
    /// Check if the page table entry is clear (null).
    pub fn is_clear(&self) -> bool {
        self.0.is_null()
    }

    /// Clear the page table entry.
    pub fn clear(&mut self) {
        self.0 = PhysAddr::null();
    }

    /// Check if the page table entry is present.
    pub fn present(&self) -> bool {
        self.flags().contains(PTEntryFlags::PRESENT)
    }

    /// Check if the page table entry is huge.
    pub fn huge(&self) -> bool {
        self.flags().contains(PTEntryFlags::HUGE)
    }

    /// Check if the page table entry is writable.
    pub fn writable(&self) -> bool {
        self.flags().contains(PTEntryFlags::WRITABLE)
    }

    /// Check if the page table entry is NX (no-execute).
    pub fn nx(&self) -> bool {
        self.flags().contains(PTEntryFlags::NX)
    }

    /// Check if the page table entry is user-accessible.
    pub fn user(&self) -> bool {
        self.flags().contains(PTEntryFlags::USER)
    }

    /// Check if the page table entry is global.
    pub fn global(&self) -> bool {
        self.flags().contains(PTEntryFlags::GLOBAL)
    }

    /// Get the raw bits (`u64`) of the page table entry.
    pub fn raw(&self) -> u64 {
        self.0.bits() as u64
    }

    /// Get the flags of the page table entry.
    pub fn flags(&self) -> PTEntryFlags {
        PTEntryFlags::from_bits_truncate(self.0.bits() as u64)
    }

    /// Set the page table entry with the specified address and flags.
    pub fn set_unrestricted(&mut self, addr: PhysAddr, flags: PTEntryFlags) {
        let addr = addr.bits() as u64;
        assert_eq!(addr & !0x000f_ffff_ffff_f000, 0);
        self.0 = PhysAddr::from(addr | flags.bits());
    }

    /// Set the page table entry with the specified address, with flags
    /// constrained to the supported feature flags.
    pub fn set(&mut self, addr: PhysAddr, flags: PTEntryFlags) {
        self.set_unrestricted(addr, supported_flags(flags));
    }

    /// Inserts the private address mask if the page is present.
    pub fn make_private_if_present(&mut self) {
        if self.flags().contains(PTEntryFlags::PRESENT) {
            self.0 = make_private_address(self.0);
        }
    }

    /// Get the address from the page table entry, including the shared bit.
    pub fn page_frame(&self) -> PhysAddr {
        let addr = PhysAddr::from(self.0.bits() & 0x000f_ffff_ffff_f000);
        strip_confidentiality_bits(addr)
    }

    /// Get the address from the page table entry, excluding the C/shared bit.
    pub fn address(&self) -> PhysAddr {
        strip_shared_address_bits(self.page_frame())
    }

    /// Read a page table entry from the specified virtual address.
    ///
    /// # Safety
    ///
    /// Reads from an arbitrary virtual address, making this essentially a
    /// raw pointer read.  The caller must be certain to calculate the correct
    /// address.
    pub unsafe fn read_pte(vaddr: VirtAddr) -> Self {
        // SAFETY: When the methods safety requirements are met, the raw
        // pointer read is safe.
        unsafe { *vaddr.as_ptr::<Self>() }
    }
}

/// A pagetable page with multiple entries.
#[repr(C)]
#[derive(Debug, FromBytes)]
pub struct PTPage {
    entries: [PTEntry; ENTRY_COUNT],
}

impl PTPage {
    /// Allocates a zeroed pagetable page and returns a `PageBox` containing
    /// the allocation.
    ///
    /// # Errors
    ///
    /// Returns [`SvsmError`] if the page cannot be allocated.
    pub fn alloc_box() -> Result<PageBox<Self>, SvsmError> {
        PageBox::try_new_zeroed()
    }

    /// Allocates a zeroed pagetable page and returns a mutable reference to
    /// it, plus its physical address.
    ///
    /// # Errors
    ///
    /// Returns [`SvsmError`] if the page cannot be allocated.
    fn alloc() -> Result<(&'static mut Self, PhysAddr), SvsmError> {
        let page = Self::alloc_box()?;
        let paddr = virt_to_phys(page.vaddr());
        Ok((PageBox::leak(page), paddr))
    }

    /// Frees a pagetable page.
    ///
    /// # Safety
    ///
    /// The given reference must correspond to a valid previously allocated
    /// page table page.
    unsafe fn free(page: &'static Self) {
        // SAFETY: The page put into the PageBox is a previously allocated
        // page table page.
        unsafe {
            let _ = PageBox::from_raw(NonNull::from(page));
        }
    }

    /// Converts a pagetable entry to a mutable reference to a [`PTPage`],
    /// if the entry is present and not huge.
    fn from_entry(entry: PTEntry) -> Option<&'static mut Self> {
        let flags = entry.flags();
        if !flags.contains(PTEntryFlags::PRESENT) || flags.contains(PTEntryFlags::HUGE) {
            return None;
        }

        let address = phys_to_virt(entry.address());
        // SAFETY: Every PTEntry points to a previously allocated page-table
        // page, so this pointer dereference is safe.
        Some(unsafe { Self::from_vaddr(address) })
    }

    /// Generates a `PTPage` from a virtual address.
    /// # Safety
    /// The caller must ensure that the virtual address is a valid page table.
    pub unsafe fn from_vaddr(vaddr: VirtAddr) -> &'static mut Self {
        // SAFETY: the caller guarantees the correctness of the virtual
        // address.
        unsafe { &mut *vaddr.as_mut_ptr::<PTPage>() }
    }
}

/// Can be used to access page table entries by index.
impl Index<usize> for PTPage {
    type Output = PTEntry;

    fn index(&self, index: usize) -> &PTEntry {
        &self.entries[index]
    }
}

/// Can be used to modify page table entries by index.
impl IndexMut<usize> for PTPage {
    fn index_mut(&mut self, index: usize) -> &mut PTEntry {
        &mut self.entries[index]
    }
}

/// Raw, borrow-based mapping levels of page table entries.
///
/// This is the original `&mut PTEntry`-based view. It is used only by the
/// untracked [`RawPageTablePart`] subtree, whose pages are not owned by the
/// root permission map and therefore cannot be threaded through the verified
/// permission API. The verified `PageTable` uses the location-based [`Mapping`]
/// defined in the `verus!` block at the end of this file.
#[derive(Debug)]
pub enum RawMapping<'a> {
    Level3(&'a mut PTEntry),
    Level2(&'a mut PTEntry),
    Level1(&'a mut PTEntry),
    Level0(&'a mut PTEntry),
}

/// Dereference the page-table entry identified by a location-based [`Mapping`]
/// slot.
///
/// # Safety
/// `loc.ptr` must address a live page-table page owned by the root permission
/// map and `loc.idx` must be `< 512`; both hold for any `loc` produced by the
/// verified `walk_addr`/`alloc_pte_*` helpers. This is the trusted bridge that
/// lets the not-yet-verified huge-page / region / shared-state methods mutate
/// an entry identified only by its `(ptr, idx)` location.
#[cfg(verus_only)]
#[inline]
unsafe fn loc_entry_mut<'a>(loc: &PTLoc) -> &'a mut PTEntry {
    unsafe { &mut (*(loc.ptr.pptr.addr as *mut PTPage)).entries[loc.idx] }
}

/// A physical address within a page frame
#[derive(Clone, Copy, Debug)]
pub enum PageFrame {
    Size4K(PhysAddr),
    Size2M(PhysAddr),
    Size1G(PhysAddr),
}

impl PageFrame {
    /// Get the address from the page frame, including the shared bit.
    pub fn page_frame(&self) -> PhysAddr {
        let paddr = match *self {
            Self::Size4K(pa) => pa,
            Self::Size2M(pa) => pa,
            Self::Size1G(pa) => pa,
        };
        strip_confidentiality_bits(paddr)
    }

    /// Get the address from the page frame, excluding the C/shared bit.
    pub fn address(&self) -> PhysAddr {
        strip_shared_address_bits(self.page_frame())
    }

    pub fn size(&self) -> usize {
        match self {
            Self::Size4K(_) => PAGE_SIZE,
            Self::Size2M(_) => PAGE_SIZE_2M,
            Self::Size1G(_) => PAGE_SIZE_1G,
        }
    }

    pub fn start(&self) -> PhysAddr {
        let end = self.address().bits() & !(self.size() - 1);
        end.into()
    }

    pub fn end(&self) -> PhysAddr {
        self.start() + self.size()
    }
}

/// Page table structure containing a root page with multiple entries.
///
/// The concrete root page is owned by the tracked `perms`; `root` is just the
/// access handle (direct-map pointer) anchored to it by `inv()`. The struct and
/// the verified operations on it live in the `verus!` block at the end of this
/// file; all the legacy (trusted) methods are in the plain `impl` below.
impl PageTable {
    fn root(&self) -> &PTPage {
        // SAFETY: `root` is the access handle for the root page owned by
        // `perms`; it remains valid until `Drop`.
        unsafe { &*(self.root.pptr.addr as *const PTPage) }
    }

    fn root_mut(&mut self) -> &mut PTPage {
        // SAFETY: `&mut self` gives exclusive access to the root page.
        unsafe { &mut *(self.root.pptr.addr as *mut PTPage) }
    }

    /// Load the current page table into the CR3 register.
    ///
    /// # Safety
    ///
    /// The caller must ensure to take other actions to make sure a memory safe
    /// execution state is warranted (e.g. changing the stack and register state)
    pub unsafe fn load(&self) {
        // SAFETY: demanded to the caller
        unsafe {
            write_cr3(self.cr3_value());
        }
    }

    /// Get the CR3 register value for the current page table.
    pub fn cr3_value(&self) -> PhysAddr {
        virt_to_phys(VirtAddr::from(self.root.pptr.addr))
    }

    /// Clone the shared part of the page table; excluding the private
    /// parts.
    ///
    /// # Errors
    /// Returns [`SvsmError`] if the page cannot be allocated.
    pub fn clone_shared(&self) -> Result<PageTable, SvsmError> {
        let mut pgtable = Self::allocate_new()?;
        pgtable.root_mut().entries[PGTABLE_LVL3_IDX_SHARED] =
            self.root().entries[PGTABLE_LVL3_IDX_SHARED];
        Ok(pgtable)
    }

    /// Copy an entry `entry` from another [`PageTable`].
    pub fn copy_entry(&mut self, other: &Self, entry: usize) {
        self.root_mut().entries[entry] = other.root().entries[entry];
    }

    /// Computes the index within a page table at the given level for a
    /// virtual address `vaddr`.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address to compute the index for.
    ///
    /// # Returns
    /// The index within the page table.
    pub fn index<const L: usize>(vaddr: VirtAddr) -> usize {
        vaddr.to_pgtbl_idx::<L>()
        //vaddr.bits() >> (12 + L * 9) & 0x1ff
    }

    // The page-table walk (`walk_addr`, `walk_addr_lvl0/1/2/3`) is verified and
    // permission-threaded; see the `verus!` block at the end of this file.

    /// Calculate the virtual address of a PTE in the self-map, which maps a
    /// specified virtual address.
    ///
    /// # Parameters
    /// - `vaddr': The virtual address whose PTE should be located.
    ///
    /// # Returns
    /// The virtual address of the PTE.
    fn get_pte_address(vaddr: VirtAddr) -> VirtAddr {
        SVSM_PTE_BASE + ((usize::from(vaddr) & 0x0000_FFFF_FFFF_F000) >> 9)
    }

    /// Perform a virtual to physical translation using the self-map.
    ///
    /// # Parameters
    /// - `vaddr': The virtual address to translate.
    ///
    /// # Returns
    /// Some(PageFrame) if the virtual address is valid.
    /// None if the virtual address is not valid.
    ///
    /// Under verification this method is replaced by a verified version that
    /// threads the self-map evidence (`SelfMapView`); see the `verus!` block at
    /// the end of this file. The control flow is identical.
    pub fn virt_to_frame(vaddr: VirtAddr) -> Option<PageFrame> {
        // Calculate the virtual addresses of each level of the paging
        // hierarchy in the self-map.
        let pte_addr = Self::get_pte_address(vaddr);
        let pde_addr = Self::get_pte_address(pte_addr);
        let pdpe_addr = Self::get_pte_address(pde_addr);
        let pml4e_addr = Self::get_pte_address(pdpe_addr);

        // SAFETY: Check each entry in the paging hierarchy to determine
        // whether this address is mapped.  Because the hierarchy is read from
        // the top down using self-map addresses that were calculated
        // correctly, the reads are safe to perform.
        let pml4e = unsafe { PTEntry::read_pte(pml4e_addr) };
        if !pml4e.present() {
            return None;
        }

        // There is no need to check for a large page in the PML4E because
        // the architecture does not support the large bit at the top-level
        // entry.  If a large page is detected at a lower level of the
        // hierarchy, the low bits from the virtual address must be combined
        // with the physical address from the PDE/PDPE.

        // SAFETY: The PML4E was checked to be present, so the PDPE exists and
        // can be read safely.
        let pdpe = unsafe { PTEntry::read_pte(pdpe_addr) };
        if !pdpe.present() {
            return None;
        }
        if pdpe.huge() {
            let pa = pdpe.page_frame() + (usize::from(vaddr) & 0x3FFF_FFFF);
            return Some(PageFrame::Size1G(pa));
        }

        // SAFETY: The PDPE was checked to be present and not to be a huge
        // page. So the PDE exists and can be read safely.
        let pde = unsafe { PTEntry::read_pte(pde_addr) };
        if !pde.present() {
            return None;
        }
        if pde.huge() {
            let pa = pde.page_frame() + (usize::from(vaddr) & 0x001F_FFFF);
            return Some(PageFrame::Size2M(pa));
        }

        // SAFETY: The PDE was checked to be present and not to be a huge
        // page. So the PTE exists and can be read safely.
        let pte = unsafe { PTEntry::read_pte(pte_addr) };
        if pte.present() {
            let pa = pte.page_frame() + (usize::from(vaddr) & 0xFFF);
            Some(PageFrame::Size4K(pa))
        } else {
            None
        }
    }

    // The allocate-on-walk helpers (`alloc_pte_4k`, `alloc_pte_2m`,
    // `alloc_pte_lvl1/2/3`) are verified and permission-threaded; see the
    // `verus!` block at the end of this file.

    /// Splits a 2MB page into 4KB pages.
    ///
    /// # Parameters
    /// - `entry`: The 2M page table entry to split.
    ///
    /// # Returns
    /// A result indicating success or an error [`SvsmError`] in failure.
    fn do_split_4k(entry: &mut PTEntry) -> Result<(), SvsmError> {
        let (page, paddr) = PTPage::alloc()?;
        let mut flags = entry.flags();

        assert!(flags.contains(PTEntryFlags::HUGE));

        let addr_2m = PhysAddr::from(entry.address().bits() & 0x000f_ffff_fff0_0000);

        flags.remove(PTEntryFlags::HUGE);

        // Prepare PTE leaf page
        for (i, e) in page.entries.iter_mut().enumerate() {
            let addr_4k = addr_2m + (i * PAGE_SIZE);
            e.clear();
            e.set(make_private_address(addr_4k), flags);
        }

        entry.set(make_private_address(paddr), flags);

        flush_tlb_global_sync();

        Ok(())
    }

    /// Splits a page into 4KB pages if it is part of a larger mapping.
    ///
    /// # Parameters
    /// - `mapping`: The mapping to split.
    ///
    /// # Returns
    /// A result indicating success or an error [`SvsmError`].
    fn split_4k(mapping: Mapping) -> Result<(), SvsmError> {
        match mapping {
            Mapping::Level0(_loc) => Ok(()),
            Mapping::Level1(loc) => {
                // SAFETY: `loc` was produced by the verified walk.
                let entry = unsafe { loc_entry_mut(&loc) };
                Self::do_split_4k(entry)
            }
            Mapping::Level2(_loc) => Err(SvsmError::Mem),
            Mapping::Level3(_loc) => Err(SvsmError::Mem),
        }
    }

    fn make_pte_shared(entry: &mut PTEntry) {
        let flags = entry.flags();
        let addr = entry.address();

        // entry.address() returned with c-bit clear already
        entry.set(make_shared_address(addr), flags);
    }

    fn make_pte_private(entry: &mut PTEntry) {
        let flags = entry.flags();
        let addr = entry.address();

        // entry.address() returned with c-bit clear already
        entry.set(make_private_address(addr), flags);
    }

    /// Sets the shared state for a 4KB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address of the page.
    ///
    /// # Returns
    /// A result indicating success or an error [`SvsmError`] if the
    /// operation fails.
    pub fn set_shared_4k(&mut self, vaddr: VirtAddr) -> Result<(), SvsmError> {
        let mapping = self.walk_addr(vaddr);
        Self::split_4k(mapping)?;

        if let Mapping::Level0(loc) = self.walk_addr(vaddr) {
            // SAFETY: `loc` was produced by the verified walk.
            let entry = unsafe { loc_entry_mut(&loc) };
            Self::make_pte_shared(entry);
            Ok(())
        } else {
            Err(SvsmError::Mem)
        }
    }

    /// Sets the encryption state for a 4KB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address of the page.
    ///
    /// # Returns
    /// A result indicating success or an error [`SvsmError`].
    pub fn set_encrypted_4k(&mut self, vaddr: VirtAddr) -> Result<(), SvsmError> {
        let mapping = self.walk_addr(vaddr);
        Self::split_4k(mapping)?;

        if let Mapping::Level0(loc) = self.walk_addr(vaddr) {
            // SAFETY: `loc` was produced by the verified walk.
            let entry = unsafe { loc_entry_mut(&loc) };
            Self::make_pte_private(entry);
            Ok(())
        } else {
            Err(SvsmError::Mem)
        }
    }

    /// Gets the physical address for a mapped `vaddr` or `None` if
    /// no such mapping exists.
    pub fn check_mapping(&mut self, vaddr: VirtAddr) -> Option<PhysAddr> {
        match self.walk_addr(vaddr) {
            Mapping::Level0(loc) | Mapping::Level1(loc) => {
                // SAFETY: `loc` was produced by the verified walk.
                Some(unsafe { loc_entry_mut(&loc) }.address())
            }
            _ => None,
        }
    }

    /// Maps a 2MB page. Verified; see the `verus!` block at the end of this
    /// file for `map_2m`/`unmap_2m`.
    //
    // moved into the verus! block

    /// Maps a 4KB page. Verified; see the `verus!` block at the end of this
    /// file.

    /// Unmaps a 4KB page. Verified; see the `verus!` block at the end of this
    /// file.

    /// Retrieves the physical address of a mapping.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address to query.
    ///
    /// # Returns
    /// The physical address of the mapping if present; otherwise, an error
    /// ([`SvsmError`]).
    pub fn phys_addr(&mut self, vaddr: VirtAddr) -> Result<PhysAddr, SvsmError> {
        let mapping = self.walk_addr(vaddr);

        match mapping {
            Mapping::Level0(loc) => {
                // SAFETY: `loc` was produced by the verified walk.
                let entry = unsafe { loc_entry_mut(&loc) };
                let offset = vaddr.page_offset();
                if !entry.flags().contains(PTEntryFlags::PRESENT) {
                    return Err(SvsmError::Mem);
                }
                Ok(entry.address() + offset)
            }
            Mapping::Level1(loc) => {
                // SAFETY: `loc` was produced by the verified walk.
                let entry = unsafe { loc_entry_mut(&loc) };
                let offset = vaddr.bits() & (PAGE_SIZE_2M - 1);
                if !entry.flags().contains(PTEntryFlags::PRESENT)
                    || !entry.flags().contains(PTEntryFlags::HUGE)
                {
                    return Err(SvsmError::Mem);
                }

                Ok(entry.address() + offset)
            }
            Mapping::Level2(_loc) => Err(SvsmError::Mem),
            Mapping::Level3(_loc) => Err(SvsmError::Mem),
        }
    }

    /// Maps a region of memory using 4KB pages.
    ///
    /// # Parameters
    /// - `vregion`: The virtual memory region to map.
    /// - `phys`: The starting physical address to map to.
    /// - `flags`: The flags to apply to the mapping.
    /// - `shared`: Indicates whether the mapping is shared.
    ///
    /// # Returns
    /// A result indicating success or failure ([`SvsmError`]).
    pub fn map_region_4k(
        &mut self,
        vregion: MemoryRegion<VirtAddr>,
        phys: PhysAddr,
        flags: PTEntryFlags,
        shared: bool,
    ) -> Result<(), SvsmError> {
        for addr in vregion.iter_pages(PageSize::Regular) {
            let offset = addr - vregion.start();
            self.map_4k(addr, phys + offset, flags, shared)?;
        }
        Ok(())
    }

    /// Unmaps a region of memory using 4KB pages.
    ///
    /// # Parameters
    /// - `vregion`: The virtual memory region to unmap.
    pub fn unmap_region_4k(&mut self, vregion: MemoryRegion<VirtAddr>) {
        for addr in vregion.iter_pages(PageSize::Regular) {
            self.unmap_4k(addr);
        }
    }

    /// Maps a region of memory using 2MB pages.
    ///
    /// # Parameters
    /// - `vregion`: The virtual memory region to map.
    /// - `phys`: The starting physical address to map to.
    /// - `flags`: The flags to apply to the mapping.
    /// - `shared`: Indicates whether the mapping is shared.
    ///
    /// # Returns
    /// A result indicating success or failure ([`SvsmError`]).
    pub fn map_region_2m(
        &mut self,
        vregion: MemoryRegion<VirtAddr>,
        phys: PhysAddr,
        flags: PTEntryFlags,
        shared: bool,
    ) -> Result<(), SvsmError> {
        for addr in vregion.iter_pages(PageSize::Huge) {
            let offset = addr - vregion.start();
            self.map_2m(addr, phys + offset, flags, shared)?;
        }
        Ok(())
    }

    /// Unmaps a region `vregion` of 2MB pages. The region must be
    /// 2MB-aligned and correspond to a set of huge mappings.
    pub fn unmap_region_2m(&mut self, vregion: MemoryRegion<VirtAddr>) {
        for addr in vregion.iter_pages(PageSize::Huge) {
            self.unmap_2m(addr);
        }
    }

    /// Maps a memory region to physical memory with specified flags.
    ///
    /// # Parameters
    /// - `region`: The virtual memory region to map.
    /// - `phys`: The starting physical address to map to.
    /// - `flags`: The flags to apply to the page table entries.
    ///
    /// # Returns
    /// A result indicating success (`Ok`) or failure (`Err`).
    pub fn map_region(
        &mut self,
        region: MemoryRegion<VirtAddr>,
        phys: PhysAddr,
        flags: PTEntryFlags,
    ) -> Result<(), SvsmError> {
        let mut vaddr = region.start();
        let end = region.end();
        let mut paddr = phys;

        while vaddr < end {
            if vaddr.is_aligned(PAGE_SIZE_2M)
                && paddr.is_aligned(PAGE_SIZE_2M)
                && vaddr + PAGE_SIZE_2M <= end
                && self.map_2m(vaddr, paddr, flags, false).is_ok()
            {
                vaddr = vaddr + PAGE_SIZE_2M;
                paddr = paddr + PAGE_SIZE_2M;
                continue;
            }

            self.map_4k(vaddr, paddr, flags, false)?;
            vaddr = vaddr + PAGE_SIZE;
            paddr = paddr + PAGE_SIZE;
        }

        Ok(())
    }

    /// Unmaps the virtual memory region `vregion`.
    pub fn unmap_region(&mut self, vregion: MemoryRegion<VirtAddr>) {
        let mut vaddr = vregion.start();
        let end = vregion.end();

        while vaddr < end {
            let mapping = self.walk_addr(vaddr);

            match mapping {
                Mapping::Level0(loc) => {
                    // SAFETY: `loc` was produced by the verified walk.
                    unsafe { loc_entry_mut(&loc) }.clear();
                    vaddr = vaddr + PAGE_SIZE;
                }
                Mapping::Level1(loc) => {
                    // SAFETY: `loc` was produced by the verified walk.
                    unsafe { loc_entry_mut(&loc) }.clear();
                    vaddr = vaddr + PAGE_SIZE_2M;
                }
                _ => {
                    log::error!("Can't unmap - address not mapped {vaddr:#x}");
                }
            }
        }
    }

    /// Populates this page table with the contents of the given subtree
    /// in `part`.
    ///
    /// Returns `true` if the PTE contents were updated.
    pub fn populate_pgtbl_part(&mut self, part: &PageTablePart) -> bool {
        let Some(paddr) = part.address() else {
            return false;
        };
        let idx = part.index();
        let flags = PTEntryFlags::PRESENT
            | PTEntryFlags::WRITABLE
            | PTEntryFlags::USER
            | PTEntryFlags::ACCESSED;
        let entry = &mut self.root_mut()[idx];
        let prev = entry.raw();
        entry.set(make_private_address(paddr), flags);
        prev != entry.raw()
    }

    /// Makes the memory region pages read-only.
    /// This method is meant for global pages only.
    ///
    /// # Safety
    ///
    /// The caller should verify that `region` can be made read-only, i.e. that
    /// no write can happen or that a #PF raised by any tentative write is
    /// expected.
    /// The caller must also ensure that the region start and size are 4k
    /// aligned.
    pub unsafe fn make_region_ro_4k(
        &mut self,
        region: MemoryRegion<VirtAddr>,
    ) -> Result<(), SvsmError> {
        for page in region.iter_pages(PageSize::Regular) {
            match self.walk_addr(page) {
                Mapping::Level0(loc) => {
                    // SAFETY: `loc` was produced by the verified walk.
                    let entry = unsafe { loc_entry_mut(&loc) };
                    if !entry.present() || !entry.global() {
                        return Err(SvsmError::Mem);
                    }

                    let flags = PTEntryFlags::data_ro();

                    let paddr = if is_shared(entry.0) {
                        make_shared_address(entry.address())
                    } else {
                        make_private_address(entry.address())
                    };

                    entry.set(paddr, flags);
                }
                Mapping::Level1(loc) | Mapping::Level2(loc) => {
                    // Ensure we never fell on a huge page while iterating over the region pages.
                    // SAFETY: `loc` was produced by the verified walk.
                    if unsafe { loc_entry_mut(&loc) }.huge() {
                        return Err(SvsmError::Mem);
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }
}

impl Drop for PageTable {
    fn drop(&mut self) {
        // SAFETY: `root` is the access handle for the root page owned by this
        // `PageTable`; it was allocated by the page allocator in `allocate_new`.
        unsafe {
            let ptr = NonNull::new_unchecked(self.root.pptr.addr as *mut PTPage);
            let _ = PageBox::from_raw(ptr);
        }
    }
}

/// Represents a sub-tree of a page-table which can be mapped at a top-level index
#[derive(Debug, FromZeros)]
struct RawPageTablePart {
    page: PTPage,
}

impl RawPageTablePart {
    /// Frees a level 1 page table.
    fn free_lvl1(page: &PTPage) {
        for entry in page.entries.iter() {
            if let Some(page) = PTPage::from_entry(*entry) {
                // SAFETY: the page comes from an entry in the page table,
                // which we allocated using `PTPage::alloc()`, so this is
                // safe.
                unsafe { PTPage::free(page) };
            }
        }
    }

    /// Frees a level 2 page table, including all level 1 tables beneath it.
    fn free_lvl2(page: &PTPage) {
        for entry in page.entries.iter() {
            if let Some(l1_page) = PTPage::from_entry(*entry) {
                Self::free_lvl1(l1_page);
                // SAFETY: the page comes from an entry in the page table,
                // which we allocated using `PTPage::alloc()`, so this is
                // safe.
                unsafe { PTPage::free(l1_page) };
            }
        }
    }

    /// Frees the resources associated with this page table part.
    fn free(&self) {
        RawPageTablePart::free_lvl2(&self.page);
    }

    /// Returns the physical address of this page table part.
    fn address(&self) -> PhysAddr {
        virt_to_phys(VirtAddr::from(self as *const RawPageTablePart))
    }

    /// Walks the page table at level 3 to find the mapping for a given
    /// virtual address.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address to find the mapping for.
    ///
    /// # Returns
    /// The [`RawMapping`] for the given virtual address.
    fn walk_addr(&mut self, vaddr: VirtAddr) -> RawMapping<'_> {
        Self::walk_addr_lvl2(&mut self.page, vaddr)
    }

    // Raw, borrow-based walk/alloc helpers for the untracked subtree. These are
    // the original `&mut PTPage`/`&mut PTEntry` operations; the [`PageTable`]
    // versions are now verified and permission-threaded, so the subtree keeps
    // its own copies here.

    fn walk_addr_lvl0(page: &mut PTPage, vaddr: VirtAddr) -> RawMapping<'_> {
        let idx = PageTable::index::<0>(vaddr);
        RawMapping::Level0(&mut page[idx])
    }

    fn walk_addr_lvl1(page: &mut PTPage, vaddr: VirtAddr) -> RawMapping<'_> {
        let idx = PageTable::index::<1>(vaddr);
        let entry = page[idx];
        match PTPage::from_entry(entry) {
            Some(page) => Self::walk_addr_lvl0(page, vaddr),
            None => RawMapping::Level1(&mut page[idx]),
        }
    }

    fn walk_addr_lvl2(page: &mut PTPage, vaddr: VirtAddr) -> RawMapping<'_> {
        let idx = PageTable::index::<2>(vaddr);
        let entry = page[idx];
        match PTPage::from_entry(entry) {
            Some(page) => Self::walk_addr_lvl1(page, vaddr),
            None => RawMapping::Level2(&mut page[idx]),
        }
    }

    fn alloc_pte_lvl2(entry: &mut PTEntry, vaddr: VirtAddr, size: PageSize) -> RawMapping<'_> {
        let flags = entry.flags();

        if flags.contains(PTEntryFlags::PRESENT) {
            return RawMapping::Level2(entry);
        }

        let Ok((page, paddr)) = PTPage::alloc() else {
            return RawMapping::Level2(entry);
        };

        let flags = PTEntryFlags::PRESENT
            | PTEntryFlags::WRITABLE
            | PTEntryFlags::USER
            | PTEntryFlags::ACCESSED;
        entry.set(make_private_address(paddr), flags);

        let idx = PageTable::index::<1>(vaddr);
        Self::alloc_pte_lvl1(&mut page[idx], vaddr, size)
    }

    fn alloc_pte_lvl1(entry: &mut PTEntry, vaddr: VirtAddr, size: PageSize) -> RawMapping<'_> {
        let flags = entry.flags();

        if size == PageSize::Huge || flags.contains(PTEntryFlags::PRESENT) {
            return RawMapping::Level1(entry);
        }

        let Ok((page, paddr)) = PTPage::alloc() else {
            return RawMapping::Level1(entry);
        };

        let flags = PTEntryFlags::PRESENT
            | PTEntryFlags::WRITABLE
            | PTEntryFlags::USER
            | PTEntryFlags::ACCESSED;
        entry.set(make_private_address(paddr), flags);

        let idx = PageTable::index::<0>(vaddr);
        RawMapping::Level0(&mut page[idx])
    }

    /// Allocates a 4KB page table entry for a given virtual address.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address for which to allocate the PTE.
    ///
    /// # Returns
    /// The [`RawMapping`] representing the allocated or existing PTE for the address.
    ///
    /// # Panics
    /// Panics if a level 3 mapping is attempted in a [`RawPageTablePart`].
    fn alloc_pte_4k(&mut self, vaddr: VirtAddr) -> RawMapping<'_> {
        let m = self.walk_addr(vaddr);

        match m {
            RawMapping::Level0(entry) => RawMapping::Level0(entry),
            RawMapping::Level1(entry) => Self::alloc_pte_lvl1(entry, vaddr, PageSize::Regular),
            RawMapping::Level2(entry) => Self::alloc_pte_lvl2(entry, vaddr, PageSize::Regular),
            RawMapping::Level3(_) => panic!("PT level 3 not possible in PageTablePart"),
        }
    }

    /// Allocates a 2MB page table entry for a given virtual address.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address for which to allocate the PTE.
    ///
    /// # Returns
    /// The [`RawMapping`] representing the allocated or existing PTE for the
    /// address.
    fn alloc_pte_2m(&mut self, vaddr: VirtAddr) -> RawMapping<'_> {
        let m = self.walk_addr(vaddr);

        match m {
            RawMapping::Level0(entry) => RawMapping::Level0(entry),
            RawMapping::Level1(entry) => RawMapping::Level1(entry),
            RawMapping::Level2(entry) => Self::alloc_pte_lvl2(entry, vaddr, PageSize::Huge),
            RawMapping::Level3(entry) => RawMapping::Level2(entry),
        }
    }

    /// Maps a 4KB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address to map.
    /// - `paddr`: The physical address to map to.
    /// - `flags`: The flags to apply to the mapping.
    /// - `shared`: Indicates whether the mapping is shared.
    ///
    /// # Returns
    /// A result indicating success (`Ok`) or failure (`Err`).
    fn map_4k(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PTEntryFlags,
        shared: bool,
    ) -> Result<(), SvsmError> {
        let mapping = self.alloc_pte_4k(vaddr);

        let addr = if !shared {
            make_private_address(paddr)
        } else {
            make_shared_address(paddr)
        };

        if let RawMapping::Level0(entry) = mapping {
            entry.set(addr, flags);
            Ok(())
        } else {
            Err(SvsmError::Mem)
        }
    }

    /// Unmaps a 4KB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address of the mapping to unmap.
    ///
    /// # Returns
    /// An optional [`PTEntry`] representing the unmapped page table entry.
    fn unmap_4k(&mut self, vaddr: VirtAddr) -> Option<PTEntry> {
        let mapping = self.walk_addr(vaddr);

        match mapping {
            RawMapping::Level0(entry) => {
                let e = *entry;
                entry.clear();
                Some(e)
            }
            RawMapping::Level1(entry) => {
                assert!(!entry.present());
                None
            }
            RawMapping::Level2(entry) => {
                assert!(!entry.present());
                None
            }
            RawMapping::Level3(entry) => {
                assert!(!entry.present());
                None
            }
        }
    }

    /// Maps a 2MB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address to map.
    /// - `paddr`: The physical address to map to.
    /// - `flags`: The flags to apply to the mapping.
    /// - `shared`: Indicates whether the mapping is shared
    ///
    /// # Returns
    /// A result indicating success (`Ok`) or failure (`Err`).
    ///
    /// # Panics
    ///
    /// Panics if `vaddr` or `paddr` are not 2MB-aligned
    fn map_2m(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PTEntryFlags,
        shared: bool,
    ) -> Result<(), SvsmError> {
        assert!(vaddr.is_aligned(PAGE_SIZE_2M));
        assert!(paddr.is_aligned(PAGE_SIZE_2M));

        let mapping = self.alloc_pte_2m(vaddr);
        let addr = if !shared {
            make_private_address(paddr)
        } else {
            make_shared_address(paddr)
        };

        if let RawMapping::Level1(entry) = mapping {
            entry.set(addr, flags | PTEntryFlags::HUGE);
            Ok(())
        } else {
            Err(SvsmError::Mem)
        }
    }

    /// Unmaps a 2MB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address of the mapping to unmap.
    ///
    /// # Returns
    /// An optional [`PTEntry`] representing the unmapped page table entry.
    ///
    /// # Panics
    ///
    /// Panics if `vaddr` is not memory aligned.
    fn unmap_2m(&mut self, vaddr: VirtAddr) -> Option<PTEntry> {
        assert!(vaddr.is_aligned(PAGE_SIZE_2M));

        let mapping = self.walk_addr(vaddr);

        match mapping {
            RawMapping::Level0(_) => None,
            RawMapping::Level1(entry) => {
                entry.clear();
                Some(*entry)
            }
            RawMapping::Level2(entry) => {
                assert!(!entry.present());
                None
            }
            RawMapping::Level3(entry) => {
                assert!(!entry.present());
                None
            }
        }
    }
}

impl Drop for RawPageTablePart {
    fn drop(&mut self) {
        self.free();
    }
}

/// Sub-tree of a page table that can be populated at the top-level
/// used for virtual memory management
#[derive(Debug)]
pub struct PageTablePart {
    /// The root of the page-table sub-tree
    raw: Option<PageBox<RawPageTablePart>>,
    /// The top-level index this PageTablePart is populated at
    idx: usize,
}

impl PageTablePart {
    /// Create a new PageTablePart and allocate a root page for the page-table sub-tree.
    ///
    /// # Arguments
    ///
    /// - `start`: Virtual start address this PageTablePart maps
    ///
    /// # Returns
    ///
    /// A new instance of PageTablePart
    pub fn new(start: VirtAddr) -> Self {
        PageTablePart {
            raw: None,
            idx: PageTable::index::<3>(start),
        }
    }

    pub fn alloc(&mut self) {
        self.get_or_init_mut();
    }

    fn get_or_init_mut(&mut self) -> &mut RawPageTablePart {
        self.raw.get_or_insert_with(|| {
            PageBox::try_new_zeroed().expect("Failed to allocate page table page")
        })
    }

    fn get_mut(&mut self) -> Option<&mut RawPageTablePart> {
        self.raw.as_deref_mut()
    }

    fn get(&self) -> Option<&RawPageTablePart> {
        self.raw.as_deref()
    }

    /// Request PageTable index to populate this instance to
    ///
    /// # Returns
    ///
    /// Index of the top-level PageTable this sub-tree is populated to
    pub fn index(&self) -> usize {
        self.idx
    }

    /// Request physical base address of the page-table sub-tree. This is
    /// needed to populate the PageTablePart.
    ///
    /// # Returns
    ///
    /// Physical base address of the page-table sub-tree
    pub fn address(&self) -> Option<PhysAddr> {
        self.get().map(|p| p.address())
    }

    /// Map a 4KiB page in the page table sub-tree
    ///
    /// # Arguments
    ///
    /// * `vaddr` - Virtual address to create the mapping. Must be aligned to 4KiB.
    /// * `paddr` - Physical address to map. Must be aligned to 4KiB.
    /// * `flags` - PTEntryFlags used for the mapping
    /// * `shared` - Defines whether the page is mapped shared or private
    ///
    /// # Returns
    ///
    /// OK(()) on Success, Err(SvsmError::Mem) on error.
    ///
    /// This function can fail when there not enough memory to allocate pages for the mapping.
    ///
    /// # Panics
    ///
    /// This method panics when either `vaddr` or `paddr` are not aligned to 4KiB.
    pub fn map_4k(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PTEntryFlags,
        shared: bool,
    ) -> Result<(), SvsmError> {
        assert!(PageTable::index::<3>(vaddr) == self.idx);

        self.get_or_init_mut().map_4k(vaddr, paddr, flags, shared)
    }

    /// Unmaps a 4KiB page from the page table sub-tree
    ///
    /// # Arguments
    ///
    /// * `vaddr` - The virtual address to unmap. Must be aligned to 4KiB.
    ///
    /// # Returns
    ///
    /// Returns a copy of the PTEntry that mapped the virtual address, if any.
    ///
    /// # Panics
    ///
    /// This method panics when `vaddr` is not aligned to 4KiB.
    pub fn unmap_4k(&mut self, vaddr: VirtAddr) -> Option<PTEntry> {
        assert!(PageTable::index::<3>(vaddr) == self.idx);

        self.get_mut().and_then(|r| r.unmap_4k(vaddr))
    }

    /// Map a 2MiB page in the page table sub-tree
    ///
    /// # Arguments
    ///
    /// * `vaddr` - Virtual address to create the mapping. Must be aligned to 2MiB.
    /// * `paddr` - Physical address to map. Must be aligned to 2MiB.
    /// * `flags` - PTEntryFlags used for the mapping
    /// * `shared` - Defines whether the page is mapped shared or private
    ///
    /// # Returns
    ///
    /// OK(()) on Success, Err(SvsmError::Mem) on error.
    ///
    /// This function can fail when there not enough memory to allocate pages for the mapping.
    ///
    /// # Panics
    ///
    /// This method panics when either `vaddr` or `paddr` are not aligned to 2MiB.
    pub fn map_2m(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PTEntryFlags,
        shared: bool,
    ) -> Result<(), SvsmError> {
        assert!(PageTable::index::<3>(vaddr) == self.idx);

        self.get_or_init_mut().map_2m(vaddr, paddr, flags, shared)
    }

    /// Unmaps a 2MiB page from the page table sub-tree
    ///
    /// # Arguments
    ///
    /// * `vaddr` - The virtual address to unmap. Must be aligned to 2MiB.
    ///
    /// # Returns
    ///
    /// Returns a copy of the PTEntry that mapped the virtual address, if any.
    ///
    /// # Panics
    ///
    /// This method panics when `vaddr` is not aligned to 2MiB.
    pub fn unmap_2m(&mut self, vaddr: VirtAddr) -> Option<PTEntry> {
        assert!(PageTable::index::<3>(vaddr) == self.idx);

        self.get_mut().and_then(|r| r.unmap_2m(vaddr))
    }
}

// =====================================================================
// Verified page-table root: storage, allocation, and 4K map/unmap.
//
// The struct stores only the access handle `root` (a direct-map pointer); the
// real authority over every page-table page lives in the tracked `perms`. The
// invariant `inv()` anchors `root` to the permission map and asserts the map is
// well-formed. `map_4k`/`unmap_4k` thread `perms` through the trusted memory API
// in `specs.rs`, so no page-table `unsafe` appears here.
// =====================================================================
#[cfg(verus_only)]
verus! {

#[allow(missing_debug_implementations)]
pub struct PageTable {
    pub root: PTPagePtr,
    pub perms: Tracked<PageTablePerms>,
}

/// A location-based page-table entry slot: the access handle and (ghost) PFN of
/// the node together with the entry index. This replaces the original
/// borrow-based `&mut PTEntry` mapping for the verified `PageTable`, so that a
/// slot can be tied back to the root permission map (`perms.pages()[node@]`) and
/// written through the trusted memory API.
#[allow(missing_debug_implementations)]
pub struct PTLoc {
    pub ptr: PTPagePtr,
    pub node: Ghost<PFN>,
    pub idx: usize,
}

/// Location-based mapping levels, tagged by the level of the node holding the
/// entry. The verified `walk_addr`/`alloc_pte_*` helpers return these.
#[allow(missing_debug_implementations)]
pub enum Mapping {
    Level3(PTLoc),
    Level2(PTLoc),
    Level1(PTLoc),
    Level0(PTLoc),
}

/// A slot `loc` denotes a live entry at paging `lvl` in the permission map.
pub open spec fn loc_at(loc: PTLoc, perms: PageTablePerms, lvl: nat) -> bool {
    &&& perms.pages().dom().contains(loc.node@)
    &&& loc.ptr.addr() == perms.pages()[loc.node@].pptr().addr()
    &&& perms.pages()[loc.node@].level() == lvl
    &&& loc.idx < 512
}

/// A mapping's slot is live at the level indicated by its tag.
pub open spec fn mapping_ok(m: Mapping, perms: PageTablePerms) -> bool {
    match m {
        Mapping::Level3(loc) => loc_at(loc, perms, 3),
        Mapping::Level2(loc) => loc_at(loc, perms, 2),
        Mapping::Level1(loc) => loc_at(loc, perms, 1),
        Mapping::Level0(loc) => loc_at(loc, perms, 0),
    }
}

impl PageTable {
    /// Root-owned well-formedness: the permission map is consistent and the
    /// stored access handle points at the root node it tracks.
    pub open spec fn inv(self) -> bool {
        &&& self.perms@.wf()
        &&& self.root.addr() == self.perms@.root_pptr().addr()
    }

    /// Allocate a new page-table root.
    pub fn allocate_new() -> (r: Result<PageTable, SvsmError>)
        ensures
            r matches Ok(pt) ==> pt.inv(),
    {
        let (root, _pfn, perms) = match pt_root_alloc() {
            Ok(t) => t,
            Err(e) => return Err(e),
        };
        let pt = PageTable { root, perms };
        Ok(pt)
    }

    // =================================================================
    // Verified walk: locate the slot for `vaddr`, descending through
    // existing interior tables. Mirrors the original recursive
    // `walk_addr_lvl3 -> lvl2 -> lvl1 -> lvl0`, but threads the root
    // permission map and returns a location-based `Mapping`.
    // =================================================================

    /// Level-0 node: the slot is always the final 4K leaf slot.
    fn walk_addr_lvl0(&self, node_ptr: PTPagePtr, Ghost(node_pfn): Ghost<PFN>, vaddr: VirtAddr)
        -> (r: Mapping)
        requires
            self.perms@.wf(),
            self.perms@.pages().dom().contains(node_pfn),
            node_ptr.addr() == self.perms@.pages()[node_pfn].pptr().addr(),
            self.perms@.pages()[node_pfn].level() == 0,
        ensures
            mapping_ok(r, self.perms@),
    {
        let idx = pt_index_exec(vaddr, 0);
        Mapping::Level0(PTLoc { ptr: node_ptr, node: Ghost(node_pfn), idx })
    }

    /// Level-1 node: descend into the level-0 child if present, else stop here.
    fn walk_addr_lvl1(&self, node_ptr: PTPagePtr, Ghost(node_pfn): Ghost<PFN>, vaddr: VirtAddr)
        -> (r: Mapping)
        requires
            self.perms@.wf(),
            self.perms@.pages().dom().contains(node_pfn),
            node_ptr.addr() == self.perms@.pages()[node_pfn].pptr().addr(),
            self.perms@.pages()[node_pfn].level() == 1,
        ensures
            mapping_ok(r, self.perms@),
    {
        let idx = pt_index_exec(vaddr, 1);
        let e = pt_read_entry(&node_ptr, Ghost(node_pfn), idx, Tracked(self.perms.borrow()));
        if entry_present(e) && !entry_huge(e) {
            assert(node_pfn != self.perms@.root());
            proof {
                lemma_interior_child_level(self.perms@, node_pfn, idx as nat, pte_decode(e));
            }
            let cptr = entry_child(e, Tracked(self.perms.borrow()));
            let cpfn = Ghost(pte_decode(e).target);
            self.walk_addr_lvl0(cptr, cpfn, vaddr)
        } else {
            Mapping::Level1(PTLoc { ptr: node_ptr, node: Ghost(node_pfn), idx })
        }
    }

    /// Level-2 node: descend into the level-1 child if present, else stop here.
    fn walk_addr_lvl2(&self, node_ptr: PTPagePtr, Ghost(node_pfn): Ghost<PFN>, vaddr: VirtAddr)
        -> (r: Mapping)
        requires
            self.perms@.wf(),
            self.perms@.pages().dom().contains(node_pfn),
            node_ptr.addr() == self.perms@.pages()[node_pfn].pptr().addr(),
            self.perms@.pages()[node_pfn].level() == 2,
        ensures
            mapping_ok(r, self.perms@),
    {
        let idx = pt_index_exec(vaddr, 2);
        let e = pt_read_entry(&node_ptr, Ghost(node_pfn), idx, Tracked(self.perms.borrow()));
        if entry_present(e) && !entry_huge(e) {
            assert(node_pfn != self.perms@.root());
            proof {
                lemma_interior_child_level(self.perms@, node_pfn, idx as nat, pte_decode(e));
            }
            let cptr = entry_child(e, Tracked(self.perms.borrow()));
            let cpfn = Ghost(pte_decode(e).target);
            self.walk_addr_lvl1(cptr, cpfn, vaddr)
        } else {
            Mapping::Level2(PTLoc { ptr: node_ptr, node: Ghost(node_pfn), idx })
        }
    }

    /// Level-3 (root) node: descend into the level-2 child if present, except for
    /// the self-map slot, which is never followed.
    fn walk_addr_lvl3(&self, node_ptr: PTPagePtr, Ghost(node_pfn): Ghost<PFN>, vaddr: VirtAddr)
        -> (r: Mapping)
        requires
            self.perms@.wf(),
            self.perms@.pages().dom().contains(node_pfn),
            node_ptr.addr() == self.perms@.pages()[node_pfn].pptr().addr(),
            self.perms@.pages()[node_pfn].level() == 3,
        ensures
            mapping_ok(r, self.perms@),
    {
        let idx = pt_index_exec(vaddr, 3);
        let sm = idx_selfmap();
        let e = pt_read_entry(&node_ptr, Ghost(node_pfn), idx, Tracked(self.perms.borrow()));
        if entry_present(e) && !entry_huge(e) && idx != sm {
            assert(idx as nat != IDX_SELFMAP);
            proof {
                lemma_interior_child_level(self.perms@, node_pfn, idx as nat, pte_decode(e));
            }
            let cptr = entry_child(e, Tracked(self.perms.borrow()));
            let cpfn = Ghost(pte_decode(e).target);
            self.walk_addr_lvl2(cptr, cpfn, vaddr)
        } else {
            Mapping::Level3(PTLoc { ptr: node_ptr, node: Ghost(node_pfn), idx })
        }
    }

    /// Walk from the root and return the slot for `vaddr`.
    fn walk_addr(&self, vaddr: VirtAddr) -> (r: Mapping)
        requires
            self.inv(),
        ensures
            mapping_ok(r, self.perms@),
    {
        let ghost root_pfn = self.perms@.root();
        self.walk_addr_lvl3(self.root, Ghost(root_pfn), vaddr)
    }

    // =================================================================
    // Verified allocate-on-walk: fill an absent slot by allocating and
    // publishing a fresh interior page, descending to the next level.
    // Mirrors the original `alloc_pte_lvl3 -> lvl2 -> lvl1`.
    // `huge` selects the 2M path: at level 1 a huge mapping stops at the
    // level-1 slot instead of allocating a level-0 leaf table.
    // =================================================================

    /// Fill an absent level-1 slot. For a 4K mapping, allocate a level-0 leaf
    /// table and return its slot; for a huge (2M) mapping, return the level-1
    /// slot directly.
    fn alloc_pte_lvl1(&mut self, loc: PTLoc, vaddr: VirtAddr, huge: bool) -> (r: Mapping)
        requires
            old(self).inv(),
            loc_at(loc, old(self).perms@, 1),
        ensures
            final(self).inv(),
            mapping_ok(r, final(self).perms@),
    {
        let e = pt_read_entry(&loc.ptr, loc.node, loc.idx, Tracked(self.perms.borrow()));
        if huge || entry_present(e) {
            return Mapping::Level1(loc);
        }
        let (cptr, cpfn, cperm) = match pt_page_alloc_fresh(0, Tracked(self.perms.borrow())) {
            Ok(t) => t,
            Err(_e) => return Mapping::Level1(loc),
        };
        let pte = make_interior_pte(cpfn);
        pt_publish_child(
            &loc.ptr,
            loc.node,
            loc.idx,
            pte,
            Ghost(cpfn as nat),
            cperm,
            Tracked(self.perms.borrow_mut()),
        );
        let i0 = pt_index_exec(vaddr, 0);
        Mapping::Level0(PTLoc { ptr: cptr, node: Ghost(cpfn as nat), idx: i0 })
    }

    /// Fill an absent level-2 slot by allocating a level-1 table, then continue.
    fn alloc_pte_lvl2(&mut self, loc: PTLoc, vaddr: VirtAddr, huge: bool) -> (r: Mapping)
        requires
            old(self).inv(),
            loc_at(loc, old(self).perms@, 2),
        ensures
            final(self).inv(),
            mapping_ok(r, final(self).perms@),
    {
        let e = pt_read_entry(&loc.ptr, loc.node, loc.idx, Tracked(self.perms.borrow()));
        if entry_present(e) {
            return Mapping::Level2(loc);
        }
        let (cptr, cpfn, cperm) = match pt_page_alloc_fresh(1, Tracked(self.perms.borrow())) {
            Ok(t) => t,
            Err(_e) => return Mapping::Level2(loc),
        };
        let pte = make_interior_pte(cpfn);
        pt_publish_child(
            &loc.ptr,
            loc.node,
            loc.idx,
            pte,
            Ghost(cpfn as nat),
            cperm,
            Tracked(self.perms.borrow_mut()),
        );
        let i1 = pt_index_exec(vaddr, 1);
        let child_loc = PTLoc { ptr: cptr, node: Ghost(cpfn as nat), idx: i1 };
        self.alloc_pte_lvl1(child_loc, vaddr, huge)
    }

    /// Fill an absent level-3 (root) slot by allocating a level-2 table, then
    /// continue. The self-map slot is excluded by the caller.
    fn alloc_pte_lvl3(&mut self, loc: PTLoc, vaddr: VirtAddr, huge: bool) -> (r: Mapping)
        requires
            old(self).inv(),
            loc_at(loc, old(self).perms@, 3),
            loc.idx as nat != IDX_SELFMAP,
        ensures
            final(self).inv(),
            mapping_ok(r, final(self).perms@),
    {
        let e = pt_read_entry(&loc.ptr, loc.node, loc.idx, Tracked(self.perms.borrow()));
        if entry_present(e) {
            return Mapping::Level3(loc);
        }
        let (cptr, cpfn, cperm) = match pt_page_alloc_fresh(2, Tracked(self.perms.borrow())) {
            Ok(t) => t,
            Err(_e) => return Mapping::Level3(loc),
        };
        let pte = make_interior_pte(cpfn);
        pt_publish_child(
            &loc.ptr,
            loc.node,
            loc.idx,
            pte,
            Ghost(cpfn as nat),
            cperm,
            Tracked(self.perms.borrow_mut()),
        );
        let i2 = pt_index_exec(vaddr, 2);
        let child_loc = PTLoc { ptr: cptr, node: Ghost(cpfn as nat), idx: i2 };
        self.alloc_pte_lvl2(child_loc, vaddr, huge)
    }

    /// Allocate (as needed) and return the level-0 slot for a 4K mapping of
    /// `vaddr`. Routes through the verified walk and per-level allocators.
    fn alloc_pte_4k(&mut self, vaddr: VirtAddr) -> (r: Mapping)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            mapping_ok(r, final(self).perms@),
    {
        let m = self.walk_addr(vaddr);
        match m {
            Mapping::Level0(loc) => Mapping::Level0(loc),
            Mapping::Level1(loc) => self.alloc_pte_lvl1(loc, vaddr, false),
            Mapping::Level2(loc) => self.alloc_pte_lvl2(loc, vaddr, false),
            Mapping::Level3(loc) => {
                let sm = idx_selfmap();
                if loc.idx == sm {
                    Mapping::Level3(loc)
                } else {
                    assert(loc.idx as nat != IDX_SELFMAP);
                    self.alloc_pte_lvl3(loc, vaddr, false)
                }
            }
        }
    }

    /// Allocate (as needed) and return the level-1 slot for a 2M mapping of
    /// `vaddr`. Routes through the verified walk and per-level allocators.
    fn alloc_pte_2m(&mut self, vaddr: VirtAddr) -> (r: Mapping)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            mapping_ok(r, final(self).perms@),
    {
        let m = self.walk_addr(vaddr);
        match m {
            Mapping::Level0(loc) => Mapping::Level0(loc),
            Mapping::Level1(loc) => Mapping::Level1(loc),
            Mapping::Level2(loc) => self.alloc_pte_lvl2(loc, vaddr, true),
            Mapping::Level3(loc) => {
                let sm = idx_selfmap();
                if loc.idx == sm {
                    Mapping::Level3(loc)
                } else {
                    assert(loc.idx as nat != IDX_SELFMAP);
                    self.alloc_pte_lvl3(loc, vaddr, true)
                }
            }
        }
    }

    /// Map a 4K page at `vaddr` to `paddr`, allocating interior tables as needed.
    pub fn map_4k(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PTEntryFlags,
        shared: bool,
    ) -> (r: Result<(), SvsmError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        let sm = idx_selfmap();
        let i3 = pt_index_exec(vaddr, 3);
        if i3 == sm {
            return Err(svsm_mem_error());
        }
        let m = self.alloc_pte_4k(vaddr);
        match m {
            Mapping::Level0(loc) => {
                let leaf = make_map_4k_leaf(paddr, flags, shared);
                pt_write_entry(&loc.ptr, loc.node, loc.idx, leaf, Tracked(self.perms.borrow_mut()));
                Ok(())
            }
            _ => Err(svsm_mem_error()),
        }
    }

    /// Unmap a 4K page at `vaddr`. A no-op when the address is not 4K-mapped.
    pub fn unmap_4k(&mut self, vaddr: VirtAddr)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        let sm = idx_selfmap();
        let i3 = pt_index_exec(vaddr, 3);
        if i3 == sm {
            return;
        }
        let m = self.walk_addr(vaddr);
        match m {
            Mapping::Level0(loc) => {
                let e0 = absent_entry();
                pt_write_entry(&loc.ptr, loc.node, loc.idx, e0, Tracked(self.perms.borrow_mut()));
            }
            _ => {}
        }
    }

    /// Map a 2M huge page at `vaddr` to `paddr`, allocating interior tables as
    /// needed. Mirrors `map_4k` but stops at the level-1 (2M) leaf slot.
    pub fn map_2m(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PTEntryFlags,
        shared: bool,
    ) -> (r: Result<(), SvsmError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        let sm = idx_selfmap();
        let i3 = pt_index_exec(vaddr, 3);
        if i3 == sm {
            return Err(svsm_mem_error());
        }
        let m = self.alloc_pte_2m(vaddr);
        match m {
            Mapping::Level1(loc) => {
                let leaf = make_map_2m_leaf(paddr, flags, shared);
                pt_write_entry(&loc.ptr, loc.node, loc.idx, leaf, Tracked(self.perms.borrow_mut()));
                Ok(())
            }
            _ => Err(svsm_mem_error()),
        }
    }

    /// Unmap a 2M huge page at `vaddr`. A no-op when the address is not 2M-mapped.
    pub fn unmap_2m(&mut self, vaddr: VirtAddr)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        let sm = idx_selfmap();
        let i3 = pt_index_exec(vaddr, 3);
        if i3 == sm {
            return;
        }
        let m = self.walk_addr(vaddr);
        match m {
            Mapping::Level1(loc) => {
                let e1 = absent_entry();
                pt_write_entry(&loc.ptr, loc.node, loc.idx, e1, Tracked(self.perms.borrow_mut()));
            }
            _ => {}
        }
    }
}

} // verus!
