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
fn make_shared_address(paddr: PhysAddr) -> PhysAddr {
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

/// Mapping levels of page table entries.
#[derive(Debug)]
pub enum Mapping<'a> {
    Level3(&'a mut PTEntry),
    Level2(&'a mut PTEntry),
    Level1(&'a mut PTEntry),
    Level0(&'a mut PTEntry),
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
#[repr(C)]
#[derive(Debug, FromZeros)]
pub struct PageTable {
    root: PTPage,
}

impl PageTable {
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
        let pgtable = VirtAddr::from(self as *const Self);
        virt_to_phys(pgtable)
    }

    /// Allocate a new page table root.
    ///
    /// # Errors
    /// Returns [`SvsmError`] if the page cannot be allocated.
    pub fn allocate_new() -> Result<PageBox<Self>, SvsmError> {
        let mut pgtable: PageBox<Self> = PageBox::try_new_zeroed()?;
        let paddr = virt_to_phys(pgtable.vaddr());

        // Set the self-map entry.
        let entry = &mut pgtable.root[PGTABLE_LVL3_IDX_PTE_SELFMAP];
        let flags = PTEntryFlags::PRESENT
            | PTEntryFlags::WRITABLE
            | PTEntryFlags::ACCESSED
            | PTEntryFlags::DIRTY
            | PTEntryFlags::NX;
        entry.set(make_private_address(paddr), flags);

        Ok(pgtable)
    }

    /// Clone the shared part of the page table; excluding the private
    /// parts.
    ///
    /// # Errors
    /// Returns [`SvsmError`] if the page cannot be allocated.
    pub fn clone_shared(&self) -> Result<PageBox<PageTable>, SvsmError> {
        let mut pgtable = Self::allocate_new()?;
        pgtable.root.entries[PGTABLE_LVL3_IDX_SHARED] = self.root.entries[PGTABLE_LVL3_IDX_SHARED];
        Ok(pgtable)
    }

    /// Copy an entry `entry` from another [`PageTable`].
    pub fn copy_entry(&mut self, other: &Self, entry: usize) {
        self.root.entries[entry] = other.root.entries[entry];
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

    /// Walks a page table at level 0 to find a mapping.
    ///
    /// # Parameters
    /// - `page`: A mutable reference to the root page table.
    /// - `vaddr`: The virtual address to find a mapping for.
    ///
    /// # Returns
    /// A `Mapping` representing the found mapping.
    fn walk_addr_lvl0(page: &mut PTPage, vaddr: VirtAddr) -> Mapping<'_> {
        let idx = Self::index::<0>(vaddr);
        Mapping::Level0(&mut page[idx])
    }

    /// Walks a page table at level 1 to find a mapping.
    ///
    /// # Parameters
    /// - `page`: A mutable reference to the root page table.
    /// - `vaddr`: The virtual address to find a mapping for.
    ///
    /// # Returns
    /// A `Mapping` representing the found mapping.
    fn walk_addr_lvl1(page: &mut PTPage, vaddr: VirtAddr) -> Mapping<'_> {
        let idx = Self::index::<1>(vaddr);
        let entry = page[idx];
        match PTPage::from_entry(entry) {
            Some(page) => Self::walk_addr_lvl0(page, vaddr),
            None => Mapping::Level1(&mut page[idx]),
        }
    }

    /// Walks a page table at level 2 to find a mapping.
    ///
    /// # Parameters
    /// - `page`: A mutable reference to the root page table.
    /// - `vaddr`: The virtual address to find a mapping for.
    ///
    /// # Returns
    /// A `Mapping` representing the found mapping.
    fn walk_addr_lvl2(page: &mut PTPage, vaddr: VirtAddr) -> Mapping<'_> {
        let idx = Self::index::<2>(vaddr);
        let entry = page[idx];
        match PTPage::from_entry(entry) {
            Some(page) => Self::walk_addr_lvl1(page, vaddr),
            None => Mapping::Level2(&mut page[idx]),
        }
    }

    /// Walks the page table to find a mapping for a given virtual address.
    ///
    /// # Parameters
    /// - `page`: A mutable reference to the root page table.
    /// - `vaddr`: The virtual address to find a mapping for.
    ///
    /// # Returns
    /// A `Mapping` representing the found mapping.
    fn walk_addr_lvl3(page: &mut PTPage, vaddr: VirtAddr) -> Mapping<'_> {
        let idx = Self::index::<3>(vaddr);
        let entry = page[idx];
        match PTPage::from_entry(entry) {
            Some(page) => Self::walk_addr_lvl2(page, vaddr),
            None => Mapping::Level3(&mut page[idx]),
        }
    }

    /// Walk the virtual address and return the corresponding mapping.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address to find a mapping for.
    ///
    /// # Returns
    /// A `Mapping` representing the found mapping.
    fn walk_addr(&mut self, vaddr: VirtAddr) -> Mapping<'_> {
        Self::walk_addr_lvl3(&mut self.root, vaddr)
    }

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

    fn alloc_pte_lvl3(entry: &mut PTEntry, vaddr: VirtAddr, size: PageSize) -> Mapping<'_> {
        let flags = entry.flags();

        if flags.contains(PTEntryFlags::PRESENT) {
            return Mapping::Level3(entry);
        }

        let Ok((page, paddr)) = PTPage::alloc() else {
            return Mapping::Level3(entry);
        };

        let flags = PTEntryFlags::PRESENT
            | PTEntryFlags::WRITABLE
            | PTEntryFlags::USER
            | PTEntryFlags::ACCESSED;
        entry.set(make_private_address(paddr), flags);

        let idx = Self::index::<2>(vaddr);
        Self::alloc_pte_lvl2(&mut page[idx], vaddr, size)
    }

    fn alloc_pte_lvl2(entry: &mut PTEntry, vaddr: VirtAddr, size: PageSize) -> Mapping<'_> {
        let flags = entry.flags();

        if flags.contains(PTEntryFlags::PRESENT) {
            return Mapping::Level2(entry);
        }

        let Ok((page, paddr)) = PTPage::alloc() else {
            return Mapping::Level2(entry);
        };

        let flags = PTEntryFlags::PRESENT
            | PTEntryFlags::WRITABLE
            | PTEntryFlags::USER
            | PTEntryFlags::ACCESSED;
        entry.set(make_private_address(paddr), flags);

        let idx = Self::index::<1>(vaddr);
        Self::alloc_pte_lvl1(&mut page[idx], vaddr, size)
    }

    fn alloc_pte_lvl1(entry: &mut PTEntry, vaddr: VirtAddr, size: PageSize) -> Mapping<'_> {
        let flags = entry.flags();

        if size == PageSize::Huge || flags.contains(PTEntryFlags::PRESENT) {
            return Mapping::Level1(entry);
        }

        let Ok((page, paddr)) = PTPage::alloc() else {
            return Mapping::Level1(entry);
        };

        let flags = PTEntryFlags::PRESENT
            | PTEntryFlags::WRITABLE
            | PTEntryFlags::USER
            | PTEntryFlags::ACCESSED;
        entry.set(make_private_address(paddr), flags);

        let idx = Self::index::<0>(vaddr);
        Mapping::Level0(&mut page[idx])
    }

    /// Allocates a 4KB page table entry for a given virtual address.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address for which to allocate the PTE.
    ///
    /// # Returns
    /// A `Mapping` representing the allocated or existing PTE for the address.
    fn alloc_pte_4k(&mut self, vaddr: VirtAddr) -> Mapping<'_> {
        let m = self.walk_addr(vaddr);

        match m {
            Mapping::Level0(entry) => Mapping::Level0(entry),
            Mapping::Level1(entry) => Self::alloc_pte_lvl1(entry, vaddr, PageSize::Regular),
            Mapping::Level2(entry) => Self::alloc_pte_lvl2(entry, vaddr, PageSize::Regular),
            Mapping::Level3(entry) => Self::alloc_pte_lvl3(entry, vaddr, PageSize::Regular),
        }
    }

    /// Allocates a 2MB page table entry for a given virtual address.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address for which to allocate the PTE.
    ///
    /// # Returns
    /// A `Mapping` representing the allocated or existing PTE for the address.
    fn alloc_pte_2m(&mut self, vaddr: VirtAddr) -> Mapping<'_> {
        let m = self.walk_addr(vaddr);

        match m {
            Mapping::Level0(entry) => Mapping::Level0(entry),
            Mapping::Level1(entry) => Mapping::Level1(entry),
            Mapping::Level2(entry) => Self::alloc_pte_lvl2(entry, vaddr, PageSize::Huge),
            Mapping::Level3(entry) => Self::alloc_pte_lvl3(entry, vaddr, PageSize::Huge),
        }
    }

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
    fn split_4k(mapping: Mapping<'_>) -> Result<(), SvsmError> {
        match mapping {
            Mapping::Level0(_entry) => Ok(()),
            Mapping::Level1(entry) => Self::do_split_4k(entry),
            Mapping::Level2(_entry) => Err(SvsmError::Mem),
            Mapping::Level3(_entry) => Err(SvsmError::Mem),
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

        if let Mapping::Level0(entry) = self.walk_addr(vaddr) {
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

        if let Mapping::Level0(entry) = self.walk_addr(vaddr) {
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
            Mapping::Level0(entry) => Some(entry.address()),
            Mapping::Level1(entry) => Some(entry.address()),
            _ => None,
        }
    }

    /// Maps a 2MB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address to map.
    /// - `paddr`: The physical address to map to.
    /// - `flags`: The flags to apply to the mapping.
    /// - `shared`: Indicates whether the mapping is shared.
    ///
    /// # Returns
    /// A result indicating success or failure ([`SvsmError`]).
    ///
    /// # Panics
    /// Panics if either `vaddr` or `paddr` is not aligned to a 2MB boundary.
    pub fn map_2m(
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

        if let Mapping::Level1(entry) = mapping {
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
    /// # Panics
    /// Panics if `vaddr` is not aligned to a 2MB boundary.
    pub fn unmap_2m(&mut self, vaddr: VirtAddr) {
        assert!(vaddr.is_aligned(PAGE_SIZE_2M));

        let mapping = self.walk_addr(vaddr);

        match mapping {
            Mapping::Level0(_) => unreachable!(),
            Mapping::Level1(entry) => entry.clear(),
            Mapping::Level2(entry) => assert!(!entry.present()),
            Mapping::Level3(entry) => assert!(!entry.present()),
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
    /// A result indicating success or failure ([`SvsmError`]).
    pub fn map_4k(
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

        if let Mapping::Level0(entry) = mapping {
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
    pub fn unmap_4k(&mut self, vaddr: VirtAddr) {
        let mapping = self.walk_addr(vaddr);

        match mapping {
            Mapping::Level0(entry) => entry.clear(),
            Mapping::Level1(entry) => assert!(!entry.present()),
            Mapping::Level2(entry) => assert!(!entry.present()),
            Mapping::Level3(entry) => assert!(!entry.present()),
        }
    }

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
            Mapping::Level0(entry) => {
                let offset = vaddr.page_offset();
                if !entry.flags().contains(PTEntryFlags::PRESENT) {
                    return Err(SvsmError::Mem);
                }
                Ok(entry.address() + offset)
            }
            Mapping::Level1(entry) => {
                let offset = vaddr.bits() & (PAGE_SIZE_2M - 1);
                if !entry.flags().contains(PTEntryFlags::PRESENT)
                    || !entry.flags().contains(PTEntryFlags::HUGE)
                {
                    return Err(SvsmError::Mem);
                }

                Ok(entry.address() + offset)
            }
            Mapping::Level2(_entry) => Err(SvsmError::Mem),
            Mapping::Level3(_entry) => Err(SvsmError::Mem),
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
                Mapping::Level0(entry) => {
                    entry.clear();
                    vaddr = vaddr + PAGE_SIZE;
                }
                Mapping::Level1(entry) => {
                    entry.clear();
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
        let entry = &mut self.root[idx];
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
                Mapping::Level0(entry) => {
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
                Mapping::Level1(entry) | Mapping::Level2(entry) => {
                    // Ensure we never fell on a huge page while iterating over the region pages.
                    if entry.huge() {
                        return Err(SvsmError::Mem);
                    }
                }
                _ => {}
            }
        }

        Ok(())
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
    /// The [`Mapping`] for the given virtual address.
    fn walk_addr(&mut self, vaddr: VirtAddr) -> Mapping<'_> {
        PageTable::walk_addr_lvl2(&mut self.page, vaddr)
    }

    /// Allocates a 4KB page table entry for a given virtual address.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address for which to allocate the PTE.
    ///
    /// # Returns
    /// The [`Mapping`] representing the allocated or existing PTE for the address.
    ///
    /// # Panics
    /// Panics if a level 3 mapping is attempted in a [`RawPageTablePart`].
    fn alloc_pte_4k(&mut self, vaddr: VirtAddr) -> Mapping<'_> {
        let m = self.walk_addr(vaddr);

        match m {
            Mapping::Level0(entry) => Mapping::Level0(entry),
            Mapping::Level1(entry) => PageTable::alloc_pte_lvl1(entry, vaddr, PageSize::Regular),
            Mapping::Level2(entry) => PageTable::alloc_pte_lvl2(entry, vaddr, PageSize::Regular),
            Mapping::Level3(_) => panic!("PT level 3 not possible in PageTablePart"),
        }
    }

    /// Allocates a 2MB page table entry for a given virtual address.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address for which to allocate the PTE.
    ///
    /// # Returns
    /// The [`Mapping`] representing the allocated or existing PTE for the
    /// address.
    fn alloc_pte_2m(&mut self, vaddr: VirtAddr) -> Mapping<'_> {
        let m = self.walk_addr(vaddr);

        match m {
            Mapping::Level0(entry) => Mapping::Level0(entry),
            Mapping::Level1(entry) => Mapping::Level1(entry),
            Mapping::Level2(entry) => PageTable::alloc_pte_lvl2(entry, vaddr, PageSize::Huge),
            Mapping::Level3(entry) => PageTable::alloc_pte_lvl3(entry, vaddr, PageSize::Huge),
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

        if let Mapping::Level0(entry) = mapping {
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
            Mapping::Level0(entry) => {
                let e = *entry;
                entry.clear();
                Some(e)
            }
            Mapping::Level1(entry) => {
                assert!(!entry.present());
                None
            }
            Mapping::Level2(entry) => {
                assert!(!entry.present());
                None
            }
            Mapping::Level3(entry) => {
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

        if let Mapping::Level1(entry) = mapping {
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
            Mapping::Level0(_) => None,
            Mapping::Level1(entry) => {
                entry.clear();
                Some(*entry)
            }
            Mapping::Level2(entry) => {
                assert!(!entry.present());
                None
            }
            Mapping::Level3(entry) => {
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
