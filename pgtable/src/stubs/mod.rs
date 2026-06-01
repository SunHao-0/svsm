// SPDX-License-Identifier: MIT OR Apache-2.0
//
//! Trusted dependency stubs for the page table.
//!
//! Everything `pagetable.rs` relies on outside the verified spec stack lives
//! here: the vendored "core" modules ([`address`], [`types`], [`memory_region`])
//! plus minimal plain-Rust stand-ins for the hardware / allocator / platform glue
//! (page allocator, CR3/TLB, encryption masks, paging-feature config, page-fault
//! types). Verus treats this whole module tree as trusted (external): there are
//! no `verus! { }` blocks or verus attributes here.

pub mod address;
pub mod memory_region;
pub mod types;

pub use address::{Address, PhysAddr, VirtAddr};
pub use memory_region::MemoryRegion;
pub use types::{PAGE_SHIFT, PAGE_SIZE, PAGE_SIZE_1G, PAGE_SIZE_2M, PageSize};

use alloc::boxed::Box;
use bitflags::bitflags;
use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use core::ops::{Add, BitAnd, Deref, DerefMut, Not, Sub};
use core::ptr::NonNull;
use zerocopy::FromZeros;

/// Maximum number of VMPL levels (used by `types.rs`).
pub const VMPL_MAX: usize = 4;

/// Minimal error type standing in for the kernel-wide `SvsmError`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum SvsmError {
    /// Generic memory error (allocation failure, etc.).
    Mem,
    /// Invalid byte count conversion.
    InvalidBytes,
}

// Alignment helpers + bit macros, merged from kernel/src/utils/util.rs.

pub fn align_up<T>(addr: T, align: T) -> T
where
    T: Add<Output = T> + Sub<Output = T> + BitAnd<Output = T> + Not<Output = T> + From<u8> + Copy,
{
    let mask: T = align - T::from(1u8);
    (addr + mask) & !mask
}

pub fn align_down<T>(addr: T, align: T) -> T
where
    T: Sub<Output = T> + Not<Output = T> + BitAnd<Output = T> + From<u8> + Copy,
{
    addr & !(align - T::from(1u8))
}

pub fn is_aligned<T>(addr: T, align: T) -> bool
where
    T: Sub<Output = T> + BitAnd<Output = T> + PartialEq + From<u8>,
{
    (addr & (align - T::from(1u8))) == T::from(0u8)
}

/// Obtain bit for a given position
#[macro_export]
macro_rules! BIT {
    ($x: expr) => {
        (1 << ($x))
    };
}

/// Obtain bit mask for the given positions
#[macro_export]
macro_rules! BIT_MASK {
    ($e: expr, $s: expr) => {{
        assert!(
            $s <= 63 && $e <= 63 && $s <= $e,
            "Start bit position must be less than or equal to end bit position"
        );
        (((1u64 << ($e - $s + 1)) - 1) << $s)
    }};
}

/// Trusted no-op stand-in for writing CR3.
///
/// # Safety
/// Mirrors the kernel signature; the real implementation switches the active
/// page table. The stub does nothing.
pub unsafe fn write_cr3(_cr3: PhysAddr) {}

/// Trusted no-op stand-in for a global, synchronized TLB flush.
pub fn flush_tlb_global_sync() {}

/// Trusted address-translation stand-ins (identity mapping on the raw bits).
pub fn virt_to_phys(vaddr: VirtAddr) -> PhysAddr {
    PhysAddr::from(vaddr.bits())
}

pub fn phys_to_virt(paddr: PhysAddr) -> VirtAddr {
    VirtAddr::from(paddr.bits())
}

/// A trusted stand-in for the kernel's page allocator `PageBox<T>`: an owning,
/// page-aligned-ish heap box. Backed by the global allocator here.
pub struct PageBox<T: ?Sized>(NonNull<T>);

impl<T: ?Sized> core::fmt::Debug for PageBox<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "PageBox({:p})", self.0.as_ptr())
    }
}

impl<T: FromZeros> PageBox<T> {
    /// Allocates a zeroed `T`.
    pub fn try_new_zeroed() -> Result<PageBox<T>, SvsmError> {
        let b: Box<MaybeUninit<T>> = Box::new(MaybeUninit::zeroed());
        let ptr = Box::into_raw(b) as *mut T;
        Ok(PageBox(NonNull::new(ptr).ok_or(SvsmError::Mem)?))
    }

    /// Allocates a `T` initialized with `x`.
    pub fn try_new(x: T) -> Result<Self, SvsmError> {
        let ptr = Box::into_raw(Box::new(x));
        Ok(PageBox(NonNull::new(ptr).ok_or(SvsmError::Mem)?))
    }
}

impl<T: ?Sized> PageBox<T> {
    /// # Safety
    /// `ptr` must have been produced by [`PageBox`] (i.e. via the global
    /// allocator) and not yet freed.
    pub const unsafe fn from_raw(ptr: NonNull<T>) -> Self {
        PageBox(ptr)
    }

    /// Consumes the box and returns a `'static`-ish mutable reference, leaking
    /// the allocation (matching the kernel API).
    pub fn leak<'a>(b: Self) -> &'a mut T {
        let mut ptr = b.0;
        core::mem::forget(b);
        // SAFETY: we own the allocation and have just forgotten the box.
        unsafe { ptr.as_mut() }
    }

    /// Virtual address of the backing allocation.
    pub fn vaddr(&self) -> VirtAddr {
        VirtAddr::new(self.0.as_ptr() as *const u8 as usize)
    }
}

impl<T: ?Sized> Deref for PageBox<T> {
    type Target = T;
    fn deref(&self) -> &T {
        // SAFETY: we own a valid allocation.
        unsafe { self.0.as_ref() }
    }
}

impl<T: ?Sized> DerefMut for PageBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: we own a valid allocation with exclusive access.
        unsafe { self.0.as_mut() }
    }
}

impl<T: ?Sized> Drop for PageBox<T> {
    fn drop(&mut self) {
        // SAFETY: the pointer was produced by Box::into_raw with the global
        // allocator and is freed exactly once here.
        unsafe {
            let _ = Box::from_raw(self.0.as_ptr());
        }
    }
}

// =====================================================================
// The trusted page allocator (shared by `pagetable.rs` and `specs::perm`)
// =====================================================================

/// 4K page-sized, zeroable backing storage for the trusted page allocator.
#[repr(C)]
#[derive(FromZeros)]
#[allow(missing_debug_implementations)]
pub struct PageStorage([u8; PAGE_SIZE]);

/// Allocate one zeroed 4K page; returns its (direct-map) virtual address, or
/// `None` on failure. This is the single trusted page-allocation primitive: the
/// page-table source allocates `PageBox`es and the permission layer's
/// `page_alloc_zeroed` calls this, so both rest on the same allocator.
pub fn alloc_zeroed_page() -> Option<VirtAddr> {
    let pb: PageBox<PageStorage> = PageBox::try_new_zeroed().ok()?;
    let vaddr = pb.vaddr();
    let _ = PageBox::leak(pb);
    Some(vaddr)
}

/// Free a page previously returned by [`alloc_zeroed_page`].
pub fn free_page(vaddr: VirtAddr) {
    if let Some(ptr) = NonNull::new(vaddr.as_mut_ptr::<PageStorage>()) {
        // SAFETY: trusted stub; `vaddr` came from `alloc_zeroed_page`.
        unsafe {
            let _ = PageBox::from_raw(ptr);
        }
    }
}

// =====================================================================
// Write-once configuration cell (paging feature masks)
// =====================================================================

/// Error type for one-time initialization (trusted stub).
#[derive(Clone, Copy, Debug)]
pub struct ImmutAfterInitError;

pub type ImmutAfterInitResult<T> = Result<T, ImmutAfterInitError>;

/// Trusted stand-in for the kernel's write-once cell. `uninit()` is `const` so it
/// can initialize a `static`; `init` stores the value and `Deref` reads it.
/// Single-threaded init is assumed - this scaffold never runs `paging_init`.
#[allow(missing_debug_implementations)]
pub struct ImmutAfterInitCell<T> {
    value: UnsafeCell<Option<T>>,
}

// SAFETY: trusted stub; treated as external by Verus and never raced here.
unsafe impl<T> Sync for ImmutAfterInitCell<T> {}

impl<T> ImmutAfterInitCell<T> {
    pub const fn uninit() -> Self {
        Self {
            value: UnsafeCell::new(None),
        }
    }

    pub fn init(&self, v: T) -> ImmutAfterInitResult<()> {
        // SAFETY: trusted stub; one-time init during `paging_init`.
        unsafe {
            *self.value.get() = Some(v);
        }
        Ok(())
    }
}

impl<T> Deref for ImmutAfterInitCell<T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: trusted stub; deref follows `init` in `paging_init`.
        unsafe { (*self.value.get()).as_ref().unwrap() }
    }
}

// =====================================================================
// Platform encryption masks
// =====================================================================

/// Encryption-mask parameters the platform reports (trusted stub shape).
#[derive(Debug, Clone, Copy)]
pub struct PageEncryptionMasks {
    pub private_pte_mask: usize,
    pub shared_pte_mask: usize,
    pub addr_mask_width: u32,
    pub phys_addr_sizes: u32,
}

/// Minimal platform trait - only the method `pagetable.rs` uses.
pub trait SvsmPlatform {
    fn get_page_encryption_masks(&self) -> PageEncryptionMasks;
}

// =====================================================================
// CPU page-fault / flags bitflags (used by the access-rights checker)
// =====================================================================

bitflags! {
    /// Page-fault error-code flags (trusted stub).
    #[derive(Clone, Copy, Debug, PartialEq)]
    pub struct PageFaultError: u32 {
        const P = 1 << 0;
        const W = 1 << 1;
        const U = 1 << 2;
        const R = 1 << 3;
        const I = 1 << 4;
    }
}

bitflags! {
    /// CPU flags register (trusted stub; only `AC` is referenced by `pagetable.rs`).
    #[derive(Clone, Copy, Debug)]
    pub struct RFlags: usize {
        const AC = 1 << 18;
    }
}

// =====================================================================
// Address-space layout constants (from kernel `mm::address_space`)
// =====================================================================

/// Level-3 (PML4) index for the shared half of the address space.
pub const PGTABLE_LVL3_IDX_SHARED: usize = 511;

/// Level-3 (PML4) index used for the page-table self-map.
pub const PGTABLE_LVL3_IDX_PTE_SELFMAP: usize = 493;

/// Canonical virtual base address for a top-level (PML4) index.
pub const fn virt_from_idx(idx: usize) -> VirtAddr {
    VirtAddr::new(idx << ((3 * 9) + 12))
}

/// Virtual base address of the page-table self-map.
pub const SVSM_PTE_BASE: VirtAddr = virt_from_idx(PGTABLE_LVL3_IDX_PTE_SELFMAP);
