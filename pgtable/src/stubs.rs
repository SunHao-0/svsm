// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Trusted glue for the hardware / allocator / platform dependencies that the
// page table relies on. In the kernel these live across many modules that drag
// in the allocator, SMP/IPI and platform code. Here they are replaced with
// minimal, trusted plain-Rust stand-ins so the page-table logic can be verified
// in isolation. Verus treats everything in this module as trusted (external):
// there are no `verus! { }` blocks or verus attributes here.

use crate::address::{Address, PhysAddr, VirtAddr};
use alloc::boxed::Box;
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
