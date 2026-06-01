// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Standalone copy of the SVSM kernel page table for Verus verification.
//
// Top-level layout:
//   pagetable  - the source under verification, a direct copy of
//                kernel/src/mm/pagetable.rs, built against `stubs`.
//   specs      - the verus specification & permission stack (perm / node / table).
//   stubs      - trusted dependency definitions (address/types/memory_region +
//                hardware/allocator/platform glue); less important, treated as
//                external by Verus.

#![no_std]
#![allow(unused_braces)]
#![allow(unexpected_cfgs)]
#![allow(dead_code)]

extern crate alloc;

// Verus needs `verus_builtin` (pulled in via vstd) imported at the crate root.
#[cfg(feature = "verus")]
#[allow(unused_imports)]
use vstd::prelude::*;

// Trusted dependency stubs (address / types / memory_region + platform glue).
pub mod stubs;

// The source under verification (direct copy of kernel/src/mm/pagetable.rs).
pub mod pagetable;

// The verus specification & permission stack (perm / node / table).
#[cfg(verus_only)]
pub mod specs;
