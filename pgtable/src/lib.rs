// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Standalone copy of the SVSM kernel page table for Verus verification.
//
// The page-table code in `pagetable` is copied from `kernel/src/mm/pagetable.rs`.
// The `*` modules below are the "core" dependencies copied from the kernel; their
// verus annotations are neutralized (treated as trusted plain Rust) so that the
// verification effort can focus on the page-table logic itself.

#![no_std]
#![allow(unused_braces)]
#![allow(unexpected_cfgs)]
#![allow(dead_code)]

extern crate alloc;

// Verus needs `verus_builtin` (pulled in via vstd) imported at the crate root.
#[cfg(feature = "verus")]
#[allow(unused_imports)]
use vstd::prelude::*;

// Vendored "core" dependencies (trusted, plain Rust).
pub mod address;
pub mod memory_region;
pub mod types;

// Trusted glue for hardware / allocator / platform that the page table relies
// on, plus alignment helpers and bit macros.
pub mod stubs;

// The verus specification & permission stack (perm / node / table). The single
// home for `verus! { }` specs/proofs for this crate.
//
// NOTE: `pagetable.rs` (the kernel copy) is intentionally NOT a module right now.
// Its old in-place verification used the previous specs API and has been retired;
// the original code will be re-ported and verified cleanly against this stack.
#[cfg(verus_only)]
pub mod specs;
