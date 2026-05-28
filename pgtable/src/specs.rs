// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Verus specifications and proofs for the page table.
//
// This module is only compiled under verification (`verus_only`). It is the
// home for `verus! { }` specs/proofs that are added incrementally as functions
// in `crate::pagetable` are migrated from "trusted" to "verified".
//
// For now it contains a single smoke proof that confirms the `verus! { }`
// environment is wired up and the verifier runs on this crate. It is NOT a
// page-table correctness spec.

use vstd::prelude::*;

verus! {

/// Smoke proof: a page holds 512 8-byte entries (512 * 8 == 4096).
/// Confirms the verus! environment verifies real content in this crate.
pub proof fn smoke_pagetable_geometry()
    ensures
        512usize * 8 == 4096,
{
}

} // verus!
