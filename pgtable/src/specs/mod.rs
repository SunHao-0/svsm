// SPDX-License-Identifier: MIT OR Apache-2.0
//
//! Verus specification & permission stack for the page table.
//!
//! Built bottom-up as linear ghost permissions in the style of vstd's `raw_ptr`
//! / `simple_pptr`, specialized for direct-mapped page-table pages:
//!
//!   [`perm`]  - Layer 0/1: physical-frame regions (`FramePerm`) and the typed,
//!               PFN-tagged page permission (`PagePerm<V>`), over `VA`/`PA`.
//!   [`node`]  - Layer 2: the conceptual model (`Entry`/`PTNode`), the `PtPage`
//!               mapping trait the page-table author implements, and the
//!               page-table-page permission (`PTNodePerm<V>`).
//!   [`table`] - Layer 3: the page table as a collection of `PTNodePerm`s, with
//!               the MMU walk, the tree-shape invariants, region typing, the
//!               A/D-pin discipline, and confidentiality - all stated over the
//!               permission set.
//!
//! Compiled only under verification (`verus_only`).
#![allow(missing_debug_implementations)]

pub mod node;
pub mod perm;
pub mod table;
