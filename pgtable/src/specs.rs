// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Verus specifications for the SVSM address space.
//
// This module is only compiled under verification (`verus_only`).
//
// It contains a *spec-level* (mathematical) model of the SVSM virtual address
// space, deliberately abstracting away the concrete page-table tree. The model
// is the semantic target that `crate::pagetable` will later be proven to refine.
//
// Design decisions (agreed up front):
//   * leaves are **size-tagged** (4K / 2M / 1G), not normalized to 4K pages;
//   * the **TLB / multi-CPU** layer is modeled from the start;
//   * the model lives in the standalone `pgtable/` crate.
//
// The model is organized in four layers (see the module-level comment blocks):
//   L0  address / frame primitives
//   L1  RegionMap     - the pure translation content of one PageTablePart subtree
//   L2  region typing - the PerCpu / Shared / PerTask / User / SelfMap distinction
//   L3  System + TLB  - the CPU fleet, per-CPU TLBs, flush modes, and the
//                       top-level confidentiality property.
//
// NOTE: this file states the model and the invariants/goals. The refinement of
// `pagetable.rs` onto L1 and the proofs of invariant preservation across the L3
// transitions are the next phases; they are intentionally not attempted here.

use vstd::prelude::*;

verus! {

// =====================================================================
// L0 - Address and frame primitives
// =====================================================================

/// Virtual page number (`vaddr >> 12`).
pub type VPage = nat;

/// Physical frame number (`paddr >> 12`).
pub type PFN = nat;

/// Logical CPU identifier.
pub type CpuId = nat;

/// Task identifier (selects the PerTask/User subtree mounted under a CR3).
pub type TaskId = nat;

/// Entries per page-table page on x86-64 4-level paging.
pub spec const ENTRIES_PER_TABLE: nat = 512;

/// Pages spanned by one top-level (PML4 / level-3) slot = 512^3 4K pages.
pub spec const PML4_SLOT_PAGES: nat = 512 * 512 * 512;

/// Leaf page sizes supported by the hardware.
#[derive(PartialEq, Eq, Structural, Debug)]
pub enum PageSz {
    Size4K,
    Size2M,
    Size1G,
}

impl PageSz {
    /// Number of 4K pages covered by a leaf of this size.
    pub open spec fn pages(self) -> nat {
        match self {
            PageSz::Size4K => 1,
            PageSz::Size2M => 512,
            PageSz::Size1G => 512 * 512,
        }
    }
}

// =====================================================================
// L1 - RegionMap: the pure translation content of one subtree
// =====================================================================

/// The semantically-meaningful attributes of one leaf mapping.
///
/// `present`/`accessed`/`dirty`/`huge` from the concrete PTE are *not* carried:
/// presence is encoded by membership in the [`RegionMap`], and the huge bit is
/// subsumed by [`MapEntry::size`]. What remains are the access-control and
/// confidentiality attributes that the security argument depends on.
#[allow(missing_debug_implementations)]
pub struct MapEntry {
    /// Starting physical frame number backing the leaf.
    pub frame: PFN,
    /// Leaf size (determines how many pages the entry covers).
    pub size: PageSz,
    /// Writable (PTE `WRITABLE`).
    pub w: bool,
    /// Executable (PTE `NX` cleared).
    pub x: bool,
    /// User-accessible (PTE `USER`).
    pub user: bool,
    /// Survives a CR3 reload (PTE `GLOBAL`).
    pub global: bool,
    /// Confidentiality state: `true` = private (C-bit set, guest-confidential),
    /// `false` = shared (host/hypervisor-visible).
    pub encrypted: bool,
}

/// The translation content of one `PageTablePart` subtree, abstracted away from
/// the page-table tree: a partial map from a leaf's *start* page to its entry.
/// A leaf keyed at `k` covers `[k, k + e.size.pages())`.
#[allow(missing_debug_implementations)]
pub struct RegionMap {
    pub leaves: Map<VPage, MapEntry>,
}

/// Does the leaf keyed at `start` cover virtual page `vp`?
pub open spec fn covers(start: VPage, e: MapEntry, vp: VPage) -> bool {
    start <= vp < start + e.size.pages()
}

/// Do two leaves overlap in the virtual page space?
pub open spec fn leaves_overlap(k1: VPage, e1: MapEntry, k2: VPage, e2: MapEntry) -> bool {
    k1 < k2 + e2.size.pages() && k2 < k1 + e1.size.pages()
}

/// A single leaf is well-formed when its start and backing frame are aligned to
/// the leaf size (so the page offset is preserved by the linear translation).
pub open spec fn entry_wf(start: VPage, e: MapEntry) -> bool {
    &&& start % e.size.pages() == 0
    &&& e.frame % e.size.pages() == 0
}

/// A region map is well-formed when every leaf is well-formed and no two
/// distinct leaves overlap.
pub open spec fn region_wf(rm: RegionMap) -> bool {
    &&& forall|k: VPage| #[trigger]
        rm.leaves.dom().contains(k) ==> entry_wf(k, rm.leaves[k])
    &&& forall|k1: VPage, k2: VPage|
        (#[trigger] rm.leaves.dom().contains(k1) && #[trigger] rm.leaves.dom().contains(k2) && k1
            != k2) ==> !leaves_overlap(k1, rm.leaves[k1], k2, rm.leaves[k2])
}

/// Translate a virtual page through a region map: find the covering leaf (if
/// any) and apply the linear offset to its base frame.
pub open spec fn region_translate(rm: RegionMap, vp: VPage) -> Option<(PFN, MapEntry)> {
    if exists|k: VPage| #[trigger] rm.leaves.dom().contains(k) && covers(k, rm.leaves[k], vp) {
        let k = choose|k: VPage|
            #[trigger] rm.leaves.dom().contains(k) && covers(k, rm.leaves[k], vp);
        let e = rm.leaves[k];
        Some(((e.frame + (vp - k)) as nat, e))
    } else {
        None
    }
}

// --- L1 pure updates (the abstract effect of pagetable.rs operations) -------

/// Abstract `map_*`: install a leaf. (Refinement target for `map_4k`/`map_2m`.)
pub open spec fn region_map_leaf(rm: RegionMap, start: VPage, e: MapEntry) -> RegionMap {
    RegionMap { leaves: rm.leaves.insert(start, e) }
}

/// Abstract `unmap_*`: remove a leaf.
pub open spec fn region_unmap_leaf(rm: RegionMap, start: VPage) -> RegionMap {
    RegionMap { leaves: rm.leaves.remove(start) }
}

/// Abstract `set_shared_4k` / `set_encrypted_4k`: flip a leaf's C-bit.
/// (`do_split_4k` is invisible here: splitting a 2M leaf into 512 identical 4K
/// leaves does not change `region_translate`, which is exactly why it is sound.)
pub open spec fn region_set_encrypted(rm: RegionMap, start: VPage, enc: bool) -> RegionMap {
    if rm.leaves.dom().contains(start) {
        let e = rm.leaves[start];
        RegionMap {
            leaves: rm.leaves.insert(
                start,
                MapEntry { encrypted: enc, ..e },
            ),
        }
    } else {
        rm
    }
}

// =====================================================================
// L2 - Region typing: PerCpu / Shared / PerTask / User / SelfMap
// =====================================================================

// Top-level (PML4 / level-3) indices, from `crate::address_space`.
pub spec const PML4_PERTASK: nat = 508;
pub spec const PML4_SELFMAP: nat = 493;
pub spec const PML4_PERCPU: nat = 510;
pub spec const PML4_SHARED: nat = 511;

/// The PML4 index that owns a virtual page.
pub open spec fn pml4_index(vp: VPage) -> nat {
    (vp / PML4_SLOT_PAGES) % ENTRIES_PER_TABLE
}

/// Which kind of address-space region a virtual page falls in. This is the
/// distinction that makes the three categories behave differently:
///   * `Shared`   - one subtree shared by reference across every CR3;
///   * `PerCpu`   - a distinct subtree per CPU;
///   * `PerTask`  - kernel-side per-task subtree (idx 508);
///   * `User`     - user-side per-task subtree (idx 0..=255);
///   * `SelfMap`  - the recursive page-table self-map (idx 493);
///   * `Unused`   - nothing should be mapped here.
#[derive(PartialEq, Eq, Structural, Debug)]
pub enum RegionKind {
    User,
    PerTask,
    PerCpu,
    Shared,
    SelfMap,
    Unused,
}

pub open spec fn region_of(vp: VPage) -> RegionKind {
    let idx = pml4_index(vp);
    if idx <= 255 {
        RegionKind::User
    } else if idx == PML4_PERTASK {
        RegionKind::PerTask
    } else if idx == PML4_SELFMAP {
        RegionKind::SelfMap
    } else if idx == PML4_PERCPU {
        RegionKind::PerCpu
    } else if idx == PML4_SHARED {
        RegionKind::Shared
    } else {
        RegionKind::Unused
    }
}

/// The attribute profile each region is allowed to expose. This is where the
/// per-region policy differences live.
pub open spec fn region_attr_wf(kind: RegionKind, e: MapEntry) -> bool {
    match kind {
        // User mappings are user-accessible and never global (flushed on CR3
        // switch) and back private task memory.
        RegionKind::User => e.user && !e.global && e.encrypted,
        // Per-task kernel mappings: supervisor, global, private.
        RegionKind::PerTask => !e.user && e.global && e.encrypted,
        // Per-CPU mappings: supervisor, global. (encryption varies: e.g. guest
        // VMSA/CAA windows may be shared, so it is not constrained here.)
        RegionKind::PerCpu => !e.user && e.global,
        // Shared kernel image / heap / global maps: supervisor, global.
        RegionKind::Shared => !e.user && e.global,
        // Self-map points at page-table pages: never executable, private.
        RegionKind::SelfMap => !e.x && e.encrypted,
        // Nothing may be mapped in unused regions.
        RegionKind::Unused => false,
    }
}

// =====================================================================
// L3 - System: CPU fleet, per-CPU TLBs, flush modes, confidentiality
// =====================================================================

/// A per-CPU TLB: a cache of translations the CPU may still use even after the
/// backing page table has changed. Modeled as the set of cached leaves keyed by
/// the accessed virtual page.
#[allow(missing_debug_implementations)]
pub struct Tlb {
    pub cached: Map<VPage, MapEntry>,
}

/// The whole-system address-space state.
///
/// The shared subtree is a *single* object (idx 511, shared by reference); the
/// per-CPU and per-task subtrees are indexed families. `running[cpu]` records
/// which task's subtree is mounted under that CPU's CR3.
#[allow(missing_debug_implementations)]
pub struct System {
    pub shared: RegionMap,
    pub percpu: Map<CpuId, RegionMap>,
    pub pertask: Map<TaskId, RegionMap>,
    pub running: Map<CpuId, TaskId>,
    pub tlb: Map<CpuId, Tlb>,
}

/// The translation a CPU's *page table* currently encodes for `vp`: pick the
/// subtree by region, composing shared (by reference) + this CPU's per-CPU
/// subtree + the running task's per-task/user subtree.
pub open spec fn pagetable_view(sys: System, cpu: CpuId, vp: VPage) -> Option<(PFN, MapEntry)> {
    match region_of(vp) {
        RegionKind::Shared => region_translate(sys.shared, vp),
        RegionKind::PerCpu => region_translate(sys.percpu[cpu], vp),
        RegionKind::PerTask => region_translate(sys.pertask[sys.running[cpu]], vp),
        RegionKind::User => region_translate(sys.pertask[sys.running[cpu]], vp),
        // The self-map is the page table observing itself; left opaque here.
        RegionKind::SelfMap => None,
        RegionKind::Unused => None,
    }
}

/// The translation a CPU *actually* uses: a stale TLB entry takes priority over
/// the page table (the architectural reality that motivates flushing).
pub open spec fn effective(sys: System, cpu: CpuId, vp: VPage) -> Option<MapEntry> {
    if sys.tlb[cpu].cached.dom().contains(vp) {
        Some(sys.tlb[cpu].cached[vp])
    } else {
        match pagetable_view(sys, cpu, vp) {
            Some((_f, e)) => Some(e),
            None => None,
        }
    }
}

// --- The four TLB flush modes (cpu/tlb.rs) ----------------------------------

/// `INVLPG`: drop a single virtual page from one CPU's TLB.
pub open spec fn tlb_flush_addr(t: Tlb, vp: VPage) -> Tlb {
    Tlb { cached: t.cached.remove(vp) }
}

/// CR3 reload (non-global flush): drop all *non-global* entries; globals stay.
pub open spec fn tlb_flush_nonglobal(t: Tlb) -> Tlb {
    Tlb { cached: t.cached.restrict(Set::new(|vp: VPage| t.cached[vp].global)) }
}

/// PGE toggle (local global flush): drop *all* entries, including globals.
pub open spec fn tlb_flush_all(t: Tlb) -> Tlb {
    Tlb { cached: Map::empty() }
}

/// Global-sync broadcast: a full flush applied to *every* CPU's TLB. Models the
/// IPI broadcast that blocks until all CPUs have acknowledged.
pub open spec fn sys_flush_global_sync(sys: System) -> System {
    System {
        tlb: Map::new(|c: CpuId| sys.tlb.dom().contains(c), |c: CpuId| tlb_flush_all(sys.tlb[c])),
        ..sys
    }
}

/// Context switch: mount a different task under `cpu`'s CR3. The CR3 reload
/// flushes that CPU's non-global TLB entries (user/task mappings).
pub open spec fn sys_context_switch(sys: System, cpu: CpuId, task: TaskId) -> System {
    System {
        running: sys.running.insert(cpu, task),
        tlb: sys.tlb.insert(cpu, tlb_flush_nonglobal(sys.tlb[cpu])),
        ..sys
    }
}

// --- System well-formedness + the top-level confidentiality property --------

/// Structural well-formedness: every mounted subtree is well-formed and obeys
/// its region's attribute policy.
pub open spec fn region_map_typed(rm: RegionMap, kind: RegionKind) -> bool {
    forall|k: VPage| #[trigger]
        rm.leaves.dom().contains(k) ==> region_attr_wf(kind, rm.leaves[k])
}

pub open spec fn system_wf(sys: System) -> bool {
    &&& region_wf(sys.shared)
    &&& region_map_typed(sys.shared, RegionKind::Shared)
    &&& forall|c: CpuId| #[trigger]
        sys.percpu.dom().contains(c) ==> region_wf(sys.percpu[c]) && region_map_typed(
            sys.percpu[c],
            RegionKind::PerCpu,
        )
    &&& forall|t: TaskId| #[trigger]
        sys.pertask.dom().contains(t) ==> region_wf(sys.pertask[t])
}

/// Confidentiality goal (the property worth proving about the kernel):
/// no two effective translations anywhere in the fleet disagree about whether a
/// frame is private or shared. In particular a frame revealed to the host as
/// shared can never be simultaneously reachable as private by any CPU - through
/// the page table *or* a stale TLB entry.
pub open spec fn no_conflicting_confidentiality(sys: System) -> bool {
    forall|c1: CpuId, vp1: VPage, c2: CpuId, vp2: VPage|
        #![trigger effective(sys, c1, vp1), effective(sys, c2, vp2)]
        ({
            let e1 = effective(sys, c1, vp1);
            let e2 = effective(sys, c2, vp2);
            &&& e1 is Some
            &&& e2 is Some
            &&& e1->Some_0.frame == e2->Some_0.frame
        }) ==> effective(sys, c1, vp1)->Some_0.encrypted == effective(
            sys,
            c2,
            vp2,
        )->Some_0.encrypted
}

// =====================================================================
// Sanity lemmas (exercise the model; not the real refinement proofs)
// =====================================================================

/// Leaf sizes are positive (needed pervasively by `covers`/`entry_wf`).
pub proof fn lemma_pagesz_pages_pos(s: PageSz)
    ensures
        s.pages() > 0,
{
}

/// After a full local flush, the CPU's effective translation collapses to its
/// page-table view (no entry can be served from the emptied TLB).
pub proof fn lemma_flush_all_collapses_to_pagetable(sys: System, cpu: CpuId, vp: VPage)
    requires
        sys.tlb.dom().contains(cpu),
    ensures
        ({
            let sys2 = System { tlb: sys.tlb.insert(cpu, tlb_flush_all(sys.tlb[cpu])), ..sys };
            effective(sys2, cpu, vp) == match pagetable_view(sys2, cpu, vp) {
                Some((_f, e)) => Some(e),
                None => None::<MapEntry>,
            }
        }),
{
    let sys2 = System { tlb: sys.tlb.insert(cpu, tlb_flush_all(sys.tlb[cpu])), ..sys };
    assert(sys2.tlb[cpu].cached =~= Map::<VPage, MapEntry>::empty());
    assert(!sys2.tlb[cpu].cached.dom().contains(vp));
}

/// A global-sync broadcast empties every CPU's TLB.
pub proof fn lemma_global_sync_empties_all(sys: System, cpu: CpuId)
    requires
        sys.tlb.dom().contains(cpu),
    ensures
        sys_flush_global_sync(sys).tlb[cpu].cached =~= Map::<VPage, MapEntry>::empty(),
{
}

} // verus!
