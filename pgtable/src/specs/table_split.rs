// SPDX-License-Identifier: MIT OR Apache-2.0
//
//! Verified proofs for the top-level `split`/`join` operations: carving the subtree
//! under one top-level entry out of a full table into a standalone subtree view (and
//! merging it back). Built on the structural `xlate_base` discipline - every node's
//! translation base pins which top-level bucket it lives in, so the subtree is
//! exactly the live non-root nodes whose base falls in that bucket, and an interior
//! link never leaves its bucket.
#![allow(missing_debug_implementations)]
use crate::specs::node::*;
use crate::specs::table::*;
use crate::specs::table_proof::*;
use vstd::prelude::*;

verus! {

// =====================================================================
// Arithmetic foundation: span factorisation and bucket containment
// =====================================================================

/// `span` is additive in the exponent: `span(a + b) == span(a) * span(b)` (both are
/// powers of 512). Lets a coarse level's stride factor through a finer one's.
pub proof fn lemma_span_add(a: nat, b: nat)
    ensures
        span((a + b) as nat) == span(a) * span(b),
    decreases b,
{
    if b == 0 {
        assert(span(0) == 1);
        assert(span(a) * span(0) == span(a)) by (nonlinear_arith);
    } else {
        lemma_span_add(a, (b - 1) as nat);
        // span(a+b) = 512*span(a+b-1) = 512*span(a)*span(b-1) = span(a)*(512*span(b-1)) = span(a)*span(b)
        assert(span((a + b) as nat) == 512 * span((a + b - 1) as nat));
        assert((a + b - 1) as nat == (a + (b - 1)) as nat);
        assert(span(b) == 512 * span((b - 1) as nat));
        assert(512 * (span(a) * span((b - 1) as nat)) == span(a) * (512 * span((b - 1) as nat)))
            by (nonlinear_arith);
    }
}

/// A positive multiple of `d` is at least `d`.
pub proof fn lemma_pos_multiple_ge(x: int, d: int)
    requires
        d > 0,
        x > 0,
        x % d == 0,
    ensures
        x >= d,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, d);
    assert(x == d * (x / d));
    assert(x / d >= 1) by (nonlinear_arith)
        requires
            d > 0,
            x > 0,
            x == d * (x / d),
    ;
    assert(x >= d) by (nonlinear_arith)
        requires
            d > 0,
            x / d >= 1,
            x == d * (x / d),
    ;
}

/// Two `d`-aligned values strictly ordered are at least `d` apart.
pub proof fn lemma_aligned_lt(a: int, m: int, d: int)
    requires
        d > 0,
        a % d == 0,
        m % d == 0,
        a < m,
    ensures
        a + d <= m,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, d);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, d);
    assert(a == d * (a / d) && m == d * (m / d));
    let q = m / d - a / d;
    assert(m - a == q * d) by (nonlinear_arith)
        requires
            a == d * (a / d),
            m == d * (m / d),
            q == m / d - a / d,
    ;
    assert((m - a) % d == 0) by {
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q, d);
    }
    lemma_pos_multiple_ge(m - a, d);
}

/// Alignment containment: a below-root node whose base is in window `w` has its
/// whole translated window inside `w`'s top-level (`span(ROOT_LEVEL)`) bucket. The
/// geometric core of the split partition. Phrased over the known window index `w`
/// (no division), so callers stay in range arithmetic.
pub proof fn lemma_node_window_in_bucket<V: PtPage>(t: PageTablePerms<V>, n: PFN, w: nat)
    requires
        t.store_wf(),
        t.contains(n),
        t.level(n) < ROOT_LEVEL,
        t.xlate_base_aligned(),
        w * span(ROOT_LEVEL) <= t.xlate_base(n),
        t.xlate_base(n) < (w + 1) * span(ROOT_LEVEL),
    ensures
        t.xlate_base(n) + span((t.level(n) + 1) as nat) <= (w + 1) * span(ROOT_LEVEL),
{
    let base = t.xlate_base(n) as int;
    let l1 = (t.level(n) + 1) as nat;
    let d = span(l1) as int;
    let big = span(ROOT_LEVEL) as int;
    lemma_span_pos(l1);
    lemma_span_pos(ROOT_LEVEL);
    // n is aligned to its own stride d.
    assert(t.xlate_base(n) % span((t.level(n) + 1) as nat) == 0);  // xlate_base_aligned
    assert(base % d == 0);
    // big factors as d * span(ROOT_LEVEL - l1), so (w+1)*big is a multiple of d.
    lemma_span_add(l1, (ROOT_LEVEL - l1) as nat);
    assert(l1 + (ROOT_LEVEL - l1) as nat == ROOT_LEVEL);
    let big_q = span((ROOT_LEVEL - l1) as nat) as int;
    assert(big == d * big_q);
    assert(((w + 1) * big) % d == 0) by {
        assert((w + 1) * big == ((w + 1) * big_q) * d) by (nonlinear_arith)
            requires
                big == d * big_q,
        ;
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic((w + 1) * big_q, d);
    }
    // base is d-aligned and strictly below the (d-aligned) window top, so a full d below.
    lemma_aligned_lt(base, (w + 1) * big, d);
}

/// Two equal-width windows that share a point are the same window.
pub proof fn lemma_windows_disjoint(x: int, w1: nat, w2: nat)
    requires
        w1 * span(ROOT_LEVEL) <= x < (w1 + 1) * span(ROOT_LEVEL),
        w2 * span(ROOT_LEVEL) <= x < (w2 + 1) * span(ROOT_LEVEL),
    ensures
        w1 == w2,
{
    lemma_span_pos(ROOT_LEVEL);
    let big = span(ROOT_LEVEL) as int;
    assert(w1 <= w2) by (nonlinear_arith)
        requires
            big > 0,
            w1 * big <= x,
            x < (w2 + 1) * big,
    ;
    assert(w2 <= w1) by (nonlinear_arith)
        requires
            big > 0,
            w2 * big <= x,
            x < (w1 + 1) * big,
    ;
}

/// Every base sits in some top-level window (`w = base / span(ROOT_LEVEL)`).
pub proof fn lemma_base_has_window(base: nat) -> (w: nat)
    ensures
        w * span(ROOT_LEVEL) <= base < (w + 1) * span(ROOT_LEVEL),
{
    lemma_span_pos(ROOT_LEVEL);
    let big = span(ROOT_LEVEL) as int;
    let w = base as int / big;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(base as int, big);
    assert(base == big * w + (base as int) % big);
    assert(0 <= (base as int) % big < big);
    assert(w >= 0) by (nonlinear_arith)
        requires
            big > 0,
            base >= 0,
            base == big * w + (base as int) % big,
            (base as int) % big < big,
    ;
    assert(w * big <= base < (w + 1) * big) by (nonlinear_arith)
        requires
            base == big * w + (base as int) % big,
            0 <= (base as int) % big < big,
    ;
    w as nat
}

// =====================================================================
// Structural closure: interior links never leave their top-level bucket
// =====================================================================

/// An interior (non-self-map) link drops exactly one level and keeps its target's
/// translated window inside the parent's.
pub proof fn lemma_edge_target_in_range<V: PtPage>(t: PageTablePerms<V>, n: PFN, i: nat)
    requires
        t.store_wf(),
        t.tree_inv(),
        t.xlate_base_consistent(),
        t.interior_at(n, i),
        !t.is_self_map(n, i),
    ensures
        t.level(n) >= 1,
        t.contains(t.entry(n, i).target),
        t.level(t.entry(n, i).target) == (t.level(n) - 1) as nat,
        t.xlate_base(n) <= t.xlate_base(t.entry(n, i).target),
        t.xlate_base(t.entry(n, i).target) + span(t.level(n)) <= t.xlate_base(n) + span(
            (t.level(n) + 1) as nat,
        ),
{
    broadcast use lemma_node_struct_wf, lemma_node_level_bound;

    let tgt = t.entry(n, i).target;
    let l = t.level(n);
    assert(t.node_wf(n));  // links_wf
    assert(t.entry(n, i).present && !t.entry(n, i).leaf);  // interior_at
    assert(l >= 1 && t.contains(tgt) && t.level(tgt) == (l - 1) as nat);  // node_wf else-branch
    assert(t.xlate_base(tgt) == t.entry_vpn_base(n, i));  // xlate_base_consistent
    assert(t.entry_vpn_base(n, i) == (t.xlate_base(n) + i * span(l)) as nat);
    lemma_span_pos(l);
    assert(i < ENTRIES);  // interior_at
    assert(span((l + 1) as nat) == 512 * span(l));
    assert(i * span(l) >= 0) by (nonlinear_arith);
    assert(t.xlate_base(tgt) + span(l) == t.xlate_base(n) + (i + 1) * span(l)) by (nonlinear_arith)
        requires
            t.xlate_base(tgt) == t.xlate_base(n) + i * span(l),
    ;
    assert((i + 1) * span(l) <= 512 * span(l)) by (nonlinear_arith)
        requires
            i + 1 <= 512,
            span(l) >= 0,
    ;
}

/// An interior (non-self-map) link from a below-root node in window `w` lands its
/// target in the same window `w`.
pub proof fn lemma_edge_in_bucket<V: PtPage>(t: PageTablePerms<V>, n: PFN, i: nat, w: nat)
    requires
        t.store_wf(),
        t.tree_inv(),
        t.xlate_base_consistent(),
        t.xlate_base_aligned(),
        t.interior_at(n, i),
        !t.is_self_map(n, i),
        t.level(n) < ROOT_LEVEL,
        w * span(ROOT_LEVEL) <= t.xlate_base(n),
        t.xlate_base(n) < (w + 1) * span(ROOT_LEVEL),
    ensures
        w * span(ROOT_LEVEL) <= t.xlate_base(t.entry(n, i).target),
        t.xlate_base(t.entry(n, i).target) < (w + 1) * span(ROOT_LEVEL),
{
    let l = t.level(n);
    lemma_edge_target_in_range(t, n, i);
    lemma_node_window_in_bucket(t, n, w);
    lemma_span_pos(l);
    // base(tgt) >= base(n) >= w*big, and base(tgt) < base(tgt)+span(l) <= base(n)+span(l+1) <= (w+1)*big.
}

/// A subtree node sits below the root (only the root is at `ROOT_LEVEL`).
pub proof fn lemma_in_subtree_below_root<V: PtPage>(t: PageTablePerms<V>, i: nat, n: PFN)
    requires
        t.store_wf(),
        t.tree_inv(),
        t.sub_idx() is None,
        t.in_subtree(i, n),
    ensures
        t.level(n) < ROOT_LEVEL,
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    assert(t.contains(n) && n != t.root());
    // root-unique: the only node at ROOT_LEVEL is the root.
    assert(t.level(n) != ROOT_LEVEL);
    assert(t.pages()[n].wf());
    assert(t.level(n) <= ROOT_LEVEL);
}

// =====================================================================
// The subtree is closed and singly-rooted at root[idx]
// =====================================================================

/// CL1 - downward closure: an interior link out of a subtree node stays in the
/// subtree.
pub proof fn lemma_subtree_downward_closed<V: PtPage>(
    t: PageTablePerms<V>,
    idx: nat,
    n: PFN,
    i: nat,
)
    requires
        t.store_wf(),
        t.tree_inv(),
        t.sub_idx() is None,
        t.xlate_base_consistent(),
        t.xlate_base_aligned(),
        t.in_subtree(idx, n),
        t.interior_at(n, i),
    ensures
        t.in_subtree(idx, t.entry(n, i).target),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    let tgt = t.entry(n, i).target;
    lemma_in_subtree_below_root(t, idx, n);  // level(n) < ROOT_LEVEL
    assert(!t.is_self_map(n, i));  // is_self_map needs level == ROOT_LEVEL
    lemma_edge_target_in_range(t, n, i);  // tgt live, level(tgt) == level(n)-1
    lemma_edge_in_bucket(t, n, i, idx);  // tgt base in idx's window
    // tgt != root: it is two-or-more levels below the top.
    assert(t.level(t.root()) == ROOT_LEVEL);  // tree_inv + full table
    assert(tgt != t.root());
}

/// CL2 - the subtree root: `root[idx]`'s target is in the subtree (for a real
/// top-level entry, not the self-map).
pub proof fn lemma_subtree_root_in<V: PtPage>(t: PageTablePerms<V>, idx: nat)
    requires
        t.store_wf(),
        t.tree_inv(),
        t.sub_idx() is None,
        t.xlate_base_consistent(),
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        t.interior_at(t.root(), idx),
    ensures
        t.in_subtree(idx, t.entry(t.root(), idx).target),
        t.xlate_base(t.entry(t.root(), idx).target) == idx * span(ROOT_LEVEL),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    let r = t.root();
    let c = t.entry(r, idx).target;
    lemma_span_pos(ROOT_LEVEL);
    assert(t.level(r) == ROOT_LEVEL);  // tree_inv + full table
    assert(!t.is_self_map(r, idx));  // idx != IDX_SELFMAP
    lemma_edge_target_in_range(t, r, idx);  // c live, level(c) == ROOT_LEVEL-1
    // base(c) == base(root) + idx*span(ROOT_LEVEL) == idx*span(ROOT_LEVEL).
    assert(t.xlate_base(c) == t.entry_vpn_base(r, idx));  // xlate_base_consistent
    assert(t.xlate_base(r) == 0);  // root_base for full table
    assert(t.entry_vpn_base(r, idx) == idx * span(ROOT_LEVEL));
    assert(idx * span(ROOT_LEVEL) < (idx + 1) * span(ROOT_LEVEL)) by (nonlinear_arith)
        requires
            span(ROOT_LEVEL) > 0,
    ;
    assert(c != r);  // c is a level below the root
}

/// CL3 - single entry: the only interior link into subtree `idx` is `root[idx]`;
/// any other interior link targeting the subtree comes from a node already in it.
pub proof fn lemma_subtree_incoming<V: PtPage>(
    t: PageTablePerms<V>,
    idx: nat,
    m: PFN,
    j: nat,
)
    requires
        t.store_wf(),
        t.tree_inv(),
        t.sub_idx() is None,
        t.xlate_base_consistent(),
        t.xlate_base_aligned(),
        idx < ENTRIES,
        t.interior_at(m, j),
        t.in_subtree(idx, t.entry(m, j).target),
    ensures
        (m == t.root() && j == idx) || t.in_subtree(idx, m),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    let r = t.root();
    let tgt = t.entry(m, j).target;
    let big = span(ROOT_LEVEL);
    lemma_span_pos(ROOT_LEVEL);
    assert(t.level(r) == ROOT_LEVEL);  // tree_inv + full table
    // tgt in subtree means it is non-root with base in idx's window.
    assert(idx * big <= t.xlate_base(tgt) < (idx + 1) * big);
    if m == r {
        // root link: not the self-map (its target is the root, excluded from the
        // subtree), so base(tgt) == j*big, forcing j == idx.
        assert(!t.is_self_map(r, j)) by {
            if t.is_self_map(r, j) {
                assert(t.entry(r, j).target == r);  // node_wf self-map branch
            }
        }
        assert(t.xlate_base(tgt) == t.entry_vpn_base(r, j));  // xlate_base_consistent
        assert(t.xlate_base(r) == 0);
        assert(t.entry_vpn_base(r, j) == j * big);
        assert(j * big <= t.xlate_base(tgt) < (j + 1) * big) by (nonlinear_arith)
            requires
                big > 0,
                t.xlate_base(tgt) == j * big,
        ;
        lemma_windows_disjoint(t.xlate_base(tgt) as int, j, idx);
    } else {
        // m is below the root, so it has a window w; the link keeps tgt in w, and tgt
        // is also in idx's window, so w == idx and m is in the subtree.
        assert(t.level(m) != ROOT_LEVEL && t.level(m) <= ROOT_LEVEL);  // root-unique + bound
        assert(!t.is_self_map(m, j));
        let w = lemma_base_has_window(t.xlate_base(m));
        lemma_edge_in_bucket(t, m, j, w);
        lemma_windows_disjoint(t.xlate_base(tgt) as int, w, idx);
        // w == idx, so m's base is in idx's window.
    }
}

/// `c == root[idx].target` is the UNIQUE node at the subtree's top level
/// (`ROOT_LEVEL-1`) inside the subtree: any such node is parented by `root[idx]`,
/// hence equals `c`. (The subtree root-uniqueness `split` hands the subtree view.)
pub proof fn lemma_subtree_unique_top<V: PtPage>(t: PageTablePerms<V>, idx: nat, n: PFN)
    requires
        t.store_wf(),
        t.tree_inv(),
        t.sub_idx() is None,
        t.xlate_base_consistent(),
        t.xlate_base_aligned(),
        idx < ENTRIES,
        t.interior_at(t.root(), idx),
        t.in_subtree(idx, n),
        t.level(n) == (ROOT_LEVEL - 1) as nat,
    ensures
        n == t.entry(t.root(), idx).target,
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    let r = t.root();
    let big = span(ROOT_LEVEL);
    lemma_span_pos(ROOT_LEVEL);
    assert(t.level(r) == ROOT_LEVEL);  // tree_inv + full table
    assert(n != r);  // levels differ
    assert(t.tree_wf());
    let (p, k): (PFN, nat) = choose|p: PFN, k: nat|
        #![trigger t.interior_at(p, k)]
        t.interior_at(p, k) && t.entry(p, k).target == n;
    assert(t.interior_at(p, k) && t.entry(p, k).target == n);
    assert(t.node_wf(p));
    assert(!t.is_self_map(p, k)) by {
        if t.is_self_map(p, k) {
            assert(t.entry(p, k).target == p);  // node_wf self-map branch => p == n, levels clash
        }
    }
    assert(t.level(p) == ROOT_LEVEL);  // level(n) == level(p)-1 == ROOT_LEVEL-1
    assert(p == r);  // root-unique
    // base(n) == k*big and base(n) in idx's window => k == idx, so (root,idx) targets n.
    assert(t.xlate_base(n) == t.entry_vpn_base(r, k));  // xlate_base_consistent
    assert(t.xlate_base(r) == 0);
    assert(t.entry_vpn_base(r, k) == k * big);
    assert(k * big <= t.xlate_base(n) < (k + 1) * big) by (nonlinear_arith)
        requires
            big > 0,
            t.xlate_base(n) == k * big,
    ;
    lemma_windows_disjoint(t.xlate_base(n) as int, k, idx);
}

/// A leaf's recorded base sits in the same top-level window as its node: if node `w`
/// covers vpn `b` and `w`'s base is in window `ww`, then so is `b`. The bridge
/// between the `va_map` key partition and the node partition.
pub proof fn lemma_leaf_base_window<V: PtPage>(t: PageTablePerms<V>, w: PFN, b: VPage, ww: nat)
    requires
        t.store_wf(),
        t.contains(w),
        t.level(w) < ROOT_LEVEL,
        t.xlate_base_aligned(),
        t.node_covers(w, b),
        ww * span(ROOT_LEVEL) <= t.xlate_base(w),
        t.xlate_base(w) < (ww + 1) * span(ROOT_LEVEL),
    ensures
        ww * span(ROOT_LEVEL) <= b < (ww + 1) * span(ROOT_LEVEL),
{
    lemma_node_window_in_bucket(t, w, ww);
    // node_covers: base(w) <= b < base(w)+span(level(w)+1) <= (ww+1)*big; and b >= base(w) >= ww*big.
}

// =====================================================================
// The split relation: `t0` -> (`tf` full remainder, `ts` subtree view)
// =====================================================================

/// `ts` is the subtree-view of full table `t0` checked out at top-level entry `idx`:
/// its root is `root[idx]`'s target, it owns exactly the subtree's nodes (same
/// permissions / bases), and the `va_map` keys in entry `idx`'s window.
pub open spec fn is_split_sub<V: PtPage>(
    t0: PageTablePerms<V>,
    ts: PageTablePerms<V>,
    idx: nat,
) -> bool {
    &&& ts.root() == t0.entry(t0.root(), idx).target
    &&& ts.sub_idx() == Some::<nat>(idx)
    &&& (forall|n: PFN| #[trigger] ts.contains(n) <==> t0.in_subtree(idx, n))
    &&& (forall|n: PFN| #[trigger] ts.contains(n) ==> ts.pages()[n] == t0.pages()[n])
    &&& (forall|n: PFN| #[trigger] ts.contains(n) ==> ts.xlate_base(n) == t0.xlate_base(n))
    &&& (forall|b: VPage| #[trigger]
        ts.va_map().dom().contains(b) <==> (t0.va_map().dom().contains(b)
            && PageTablePerms::<V>::vpn_in_top(idx, b)))
    &&& (forall|b: VPage| #[trigger]
        ts.va_map().dom().contains(b) ==> ts.va_map()[b] == t0.va_map()[b])
}

/// Per-node bridge: on the subtree's nodes, `ts` reads identical to `t0` for every
/// structural accessor the invariants touch.
proof fn lemma_split_sub_bridge<V: PtPage>(t0: PageTablePerms<V>, ts: PageTablePerms<V>, idx: nat)
    requires
        t0.store_wf(),
        is_split_sub(t0, ts, idx),
    ensures
        forall|n: PFN| #[trigger] ts.contains(n) ==> {
            &&& ts.level(n) == t0.level(n)
            &&& ts.node(n) == t0.node(n)
        },
        forall|n: PFN, i: nat| #![trigger ts.interior_at(n, i)]
            ts.contains(n) ==> {
                &&& ts.interior_at(n, i) == t0.interior_at(n, i)
                &&& ts.leaf_at(n, i) == t0.leaf_at(n, i)
                &&& ts.entry(n, i) == t0.entry(n, i)
            },
{
    assert forall|n: PFN| #[trigger] ts.contains(n) implies {
        &&& ts.level(n) == t0.level(n)
        &&& ts.node(n) == t0.node(n)
    } by {
        assert(ts.pages()[n] == t0.pages()[n]);
        assert(t0.contains(n));  // in_subtree
    }
    assert forall|n: PFN, i: nat| #![trigger ts.interior_at(n, i)]
        ts.contains(n) implies {
            &&& ts.interior_at(n, i) == t0.interior_at(n, i)
            &&& ts.leaf_at(n, i) == t0.leaf_at(n, i)
            &&& ts.entry(n, i) == t0.entry(n, i)
        } by {
        assert(t0.contains(n));
        assert(ts.node(n) == t0.node(n) && ts.level(n) == t0.level(n));
    }
}

/// The subtree view `ts` is a valid tree (`store_wf` + `tree_inv`).
#[verifier::rlimit(60)]
pub proof fn lemma_split_sub_tree<V: PtPage>(
    t0: PageTablePerms<V>,
    ts: PageTablePerms<V>,
    idx: nat,
)
    requires
        t0.store_wf(),
        t0.wf(),
        t0.mapping_wf(),
        t0.sub_idx() is None,
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        t0.interior_at(t0.root(), idx),
        is_split_sub(t0, ts, idx),
    ensures
        ts.store_wf(),
        ts.tree_inv(),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    lemma_split_sub_bridge(t0, ts, idx);
    let r = t0.root();
    let c = t0.entry(r, idx).target;
    assert(ts.root() == c);
    // c is the subtree root: in the subtree, at level ROOT_LEVEL-1.
    lemma_subtree_root_in(t0, idx);
    lemma_edge_target_in_range(t0, r, idx);
    assert(t0.level(r) == ROOT_LEVEL);
    assert(t0.in_subtree(idx, c) && t0.level(c) == (ROOT_LEVEL - 1) as nat);
    assert(ts.contains(c));
    assert(ts.level(c) == (ROOT_LEVEL - 1) as nat);
    assert(ts.root_level() == (ROOT_LEVEL - 1) as nat);  // sub_idx Some

    // store_wf transfers node-by-node.
    assert(ts.store_wf()) by {
        assert forall|n: PFN| ts.contains(n) implies (#[trigger] ts.pages()[n].wf()
            && ts.pages()[n].pfn() == n) by {
            assert(ts.pages()[n] == t0.pages()[n]);
            assert(t0.contains(n));
        }
    }

    // links_wf: an interior link of a subtree node stays in the subtree (CL1), so
    // its target is live in `ts`; leaves keep their alignment.
    assert(ts.links_wf()) by {
        assert forall|n: PFN| ts.contains(n) implies #[trigger] ts.node_wf(n) by {
            assert(t0.contains(n) && t0.node_wf(n));
            assert forall|i: nat|
                #![trigger ts.entry(n, i)]
                (i < ENTRIES && ts.node(n).e.dom().contains(i) && ts.entry(n, i).present) implies {
                    let e = ts.entry(n, i);
                    if ts.level(n) == 0 || e.leaf {
                        &&& ts.level(n) <= 2
                        &&& e.target % span(ts.level(n)) == 0
                    } else {
                        &&& ts.contains(e.target)
                        &&& if ts.is_self_map(n, i) {
                            e.target == n
                        } else {
                            ts.level(n) >= 1 && ts.level(e.target) == ts.level(n) - 1
                        }
                    }
                } by {
                assert(ts.entry(n, i) == t0.entry(n, i) && ts.level(n) == t0.level(n));
                assert(!ts.is_self_map(n, i));  // sub_idx Some
                if ts.level(n) != 0 && !ts.entry(n, i).leaf {
                    assert(t0.interior_at(n, i));
                    lemma_subtree_downward_closed(t0, idx, n, i);  // target in subtree
                    assert(ts.contains(t0.entry(n, i).target));
                    assert(ts.level(t0.entry(n, i).target) == t0.level(t0.entry(n, i).target));
                }
            }
        }
    }

    // tree_wf, clause by clause.
    assert(ts.tree_wf()) by {
        // root-unique: any subtree node at ROOT_LEVEL-1 is `c`.
        assert forall|n: PFN| #![trigger ts.contains(n)]
            ts.contains(n) && ts.level(n) == ts.root_level() implies n == c by {
            assert(t0.in_subtree(idx, n) && t0.level(n) == (ROOT_LEVEL - 1) as nat);
            lemma_subtree_unique_top(t0, idx, n);
        }
        // self_map_inv: vacuous for a subtree.
        assert(ts.self_map_inv());
        // injectivity: subtree interiors are t0 interiors, inheriting it.
        assert forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
            (#[trigger] ts.interior_at(n1, i1) && #[trigger] ts.interior_at(n2, i2) && ts.entry(
                n1,
                i1,
            ).target == ts.entry(n2, i2).target) implies (n1 == n2 && i1 == i2) by {
            assert(t0.interior_at(n1, i1) && ts.entry(n1, i1) == t0.entry(n1, i1));
            assert(t0.interior_at(n2, i2) && ts.entry(n2, i2) == t0.entry(n2, i2));
        }
        // connectivity: a non-root subtree node keeps its parent, which (CL3) is also
        // in the subtree.
        assert forall|x: PFN| #![trigger ts.contains(x)]
            (ts.contains(x) && x != ts.root()) implies exists|p: PFN, k: nat|
            #[trigger] ts.interior_at(p, k) && ts.entry(p, k).target == x by {
            assert(t0.in_subtree(idx, x) && x != c);
            assert(t0.contains(x) && x != r);
            let (p, k): (PFN, nat) = choose|p: PFN, k: nat|
                #![trigger t0.interior_at(p, k)]
                t0.interior_at(p, k) && t0.entry(p, k).target == x;
            assert(t0.interior_at(p, k) && t0.entry(p, k).target == x);
            lemma_subtree_incoming(t0, idx, p, k);  // (p==root && k==idx) || p in subtree
            // p == root would force x == c (root[idx] is c's only parent), excluded.
            if p == r {
                lemma_subtree_root_in(t0, idx);
                assert(t0.interior_at(r, idx) && t0.entry(r, idx).target == c);
                assert(k == idx);  // injectivity: only one root entry targets x...
                assert(x == c);
            }
            assert(t0.in_subtree(idx, p));
            assert(ts.contains(p));
            assert(ts.interior_at(p, k) && ts.entry(p, k).target == x);
        }
    }

    // ad_pinned: subtree entries are unchanged from `t0`, where they were pinned.
    assert(ts.ad_pinned()) by {
        assert forall|n: PFN, i: nat|
            (ts.contains(n) && i < ENTRIES && ts.node(n).e.dom().contains(i)) implies entry_pinned(
                #[trigger] ts.entry(n, i),
            ) by {
            assert(t0.contains(n) && ts.entry(n, i) == t0.entry(n, i));
        }
    }
}

/// Every entry's base vpn is covered by its node (the entry index is `< ENTRIES`).
pub proof fn lemma_entry_covers_base<V: PtPage>(t: PageTablePerms<V>, n: PFN, i: nat)
    requires
        i < ENTRIES,
    ensures
        t.node_covers(n, t.entry_vpn_base(n, i)),
{
    let l = t.level(n);
    lemma_span_pos(l);
    assert(span((l + 1) as nat) == 512 * span(l));
    assert(i * span(l) >= 0) by (nonlinear_arith);
    assert(i * span(l) < 512 * span(l)) by (nonlinear_arith)
        requires
            i < 512,
            span(l) > 0,
    ;
}

/// The subtree view `ts` carries the user-mapping invariant `mapping_wf`.
#[verifier::rlimit(60)]
pub proof fn lemma_split_sub_mapping<V: PtPage>(
    t0: PageTablePerms<V>,
    ts: PageTablePerms<V>,
    idx: nat,
)
    requires
        t0.store_wf(),
        t0.wf(),
        t0.mapping_wf(),
        t0.sub_idx() is None,
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        t0.interior_at(t0.root(), idx),
        is_split_sub(t0, ts, idx),
    ensures
        ts.mapping_wf(),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    lemma_split_sub_bridge(t0, ts, idx);
    let r = t0.root();
    let c = t0.entry(r, idx).target;
    let big = span(ROOT_LEVEL);
    lemma_span_pos(ROOT_LEVEL);
    lemma_subtree_root_in(t0, idx);
    lemma_edge_target_in_range(t0, r, idx);
    assert(t0.level(r) == ROOT_LEVEL);
    assert(t0.in_subtree(idx, c) && t0.xlate_base(c) == idx * big);
    assert(ts.contains(c));  // iff with in_subtree(idx, c)
    assert(ts.xlate_base(c) == t0.xlate_base(c));  // is_split_sub, ts.contains(c)
    assert(ts.xlate_base(c) == idx * big);
    assert(ts.root_base() == idx * big);  // sub_idx Some(idx)

    // permissive interiors transfer (subtree interiors are t0 interiors).
    assert(ts.interiors_permissive()) by {
        assert forall|n: PFN, i: nat| #[trigger] ts.interior_at(n, i) implies permissive(
            ts.entry(n, i),
        ) by {
            assert(ts.contains(n) && t0.interior_at(n, i) && ts.entry(n, i) == t0.entry(n, i));
        }
    }
    // xlate_base_consistent: the root's base is the subtree base; links are unchanged.
    assert(ts.xlate_base_consistent()) by {
        assert(ts.xlate_base(ts.root()) == ts.root_base());
        assert forall|p: PFN, i: nat| (#[trigger] ts.interior_at(p, i) && !ts.is_self_map(p, i))
            implies ts.xlate_base(ts.entry(p, i).target) == ts.entry_vpn_base(p, i) by {
            assert(ts.contains(p) && t0.interior_at(p, i) && ts.entry(p, i) == t0.entry(p, i));
            assert(!t0.is_self_map(p, i)) by { lemma_in_subtree_below_root(t0, idx, p); }
            let tgt = t0.entry(p, i).target;
            lemma_subtree_downward_closed(t0, idx, p, i);
            assert(ts.contains(tgt) && ts.xlate_base(tgt) == t0.xlate_base(tgt));
            assert(ts.entry_vpn_base(p, i) == t0.entry_vpn_base(p, i));  // base/level of p unchanged
        }
    }
    // xlate_base_aligned: subtree nodes keep their (aligned) bases and levels.
    assert(ts.xlate_base_aligned()) by {
        assert forall|n: PFN| #[trigger] ts.contains(n) implies ts.xlate_base(n) % span(
            (ts.level(n) + 1) as nat,
        ) == 0 by {
            assert(t0.contains(n) && ts.xlate_base(n) == t0.xlate_base(n) && ts.level(n) == t0.level(
                n,
            ));
        }
    }

    // mapping_inv.
    assert(ts.mapping_inv()) by {
        // (Q): each subtree key is recorded by a subtree leaf - the recording node
        // covers the key, so it lives in the same (idx) window, hence in the subtree.
        assert forall|b: VPage| #[trigger] ts.va_map().dom().contains(b) implies {
            let m = ts.va_map()[b];
            &&& in_user_region(b)
            &&& b % m.size.pages() == 0
            &&& m.frame % m.size.pages() == 0
            &&& exists|w: PFN| ts.records_leaf(b, m, w, pt_index(b, level_of_size(m.size)))
        } by {
            assert(t0.va_map().dom().contains(b) && PageTablePerms::<V>::vpn_in_top(idx, b));
            assert(ts.va_map()[b] == t0.va_map()[b]);
            let m = t0.va_map()[b];
            let ii = pt_index(b, level_of_size(m.size));
            let w = choose|w: PFN| t0.records_leaf(b, m, w, ii);
            assert(t0.records_leaf(b, m, w, ii));
            // w covers b and is a leaf at level <= 2, so it has a window matching idx.
            assert(t0.level(w) == level_of_size(m.size) && level_of_size(m.size) <= 2);
            assert(t0.level(w) < ROOT_LEVEL);
            assert(t0.node_covers(w, b));  // records_leaf
            let ww = lemma_base_has_window(t0.xlate_base(w));
            lemma_leaf_base_window(t0, w, b, ww);  // b in ww's window
            lemma_windows_disjoint(b as int, ww, idx);  // ww == idx
            assert(t0.contains(w) && w != r);  // a leaf node is below the root
            assert(t0.in_subtree(idx, w));
            assert(ts.contains(w));  // iff with in_subtree(idx, w)
            assert(ts.level(w) == t0.level(w) && ts.node(w) == t0.node(w));  // bridge
            assert(ts.xlate_base(w) == t0.xlate_base(w));  // is_split_sub
            assert(ts.records_leaf(b, m, w, ii));
        }
        // (P): a subtree user-region leaf's base lands in idx's window, so it is a
        // subtree key - and t0 recorded it.
        assert forall|n: PFN, i: nat|
            (#[trigger] ts.leaf_at(n, i) && in_user_region(ts.entry_vpn_base(n, i)))
                implies ts.va_map().dom().contains(ts.entry_vpn_base(n, i)) by {
            assert(ts.contains(n) && t0.leaf_at(n, i) && ts.entry_vpn_base(n, i) == t0.entry_vpn_base(
                n,
                i,
            ));
            let b = t0.entry_vpn_base(n, i);
            assert(t0.va_map().dom().contains(b));  // t0.mapping_inv (P)
            // n is in idx's window and covers b, so b is in idx's window.
            assert(t0.in_subtree(idx, n));
            lemma_in_subtree_below_root(t0, idx, n);
            assert(t0.node_covers(n, b)) by {
                assert(t0.leaf_at(n, i));  // i < ENTRIES
                lemma_entry_covers_base(t0, n, i);
            }
            lemma_leaf_base_window(t0, n, b, idx);  // base(n) in idx window (in_subtree)
            assert(PageTablePerms::<V>::vpn_in_top(idx, b));
        }
        // (C),(D): subtree keys/values are a subset of t0's, inheriting disjointness.
        assert forall|b1: VPage, b2: VPage|
            (b1 != b2 && #[trigger] ts.va_map().dom().contains(b1) && #[trigger] ts.va_map().dom().contains(
                b2,
            )) implies ({
                let f1 = ts.va_map()[b1].frame;
                let f2 = ts.va_map()[b2].frame;
                &&& (f1 + ts.va_map()[b1].size.pages() <= f2 || f2 + ts.va_map()[b2].size.pages() <= f1)
                &&& (b1 + ts.va_map()[b1].size.pages() <= b2 || b2 + ts.va_map()[b2].size.pages() <= b1)
            }) by {
            assert(t0.va_map().dom().contains(b1) && ts.va_map()[b1] == t0.va_map()[b1]);
            assert(t0.va_map().dom().contains(b2) && ts.va_map()[b2] == t0.va_map()[b2]);
        }
    }
}

/// The subtree view is a valid, mapping-complete page table.
pub proof fn lemma_split_sub<V: PtPage>(t0: PageTablePerms<V>, ts: PageTablePerms<V>, idx: nat)
    requires
        t0.store_wf(),
        t0.wf(),
        t0.mapping_wf(),
        t0.sub_idx() is None,
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        t0.interior_at(t0.root(), idx),
        is_split_sub(t0, ts, idx),
    ensures
        ts.wf(),
        ts.mapping_wf(),
{
    lemma_split_sub_tree(t0, ts, idx);
    lemma_split_sub_mapping(t0, ts, idx);
}

// =====================================================================
// The full-table remainder after carving out the subtree
// =====================================================================

/// `tf` is full table `t0` with the subtree under `idx` removed: `root[idx]` cleared,
/// the subtree's nodes dropped, and the `va_map` keys outside entry `idx`'s window
/// kept. `store_wf` for the (modified) root is established by the exec op, so it is a
/// hypothesis here.
pub open spec fn is_split_full<V: PtPage>(
    t0: PageTablePerms<V>,
    tf: PageTablePerms<V>,
    idx: nat,
) -> bool {
    &&& tf.root() == t0.root()
    &&& tf.sub_idx() == t0.sub_idx()
    &&& (forall|n: PFN| #[trigger]
        tf.contains(n) <==> (t0.contains(n) && !t0.in_subtree(idx, n)))
    &&& tf.node(t0.root()) == t0.node(t0.root()).update(idx, entry_absent())
    &&& (forall|n: PFN| #[trigger]
        tf.contains(n) ==> (n == t0.root() || tf.node(n) == t0.node(n)))
    &&& (forall|n: PFN| #[trigger] tf.contains(n) ==> tf.level(n) == t0.level(n))
    &&& (forall|n: PFN| #[trigger] tf.contains(n) ==> tf.xlate_base(n) == t0.xlate_base(n))
    &&& (forall|b: VPage| #[trigger]
        tf.va_map().dom().contains(b) <==> (t0.va_map().dom().contains(b)
            && !PageTablePerms::<V>::vpn_in_top(idx, b)))
    &&& (forall|b: VPage| #[trigger]
        tf.va_map().dom().contains(b) ==> tf.va_map()[b] == t0.va_map()[b])
}

/// Entry bridge for the full remainder: `tf` reads like `t0` everywhere except the
/// cleared root slot `(root, idx)`.
proof fn lemma_split_full_bridge<V: PtPage>(t0: PageTablePerms<V>, tf: PageTablePerms<V>, idx: nat)
    requires
        t0.store_wf(),
        tf.store_wf(),
        idx < ENTRIES,
        is_split_full(t0, tf, idx),
    ensures
        forall|n: PFN, i: nat| #![trigger tf.entry(n, i)]
            (tf.contains(n) && (n != t0.root() || i != idx)) ==> tf.entry(n, i) == t0.entry(n, i),
        forall|n: PFN, i: nat| #![trigger tf.interior_at(n, i)]
            (tf.contains(n) && (n != t0.root() || i != idx)) ==> {
                &&& tf.interior_at(n, i) == t0.interior_at(n, i)
                &&& tf.leaf_at(n, i) == t0.leaf_at(n, i)
            },
{
    broadcast use lemma_node_struct_wf;

    let r = t0.root();
    assert(t0.node(r).e.dom().contains(idx));  // full node domain
    assert forall|n: PFN, i: nat| #![trigger tf.entry(n, i)]
        (tf.contains(n) && (n != r || i != idx)) implies tf.entry(n, i) == t0.entry(n, i) by {
        assert(t0.contains(n));  // contains-iff
        if n == r {
            assert(tf.node(r).e[i] == t0.node(r).e.insert(idx, entry_absent())[i]);
        }
    }
    assert forall|n: PFN, i: nat| #![trigger tf.interior_at(n, i)]
        (tf.contains(n) && (n != r || i != idx)) implies {
            &&& tf.interior_at(n, i) == t0.interior_at(n, i)
            &&& tf.leaf_at(n, i) == t0.leaf_at(n, i)
        } by {
        assert(t0.contains(n) && tf.level(n) == t0.level(n) && tf.entry(n, i) == t0.entry(n, i));
    }
}

/// The full remainder `tf` is a valid tree (`tree_inv`); `store_wf` is assumed.
#[verifier::rlimit(80)]
pub proof fn lemma_split_full_tree<V: PtPage>(
    t0: PageTablePerms<V>,
    tf: PageTablePerms<V>,
    idx: nat,
)
    requires
        t0.store_wf(),
        t0.wf(),
        t0.mapping_wf(),
        t0.sub_idx() is None,
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        t0.interior_at(t0.root(), idx),
        tf.store_wf(),
        is_split_full(t0, tf, idx),
    ensures
        tf.tree_inv(),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    lemma_split_full_bridge(t0, tf, idx);
    let r = t0.root();
    assert(tf.root() == r && tf.sub_idx() is None);
    assert(t0.level(r) == ROOT_LEVEL);
    // root survives (it is not in the subtree).
    assert(!t0.in_subtree(idx, r));
    assert(tf.contains(r));
    assert(tf.level(r) == ROOT_LEVEL && tf.root_level() == ROOT_LEVEL);
    assert(tf.entry(r, idx) == entry_absent()) by {
        assert(tf.node(r).e[idx] == t0.node(r).e.insert(idx, entry_absent())[idx]);
        assert(t0.node(r).e.dom().contains(idx));
    }
    assert(!tf.interior_at(r, idx));

    // every tf interior is a t0 interior (off the cleared slot), with the same target.
    assert forall|n: PFN, i: nat| #[trigger] tf.interior_at(n, i) implies (t0.interior_at(n, i)
        && tf.entry(n, i) == t0.entry(n, i) && (n != r || i != idx)) by {
        assert(tf.contains(n));
        if n == r && i == idx {
            assert(!tf.interior_at(r, idx));
        }
    }

    // links_wf: a surviving link's target is not in the subtree (CL1/CL3), hence survives.
    assert(tf.links_wf()) by {
        assert forall|n: PFN| tf.contains(n) implies #[trigger] tf.node_wf(n) by {
            assert(t0.contains(n) && t0.node_wf(n) && !t0.in_subtree(idx, n));
            assert forall|i: nat|
                #![trigger tf.entry(n, i)]
                (i < ENTRIES && tf.node(n).e.dom().contains(i) && tf.entry(n, i).present) implies {
                    let e = tf.entry(n, i);
                    if tf.level(n) == 0 || e.leaf {
                        &&& tf.level(n) <= 2
                        &&& e.target % span(tf.level(n)) == 0
                    } else {
                        &&& tf.contains(e.target)
                        &&& if tf.is_self_map(n, i) {
                            e.target == n
                        } else {
                            tf.level(n) >= 1 && tf.level(e.target) == tf.level(n) - 1
                        }
                    }
                } by {
                assert(n != r || i != idx);  // (r,idx) is absent, not present
                assert(tf.entry(n, i) == t0.entry(n, i) && tf.level(n) == t0.level(n));
                assert(tf.is_self_map(n, i) == t0.is_self_map(n, i));
                if tf.level(n) != 0 && !tf.entry(n, i).leaf {
                    assert(t0.interior_at(n, i));
                    let tgt = t0.entry(n, i).target;
                    if !t0.is_self_map(n, i) {
                        // a surviving non-self-map link's target is not in the subtree.
                        assert(!t0.in_subtree(idx, tgt)) by {
                            if t0.in_subtree(idx, tgt) {
                                lemma_subtree_incoming(t0, idx, n, i);
                                // (n==r && i==idx) impossible; n in subtree impossible.
                            }
                        }
                        assert(t0.contains(tgt));  // t0.node_wf
                        assert(tf.contains(tgt));  // contains-iff: live & not in subtree
                        assert(tf.level(tgt) == t0.level(tgt));
                    } else {
                        assert(tgt == n && tf.contains(n));  // self-map target is the node itself
                    }
                }
            }
        }
    }

    // tree_wf.
    assert(tf.tree_wf()) by {
        assert forall|n: PFN| #![trigger tf.contains(n)]
            tf.contains(n) && tf.level(n) == tf.root_level() implies n == r by {
            assert(t0.contains(n) && t0.level(n) == ROOT_LEVEL);
        }
        // self-map survives (SELFMAP != idx).
        assert(tf.self_map_inv()) by {
            assert(t0.interior_at(r, IDX_SELFMAP) && t0.entry(r, IDX_SELFMAP).target == r);
            assert(IDX_SELFMAP != idx);
            assert(tf.entry(r, IDX_SELFMAP) == t0.entry(r, IDX_SELFMAP));
            assert(tf.interior_at(r, IDX_SELFMAP));
        }
        assert forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
            (#[trigger] tf.interior_at(n1, i1) && #[trigger] tf.interior_at(n2, i2) && tf.entry(
                n1,
                i1,
            ).target == tf.entry(n2, i2).target) implies (n1 == n2 && i1 == i2) by {
            assert(t0.interior_at(n1, i1) && tf.entry(n1, i1) == t0.entry(n1, i1));
            assert(t0.interior_at(n2, i2) && tf.entry(n2, i2) == t0.entry(n2, i2));
        }
        // connectivity: a surviving non-root node's t0 parent survives (its target,
        // this node, is not in the subtree, so neither is the parent - CL1).
        assert forall|x: PFN| #![trigger tf.contains(x)]
            (tf.contains(x) && x != r) implies exists|p: PFN, k: nat|
            #[trigger] tf.interior_at(p, k) && tf.entry(p, k).target == x by {
            assert(t0.contains(x) && !t0.in_subtree(idx, x) && x != r);
            let (p, k): (PFN, nat) = choose|p: PFN, k: nat|
                #![trigger t0.interior_at(p, k)]
                t0.interior_at(p, k) && t0.entry(p, k).target == x;
            assert(t0.interior_at(p, k) && t0.entry(p, k).target == x);
            // p is not in the subtree (else x would be, CL1); and (p,k) != (r,idx)
            // (that targets the subtree root, which is in the subtree, != x).
            assert(!t0.in_subtree(idx, p)) by {
                if t0.in_subtree(idx, p) {
                    lemma_subtree_downward_closed(t0, idx, p, k);  // => x in subtree
                }
            }
            assert(p != r || k != idx) by {
                if p == r && k == idx {
                    lemma_subtree_root_in(t0, idx);  // entry(r,idx).target in subtree, == x
                }
            }
            assert(tf.contains(p));
            assert(tf.interior_at(p, k) && tf.entry(p, k).target == x);
        }
    }

    // ad_pinned: the cleared slot is absent (pinned); the rest is unchanged.
    assert(tf.ad_pinned()) by {
        assert forall|n: PFN, i: nat|
            (tf.contains(n) && i < ENTRIES && tf.node(n).e.dom().contains(i)) implies entry_pinned(
                #[trigger] tf.entry(n, i),
            ) by {
            if n == r && i == idx {
                assert(tf.entry(r, idx) == entry_absent());
            } else {
                assert(t0.contains(n) && tf.entry(n, i) == t0.entry(n, i));
            }
        }
    }
}

/// The full remainder `tf` carries the user-mapping invariant `mapping_wf`.
#[verifier::rlimit(80)]
pub proof fn lemma_split_full_mapping<V: PtPage>(
    t0: PageTablePerms<V>,
    tf: PageTablePerms<V>,
    idx: nat,
)
    requires
        t0.store_wf(),
        t0.wf(),
        t0.mapping_wf(),
        t0.sub_idx() is None,
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        t0.interior_at(t0.root(), idx),
        tf.store_wf(),
        tf.tree_inv(),
        is_split_full(t0, tf, idx),
    ensures
        tf.mapping_wf(),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    lemma_split_full_bridge(t0, tf, idx);
    let r = t0.root();
    let big = span(ROOT_LEVEL);
    lemma_span_pos(ROOT_LEVEL);
    assert(t0.level(r) == ROOT_LEVEL && tf.level(r) == ROOT_LEVEL);
    assert(tf.entry(r, idx) == entry_absent()) by {
        assert(tf.node(r).e[idx] == t0.node(r).e.insert(idx, entry_absent())[idx]);
        assert(t0.node(r).e.dom().contains(idx));
    }
    // every tf interior is a t0 interior off the cleared slot.
    assert forall|n: PFN, i: nat| #[trigger] tf.interior_at(n, i) implies (t0.interior_at(n, i)
        && tf.entry(n, i) == t0.entry(n, i) && (n != r || i != idx)) by {
        assert(tf.contains(n));
        if n == r && i == idx {
            assert(!tf.interior_at(r, idx));
        }
    }

    assert(tf.interiors_permissive()) by {
        assert forall|n: PFN, i: nat| #[trigger] tf.interior_at(n, i) implies permissive(
            tf.entry(n, i),
        ) by {
            assert(t0.interior_at(n, i) && tf.entry(n, i) == t0.entry(n, i));
        }
    }
    assert(tf.xlate_base_consistent()) by {
        assert(tf.xlate_base(tf.root()) == t0.xlate_base(r));
        assert(tf.xlate_base(tf.root()) == tf.root_base());  // both 0
        assert forall|p: PFN, i: nat| (#[trigger] tf.interior_at(p, i) && !tf.is_self_map(p, i))
            implies tf.xlate_base(tf.entry(p, i).target) == tf.entry_vpn_base(p, i) by {
            assert(t0.interior_at(p, i) && tf.entry(p, i) == t0.entry(p, i));
            assert(tf.is_self_map(p, i) == t0.is_self_map(p, i));
            let tgt = t0.entry(p, i).target;
            assert(!t0.in_subtree(idx, tgt)) by {
                if t0.in_subtree(idx, tgt) {
                    lemma_subtree_incoming(t0, idx, p, i);  // forces (r,idx) or p in subtree
                    assert(p != r || i != idx);
                }
            }
            assert(t0.contains(tgt));  // t0.node_wf
            assert(tf.contains(tgt) && tf.xlate_base(tgt) == t0.xlate_base(tgt));
            assert(tf.entry_vpn_base(p, i) == t0.entry_vpn_base(p, i));
        }
    }
    assert(tf.xlate_base_aligned()) by {
        assert forall|n: PFN| #[trigger] tf.contains(n) implies tf.xlate_base(n) % span(
            (tf.level(n) + 1) as nat,
        ) == 0 by {
            assert(t0.contains(n) && tf.xlate_base(n) == t0.xlate_base(n) && tf.level(n) == t0.level(
                n,
            ));
        }
    }

    assert(tf.mapping_inv()) by {
        // (Q): an out-of-window key is recorded by a node outside the subtree, which
        // therefore survives in `tf`.
        assert forall|b: VPage| #[trigger] tf.va_map().dom().contains(b) implies {
            let m = tf.va_map()[b];
            &&& in_user_region(b)
            &&& b % m.size.pages() == 0
            &&& m.frame % m.size.pages() == 0
            &&& exists|w: PFN| tf.records_leaf(b, m, w, pt_index(b, level_of_size(m.size)))
        } by {
            assert(t0.va_map().dom().contains(b) && !PageTablePerms::<V>::vpn_in_top(idx, b));
            assert(tf.va_map()[b] == t0.va_map()[b]);
            let m = t0.va_map()[b];
            let ii = pt_index(b, level_of_size(m.size));
            let w = choose|w: PFN| t0.records_leaf(b, m, w, ii);
            assert(t0.records_leaf(b, m, w, ii));
            assert(t0.node_covers(w, b));
            assert(t0.level(w) == level_of_size(m.size) && level_of_size(m.size) <= 2);
            assert(t0.level(w) < ROOT_LEVEL);
            let ww = lemma_base_has_window(t0.xlate_base(w));
            lemma_leaf_base_window(t0, w, b, ww);  // b in ww's window
            assert(ww != idx) by {
                if ww == idx {
                    assert(PageTablePerms::<V>::vpn_in_top(idx, b));  // b in ww == idx window
                }
            }
            assert(t0.contains(w) && w != r);  // leaf node is below the root
            assert(!t0.in_subtree(idx, w)) by {
                if t0.in_subtree(idx, w) {
                    lemma_windows_disjoint(t0.xlate_base(w) as int, ww, idx);  // ww == idx, contra
                }
            }
            assert(tf.contains(w));
            assert(tf.node(w) == t0.node(w) && tf.level(w) == t0.level(w) && tf.xlate_base(w)
                == t0.xlate_base(w));
            assert(tf.records_leaf(b, m, w, ii));
        }
        // (P): a surviving user-region leaf's base is outside the window, so it is a
        // surviving key.
        assert forall|n: PFN, i: nat|
            (#[trigger] tf.leaf_at(n, i) && in_user_region(tf.entry_vpn_base(n, i)))
                implies tf.va_map().dom().contains(tf.entry_vpn_base(n, i)) by {
            assert(tf.contains(n));
            assert(n != r) by {
                if n == r {
                    assert(tf.node_wf(r));  // tf.links_wf: no present leaf at ROOT_LEVEL
                }
            }
            assert(tf.entry(n, i) == t0.entry(n, i) && tf.level(n) == t0.level(n) && tf.xlate_base(n)
                == t0.xlate_base(n));
            assert(t0.leaf_at(n, i) && tf.entry_vpn_base(n, i) == t0.entry_vpn_base(n, i));
            let b = t0.entry_vpn_base(n, i);
            assert(t0.va_map().dom().contains(b));  // t0.mapping_inv (P)
            // n survives (not in subtree, != root), so base(n) is out of idx's window.
            assert(t0.contains(n) && !t0.in_subtree(idx, n));
            assert(t0.level(n) < ROOT_LEVEL);
            lemma_entry_covers_base(t0, n, i);  // node_covers(n, b)
            let wn = lemma_base_has_window(t0.xlate_base(n));
            lemma_leaf_base_window(t0, n, b, wn);  // b in wn's window
            assert(wn != idx) by {
                if wn == idx {
                    assert(t0.in_subtree(idx, n));  // base(n) in wn == idx window
                }
            }
            assert(!PageTablePerms::<V>::vpn_in_top(idx, b)) by {
                if PageTablePerms::<V>::vpn_in_top(idx, b) {
                    lemma_windows_disjoint(b as int, wn, idx);
                }
            }
        }
        // (C),(D): tf keys/values are a subset of t0's.
        assert forall|b1: VPage, b2: VPage|
            (b1 != b2 && #[trigger] tf.va_map().dom().contains(b1) && #[trigger] tf.va_map().dom().contains(
                b2,
            )) implies ({
                let f1 = tf.va_map()[b1].frame;
                let f2 = tf.va_map()[b2].frame;
                &&& (f1 + tf.va_map()[b1].size.pages() <= f2 || f2 + tf.va_map()[b2].size.pages() <= f1)
                &&& (b1 + tf.va_map()[b1].size.pages() <= b2 || b2 + tf.va_map()[b2].size.pages() <= b1)
            }) by {
            assert(t0.va_map().dom().contains(b1) && tf.va_map()[b1] == t0.va_map()[b1]);
            assert(t0.va_map().dom().contains(b2) && tf.va_map()[b2] == t0.va_map()[b2]);
        }
    }
}

/// The full remainder is a valid, mapping-complete page table.
pub proof fn lemma_split_full<V: PtPage>(t0: PageTablePerms<V>, tf: PageTablePerms<V>, idx: nat)
    requires
        t0.store_wf(),
        t0.wf(),
        t0.mapping_wf(),
        t0.sub_idx() is None,
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        t0.interior_at(t0.root(), idx),
        tf.store_wf(),
        is_split_full(t0, tf, idx),
    ensures
        tf.wf(),
        tf.mapping_wf(),
{
    lemma_split_full_tree(t0, tf, idx);
    lemma_split_full_mapping(t0, tf, idx);
}

// =====================================================================
// Join: a subtree view merges back into a full table (reverse of split)
// =====================================================================

/// A subtree view (`sub_idx` Some) has no node at the top paging level: its root
/// sits at `ROOT_LEVEL-1` and every other node has a parent one level higher,
/// capped at `ROOT_LEVEL`.
pub proof fn lemma_subtree_no_root_level<V: PtPage>(t: PageTablePerms<V>, n: PFN)
    requires
        t.store_wf(),
        t.tree_inv(),
        t.sub_idx() is Some,
        t.contains(n),
    ensures
        t.level(n) != ROOT_LEVEL,
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    let r = t.root();
    if t.level(n) == ROOT_LEVEL {
        assert(t.level(r) == t.root_level() && t.root_level() == (ROOT_LEVEL - 1) as nat);
        assert(n != r);
        assert(t.tree_wf());
        let (p, k): (PFN, nat) = choose|p: PFN, k: nat|
            #![trigger t.interior_at(p, k)]
            t.interior_at(p, k) && t.entry(p, k).target == n;
        assert(t.interior_at(p, k) && t.entry(p, k).target == n);
        assert(t.node_wf(p));
        assert(!t.is_self_map(p, k));  // sub_idx Some
        assert(t.level(p) == t.level(n) + 1);  // > ROOT_LEVEL, contradicting the bound
        assert(false);
    }
}

/// Every node of a subtree view checked out at top-level entry `idx` has its base in
/// entry `idx`'s window (the reverse of the split closure: the view is self-contained
/// in its bucket). Proven by induction up to the subtree root, whose base is
/// `idx*span(ROOT_LEVEL)`.
pub proof fn lemma_subtree_nodes_in_window<V: PtPage>(t: PageTablePerms<V>, idx: nat, n: PFN)
    requires
        t.store_wf(),
        t.tree_inv(),
        t.sub_idx() == Some::<nat>(idx),
        t.xlate_base_consistent(),
        t.xlate_base_aligned(),
        t.contains(n),
    ensures
        idx * span(ROOT_LEVEL) <= t.xlate_base(n) < (idx + 1) * span(ROOT_LEVEL),
    decreases ROOT_LEVEL - t.level(n),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    let r = t.root();
    let big = span(ROOT_LEVEL);
    lemma_span_pos(ROOT_LEVEL);
    lemma_subtree_no_root_level(t, n);
    assert(t.level(n) <= ROOT_LEVEL && t.level(n) != ROOT_LEVEL);
    if t.level(n) >= t.root_level() {
        // top of the subtree: the root, based at idx*big.
        assert(t.level(n) == t.root_level());
        assert(n == r);  // root-unique
        assert(t.xlate_base(r) == t.root_base() && t.root_base() == idx * big);  // consistent
        assert(idx * big <= idx * big < (idx + 1) * big) by (nonlinear_arith)
            requires
                big > 0,
        ;
    } else {
        // below the top: walk up to the (already in-window) parent, whose link keeps
        // this node in the same window.
        assert(n != r);
        assert(t.tree_wf());
        let (p, k): (PFN, nat) = choose|p: PFN, k: nat|
            #![trigger t.interior_at(p, k)]
            t.interior_at(p, k) && t.entry(p, k).target == n;
        assert(t.interior_at(p, k) && t.entry(p, k).target == n);
        assert(t.node_wf(p));
        assert(!t.is_self_map(p, k));  // sub_idx Some
        assert(t.level(p) == t.level(n) + 1);
        assert(t.level(p) <= ROOT_LEVEL);
        lemma_subtree_no_root_level(t, p);
        assert(t.level(p) < ROOT_LEVEL);
        lemma_subtree_nodes_in_window(t, idx, p);  // IH: base(p) in idx's window
        lemma_edge_in_bucket(t, p, k, idx);  // base(n) in idx's window
    }
}

/// In a full table, a non-root node whose base is in entry `idx`'s window forces
/// `root[idx]` to be a present interior link (the node's ancestor chain enters the
/// window through it). Contrapositive: if `root[idx]` is absent, the window is empty.
pub proof fn lemma_window_implies_root_link<V: PtPage>(t: PageTablePerms<V>, idx: nat, n: PFN)
    requires
        t.store_wf(),
        t.tree_inv(),
        t.sub_idx() is None,
        t.xlate_base_consistent(),
        t.xlate_base_aligned(),
        idx < ENTRIES,
        t.contains(n),
        n != t.root(),
        idx * span(ROOT_LEVEL) <= t.xlate_base(n) < (idx + 1) * span(ROOT_LEVEL),
    ensures
        t.interior_at(t.root(), idx),
    decreases ROOT_LEVEL - t.level(n),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    let r = t.root();
    let big = span(ROOT_LEVEL);
    lemma_span_pos(ROOT_LEVEL);
    assert(t.level(r) == ROOT_LEVEL);  // tree_inv + full table
    assert(t.tree_wf());
    // n != root has a parent (p, k).
    let (p, k): (PFN, nat) = choose|p: PFN, k: nat|
        #![trigger t.interior_at(p, k)]
        t.interior_at(p, k) && t.entry(p, k).target == n;
    assert(t.interior_at(p, k) && t.entry(p, k).target == n);
    assert(t.node_wf(p));
    assert(!t.is_self_map(p, k)) by {
        if t.is_self_map(p, k) {
            assert(t.entry(p, k).target == p);  // self-map targets itself => p == n, levels clash
        }
    }
    assert(t.level(p) == t.level(n) + 1 && t.level(p) <= ROOT_LEVEL);
    if p == r {
        // base(n) == k*big lands in idx's window, so k == idx.
        assert(t.xlate_base(n) == t.entry_vpn_base(r, k) && t.xlate_base(r) == 0);
        assert(t.entry_vpn_base(r, k) == k * big);
        assert(k * big <= t.xlate_base(n) < (k + 1) * big) by (nonlinear_arith)
            requires
                big > 0,
                t.xlate_base(n) == k * big,
        ;
        lemma_windows_disjoint(t.xlate_base(n) as int, k, idx);  // k == idx
    } else {
        // p is also in idx's window (its link keeps n there), and is closer to the root.
        assert(t.level(p) < ROOT_LEVEL);  // p != root, root-unique
        let wp = lemma_base_has_window(t.xlate_base(p));
        lemma_edge_in_bucket(t, p, k, wp);  // base(n) in wp's window
        lemma_windows_disjoint(t.xlate_base(n) as int, wp, idx);  // wp == idx
        lemma_window_implies_root_link(t, idx, p);
    }
}

/// `tj` is the full table obtained by merging subtree view `ps` back under entry
/// `idx` of full remainder `pf`: re-link `root[idx] -> ps.root()`, take the union of
/// the node stores and `va_map`s. The two stores are disjoint and `pf[idx]` is free.
pub open spec fn is_join<V: PtPage>(
    pf: PageTablePerms<V>,
    ps: PageTablePerms<V>,
    tj: PageTablePerms<V>,
    idx: nat,
) -> bool {
    &&& tj.root() == pf.root()
    &&& tj.sub_idx() is None
    &&& (forall|n: PFN| #[trigger]
        tj.contains(n) <==> (pf.contains(n) || ps.contains(n)))
    &&& tj.node(pf.root()) == pf.node(pf.root()).update(idx, interior_entry(ps.root()))
    &&& (forall|n: PFN| #[trigger] tj.contains(n) && ps.contains(n) ==> {
        &&& tj.node(n) == ps.node(n)
        &&& tj.level(n) == ps.level(n)
        &&& tj.xlate_base(n) == ps.xlate_base(n)
    })
    &&& (forall|n: PFN| #[trigger] tj.contains(n) && !ps.contains(n) ==> {
        &&& (n != pf.root() ==> tj.node(n) == pf.node(n))
        &&& tj.level(n) == pf.level(n)
        &&& tj.xlate_base(n) == pf.xlate_base(n)
    })
    &&& (forall|b: VPage| #[trigger]
        tj.va_map().dom().contains(b) <==> (pf.va_map().dom().contains(b)
            || ps.va_map().dom().contains(b)))
    &&& (forall|b: VPage| #[trigger] tj.va_map().dom().contains(b) ==> {
        &&& (ps.va_map().dom().contains(b) ==> tj.va_map()[b] == ps.va_map()[b])
        &&& (!ps.va_map().dom().contains(b) ==> tj.va_map()[b] == pf.va_map()[b])
    })
}

/// Entry/level bridge for the join: on a `ps` node `tj` reads like `ps`; on a non-root
/// `pf`-only node like `pf`; at the root it is `pf`'s row with `idx` re-linked to `c`.
proof fn lemma_join_bridge<V: PtPage>(
    pf: PageTablePerms<V>,
    ps: PageTablePerms<V>,
    tj: PageTablePerms<V>,
    idx: nat,
)
    requires
        pf.store_wf(),
        ps.store_wf(),
        idx < ENTRIES,
        pf.pages().dom().disjoint(ps.pages().dom()),
        is_join(pf, ps, tj, idx),
    ensures
        forall|n: PFN, i: nat| #![trigger ps.interior_at(n, i)] #![trigger tj.entry(n, i)]
            ps.contains(n) ==> {
                &&& tj.interior_at(n, i) == ps.interior_at(n, i)
                &&& tj.leaf_at(n, i) == ps.leaf_at(n, i)
                &&& tj.entry(n, i) == ps.entry(n, i)
            },
        forall|n: PFN, i: nat| #![trigger pf.interior_at(n, i)] #![trigger tj.entry(n, i)]
            (pf.contains(n) && n != pf.root()) ==> {
                &&& tj.interior_at(n, i) == pf.interior_at(n, i)
                &&& tj.leaf_at(n, i) == pf.leaf_at(n, i)
                &&& tj.entry(n, i) == pf.entry(n, i)
            },
        forall|i: nat| #![trigger tj.entry(pf.root(), i)]
            (i != idx ==> tj.entry(pf.root(), i) == pf.entry(pf.root(), i)) && (i == idx
                ==> tj.entry(pf.root(), i) == interior_entry(ps.root())),
{
    broadcast use lemma_node_struct_wf;

    let r = pf.root();
    assert(pf.node(r).e.dom().contains(idx));
    assert forall|n: PFN, i: nat| #![trigger ps.interior_at(n, i)]
        ps.contains(n) implies {
            &&& tj.interior_at(n, i) == ps.interior_at(n, i)
            &&& tj.leaf_at(n, i) == ps.leaf_at(n, i)
            &&& tj.entry(n, i) == ps.entry(n, i)
        } by {
        assert(tj.contains(n) && !pf.contains(n));  // disjoint
        assert(tj.node(n) == ps.node(n) && tj.level(n) == ps.level(n));
        assert(tj.entry(n, i) == ps.entry(n, i));
        assert(tj.interior_at(n, i) == ps.interior_at(n, i));
        assert(tj.leaf_at(n, i) == ps.leaf_at(n, i));
    }
    assert forall|n: PFN, i: nat| #![trigger pf.interior_at(n, i)]
        (pf.contains(n) && n != r) implies {
            &&& tj.interior_at(n, i) == pf.interior_at(n, i)
            &&& tj.leaf_at(n, i) == pf.leaf_at(n, i)
            &&& tj.entry(n, i) == pf.entry(n, i)
        } by {
        assert(tj.contains(n) && !ps.contains(n));  // disjoint
        assert(tj.node(n) == pf.node(n) && tj.level(n) == pf.level(n));
        assert(tj.entry(n, i) == pf.entry(n, i));
        assert(tj.interior_at(n, i) == pf.interior_at(n, i));
        assert(tj.leaf_at(n, i) == pf.leaf_at(n, i));
    }
    assert forall|i: nat| #![trigger tj.entry(r, i)]
        (i != idx ==> tj.entry(r, i) == pf.entry(r, i)) && (i == idx ==> tj.entry(r, i)
            == interior_entry(ps.root())) by {
        assert(tj.node(r) == pf.node(r).update(idx, interior_entry(ps.root())));
        assert(tj.entry(r, i) == tj.node(r).e[i]);
        assert(tj.node(r).e[i] == pf.node(r).e.insert(idx, interior_entry(ps.root()))[i]);
        assert(pf.entry(r, i) == pf.node(r).e[i]);
    }
}

/// `node_wf` of a `ps` node survives the join (its links stay inside `ps`, hence live).
proof fn lemma_join_node_wf_ps<V: PtPage>(
    pf: PageTablePerms<V>,
    ps: PageTablePerms<V>,
    tj: PageTablePerms<V>,
    idx: nat,
    n: PFN,
)
    requires
        pf.store_wf(),
        ps.store_wf(),
        ps.wf(),
        ps.sub_idx() == Some::<nat>(idx),
        idx < ENTRIES,
        pf.pages().dom().disjoint(ps.pages().dom()),
        is_join(pf, ps, tj, idx),
        ps.contains(n),
    ensures
        tj.node_wf(n),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    lemma_join_bridge(pf, ps, tj, idx);
    assert(ps.node_wf(n));  // ps.links_wf
    lemma_subtree_no_root_level(ps, n);
    assert forall|i: nat|
        #![trigger tj.entry(n, i)]
        (i < ENTRIES && tj.node(n).e.dom().contains(i) && tj.entry(n, i).present) implies {
            let e = tj.entry(n, i);
            if tj.level(n) == 0 || e.leaf {
                &&& tj.level(n) <= 2
                &&& e.target % span(tj.level(n)) == 0
            } else {
                &&& tj.contains(e.target)
                &&& if tj.is_self_map(n, i) {
                    e.target == n
                } else {
                    tj.level(n) >= 1 && tj.level(e.target) == tj.level(n) - 1
                }
            }
        } by {
        assert(tj.contains(n) && tj.level(n) == ps.level(n));  // is_join level
        assert(tj.entry(n, i) == ps.entry(n, i));  // bridge
        assert(!tj.is_self_map(n, i));  // tj.sub_idx None but ps node level < ROOT_LEVEL
        if tj.level(n) != 0 && !tj.entry(n, i).leaf {
            assert(ps.interior_at(n, i));
            assert(ps.contains(ps.entry(n, i).target));  // ps.node_wf
            assert(tj.contains(ps.entry(n, i).target));  // union
        }
    }
}

/// `node_wf` of a `pf` node survives the join; at the root the re-linked slot points
/// one level down to `c`, the rest is `pf`'s unchanged row.
proof fn lemma_join_node_wf_pf<V: PtPage>(
    pf: PageTablePerms<V>,
    ps: PageTablePerms<V>,
    tj: PageTablePerms<V>,
    idx: nat,
    n: PFN,
)
    requires
        pf.store_wf(),
        pf.wf(),
        ps.store_wf(),
        ps.wf(),
        ps.sub_idx() == Some::<nat>(idx),
        pf.sub_idx() is None,
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        !pf.entry(pf.root(), idx).present,
        pf.pages().dom().disjoint(ps.pages().dom()),
        is_join(pf, ps, tj, idx),
        tj.contains(n),
        !ps.contains(n),
    ensures
        tj.node_wf(n),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    lemma_join_bridge(pf, ps, tj, idx);
    let r = pf.root();
    let c = ps.root();
    assert(pf.contains(n) && pf.node_wf(n));  // n in union, not in ps
    assert(pf.level(r) == ROOT_LEVEL);
    assert(ps.contains(c) && ps.level(c) == (ROOT_LEVEL - 1) as nat);
    assert forall|i: nat|
        #![trigger tj.entry(n, i)]
        (i < ENTRIES && tj.node(n).e.dom().contains(i) && tj.entry(n, i).present) implies {
            let e = tj.entry(n, i);
            if tj.level(n) == 0 || e.leaf {
                &&& tj.level(n) <= 2
                &&& e.target % span(tj.level(n)) == 0
            } else {
                &&& tj.contains(e.target)
                &&& if tj.is_self_map(n, i) {
                    e.target == n
                } else {
                    tj.level(n) >= 1 && tj.level(e.target) == tj.level(n) - 1
                }
            }
        } by {
        assert(tj.contains(n) && !ps.contains(n) && tj.level(n) == pf.level(n));  // is_join level
        if n == r && i == idx {
            // the re-linked slot: interior to c, one level down, not the self-map.
            assert(tj.entry(r, idx) == interior_entry(c));  // bridge root row
            assert(tj.level(r) == ROOT_LEVEL);
            assert(tj.contains(c) && tj.level(c) == ps.level(c));  // is_join, c in ps
            assert(tj.level(c) == (ROOT_LEVEL - 1) as nat);
            assert(!tj.is_self_map(r, idx));  // idx != IDX_SELFMAP
        } else {
            assert(tj.entry(n, i) == pf.entry(n, i));  // bridge (n != r or i != idx)
            assert(tj.is_self_map(n, i) == pf.is_self_map(n, i));
            if pf.interior_at(n, i) {
                assert(pf.contains(pf.entry(n, i).target));  // pf.node_wf
                assert(tj.contains(pf.entry(n, i).target));  // union
                if pf.is_self_map(n, i) {
                    assert(pf.entry(n, i).target == n);
                }
            }
        }
    }
}

/// Injectivity survives the join: `pf` links target `pf` nodes, `ps` links target `ps`
/// nodes (the disjoint stores), and the one new link `root[idx] -> c` is `c`'s only
/// parent (a subtree root has no incoming edge).
proof fn lemma_join_injective<V: PtPage>(
    pf: PageTablePerms<V>,
    ps: PageTablePerms<V>,
    tj: PageTablePerms<V>,
    idx: nat,
    n1: PFN,
    i1: nat,
    n2: PFN,
    i2: nat,
)
    requires
        pf.store_wf(),
        pf.wf(),
        ps.store_wf(),
        ps.wf(),
        ps.sub_idx() == Some::<nat>(idx),
        pf.sub_idx() is None,
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        !pf.entry(pf.root(), idx).present,
        pf.pages().dom().disjoint(ps.pages().dom()),
        is_join(pf, ps, tj, idx),
        tj.interior_at(n1, i1),
        tj.interior_at(n2, i2),
        tj.entry(n1, i1).target == tj.entry(n2, i2).target,
    ensures
        n1 == n2 && i1 == i2,
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    lemma_join_bridge(pf, ps, tj, idx);
    let r = pf.root();
    let c = ps.root();
    assert(ps.contains(c));
    // classify each interior: a ps link (target in ps), the new root[idx] link
    // (target c), or a pf link off root[idx] (target in pf, disjoint from ps).
    lemma_join_edge_class(pf, ps, tj, idx, n1, i1);
    lemma_join_edge_class(pf, ps, tj, idx, n2, i2);
    let new1 = n1 == r && i1 == idx;
    let new2 = n2 == r && i2 == idx;
    if new1 && new2 {
        // both are the unique new link.
    } else if new1 || new2 {
        // exactly one is the new link (target c); the other targets c too, but no
        // edge other than root[idx] reaches c (ps root has no parent; pf has no c).
        let (m, j): (PFN, nat) = if new1 { (n2, i2) } else { (n1, i1) };
        assert(tj.entry(m, j).target == c);
        if ps.contains(m) {
            assert(ps.interior_at(m, j) && ps.entry(m, j).target == c);
            lemma_root_incoming_is_self_map(ps, m, j);  // => is_self_map, impossible in subtree
        } else {
            assert(pf.contains(tj.entry(m, j).target));  // pf edge class
            assert(pf.contains(c) && ps.contains(c));  // disjoint stores: contradiction
        }
    } else {
        // neither is the new link: both are ps edges, both pf edges, or a mixed pair
        // whose common target would have to live in both disjoint stores.
        if ps.contains(n1) && ps.contains(n2) {
            assert(ps.interior_at(n1, i1) && ps.interior_at(n2, i2));  // bridge
            assert(ps.entry(n1, i1).target == ps.entry(n2, i2).target);
            assert(ps.tree_wf());  // injectivity
        } else if !ps.contains(n1) && !ps.contains(n2) {
            assert(pf.interior_at(n1, i1) && pf.interior_at(n2, i2));  // bridge
            assert(pf.entry(n1, i1).target == pf.entry(n2, i2).target);
            assert(pf.tree_wf());  // injectivity
        } else {
            // mixed: the shared target sits in both ps and pf - impossible (disjoint).
            if ps.contains(n1) {
                assert(ps.contains(tj.entry(n1, i1).target));  // edge class, ps side
                assert(pf.contains(tj.entry(n2, i2).target));  // edge class, pf side
            } else {
                assert(pf.contains(tj.entry(n1, i1).target));
                assert(ps.contains(tj.entry(n2, i2).target));
            }
        }
    }
}

/// Each `tj` interior edge is either a `ps` edge (live `ps` target), the new
/// `root[idx]` edge (target `c`), or a `pf` edge off `root[idx]` (live `pf` target).
proof fn lemma_join_edge_class<V: PtPage>(
    pf: PageTablePerms<V>,
    ps: PageTablePerms<V>,
    tj: PageTablePerms<V>,
    idx: nat,
    n: PFN,
    i: nat,
)
    requires
        pf.store_wf(),
        pf.wf(),
        ps.store_wf(),
        ps.wf(),
        ps.sub_idx() == Some::<nat>(idx),
        idx < ENTRIES,
        !pf.entry(pf.root(), idx).present,
        pf.pages().dom().disjoint(ps.pages().dom()),
        is_join(pf, ps, tj, idx),
        tj.interior_at(n, i),
    ensures
        (n == pf.root() && i == idx && tj.entry(n, i).target == ps.root()) || (ps.contains(n)
            && ps.contains(tj.entry(n, i).target)) || (pf.contains(n) && !ps.contains(n) && (n
            != pf.root() || i != idx) && pf.contains(tj.entry(n, i).target)),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    lemma_join_bridge(pf, ps, tj, idx);
    let r = pf.root();
    assert(tj.contains(n));
    if ps.contains(n) {
        assert(ps.interior_at(n, i));
        assert(ps.node_wf(n) && ps.contains(ps.entry(n, i).target));
    } else if n == r && i == idx {
        assert(tj.entry(r, idx) == interior_entry(ps.root()));
    } else {
        assert(pf.contains(n) && pf.interior_at(n, i));  // off the re-linked slot
        assert(pf.node_wf(n) && pf.contains(pf.entry(n, i).target));
    }
}

/// Connectivity survives the join: `pf` nodes keep their `pf` parents (the root row
/// off `idx` is unchanged), `c` is parented by the new `root[idx]` link, and the
/// other `ps` nodes keep their `ps` parents.
proof fn lemma_join_connected<V: PtPage>(
    pf: PageTablePerms<V>,
    ps: PageTablePerms<V>,
    tj: PageTablePerms<V>,
    idx: nat,
    x: PFN,
)
    requires
        pf.store_wf(),
        pf.wf(),
        ps.store_wf(),
        ps.wf(),
        ps.sub_idx() == Some::<nat>(idx),
        pf.sub_idx() is None,
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        !pf.entry(pf.root(), idx).present,
        pf.pages().dom().disjoint(ps.pages().dom()),
        is_join(pf, ps, tj, idx),
        tj.contains(x),
        x != pf.root(),
    ensures
        exists|p: PFN, k: nat| #[trigger] tj.interior_at(p, k) && tj.entry(p, k).target == x,
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    lemma_join_bridge(pf, ps, tj, idx);
    let r = pf.root();
    let c = ps.root();
    assert(tj.contains(r) && !ps.contains(r));  // r in pf, disjoint stores
    assert(tj.level(r) == pf.level(r) && pf.level(r) == ROOT_LEVEL);  // is_join
    if ps.contains(x) {
        if x == c {
            assert(tj.entry(r, idx) == interior_entry(c));  // bridge root row
            assert(tj.interior_at(r, idx) && tj.entry(r, idx).target == c);
        } else {
            assert(ps.tree_wf());
            let (p, k): (PFN, nat) = choose|p: PFN, k: nat|
                #![trigger ps.interior_at(p, k)]
                ps.interior_at(p, k) && ps.entry(p, k).target == x;
            assert(ps.interior_at(p, k) && ps.entry(p, k).target == x);
            assert(tj.interior_at(p, k) && tj.entry(p, k).target == x);
        }
    } else {
        assert(pf.contains(x) && pf.tree_wf());
        let (p, k): (PFN, nat) = choose|p: PFN, k: nat|
            #![trigger pf.interior_at(p, k)]
            pf.interior_at(p, k) && pf.entry(p, k).target == x;
        assert(pf.interior_at(p, k) && pf.entry(p, k).target == x);
        // (p, k) != (root, idx): that slot is absent in pf, hence not an interior.
        assert(p != r || k != idx);
        if p == r {
            assert(tj.entry(r, k) == pf.entry(r, k));  // bridge root row, k != idx
            assert(tj.interior_at(r, k));  // pf interior + equal entry/level
        } else {
            assert(tj.interior_at(p, k) == pf.interior_at(p, k));  // bridge pf node
        }
        assert(tj.interior_at(p, k) && tj.entry(p, k).target == x);
    }
}

/// The merged table `tj` is a valid tree.
#[verifier::rlimit(100)]
pub proof fn lemma_join_tree<V: PtPage>(
    pf: PageTablePerms<V>,
    ps: PageTablePerms<V>,
    tj: PageTablePerms<V>,
    idx: nat,
)
    requires
        pf.store_wf(),
        pf.wf(),
        pf.mapping_wf(),
        pf.sub_idx() is None,
        ps.store_wf(),
        ps.wf(),
        ps.mapping_wf(),
        ps.sub_idx() == Some::<nat>(idx),
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        !pf.entry(pf.root(), idx).present,
        pf.pages().dom().disjoint(ps.pages().dom()),
        tj.store_wf(),
        is_join(pf, ps, tj, idx),
    ensures
        tj.tree_inv(),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    lemma_join_bridge(pf, ps, tj, idx);
    let r = pf.root();
    let c = ps.root();
    assert(pf.level(r) == ROOT_LEVEL && tj.contains(r));
    assert(ps.contains(c) && ps.level(c) == (ROOT_LEVEL - 1) as nat);  // ps.tree_inv
    assert(tj.contains(c) && tj.level(c) == ps.level(c));  // is_join, c in ps
    assert(tj.level(c) == (ROOT_LEVEL - 1) as nat);
    assert(!ps.contains(r));  // r in pf, disjoint
    assert(tj.level(r) == pf.level(r) && tj.root_level() == ROOT_LEVEL);  // is_join
    assert(!pf.interior_at(r, idx));  // slot absent
    assert(tj.entry(r, idx) == interior_entry(c));
    assert(tj.interior_at(r, idx) && tj.entry(r, idx).target == c);
    assert(!tj.is_self_map(r, idx));  // idx != IDX_SELFMAP

    assert(tj.links_wf()) by {
        assert forall|n: PFN| tj.contains(n) implies #[trigger] tj.node_wf(n) by {
            if ps.contains(n) {
                lemma_join_node_wf_ps(pf, ps, tj, idx, n);
            } else {
                lemma_join_node_wf_pf(pf, ps, tj, idx, n);
            }
        }
    }

    assert(tj.tree_wf()) by {
        assert forall|n: PFN| #![trigger tj.contains(n)]
            tj.contains(n) && tj.level(n) == tj.root_level() implies n == r by {
            if ps.contains(n) {
                lemma_subtree_no_root_level(ps, n);
                assert(tj.level(n) == ps.level(n));
            } else {
                assert(pf.contains(n) && tj.level(n) == pf.level(n));
            }
        }
        assert(tj.self_map_inv()) by {
            assert(pf.interior_at(r, IDX_SELFMAP) && pf.entry(r, IDX_SELFMAP).target == r);
            assert(IDX_SELFMAP != idx);
            assert(tj.entry(r, IDX_SELFMAP) == pf.entry(r, IDX_SELFMAP));
            assert(tj.interior_at(r, IDX_SELFMAP));
        }
        assert forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
            (#[trigger] tj.interior_at(n1, i1) && #[trigger] tj.interior_at(n2, i2) && tj.entry(
                n1,
                i1,
            ).target == tj.entry(n2, i2).target) implies (n1 == n2 && i1 == i2) by {
            lemma_join_injective(pf, ps, tj, idx, n1, i1, n2, i2);
        }
        assert forall|x: PFN| #![trigger tj.contains(x)]
            (tj.contains(x) && x != r) implies exists|p: PFN, k: nat|
            #[trigger] tj.interior_at(p, k) && tj.entry(p, k).target == x by {
            lemma_join_connected(pf, ps, tj, idx, x);
        }
    }

    assert(tj.ad_pinned()) by {
        assert forall|n: PFN, i: nat|
            (tj.contains(n) && i < ENTRIES && tj.node(n).e.dom().contains(i)) implies entry_pinned(
                #[trigger] tj.entry(n, i),
            ) by {
            if ps.contains(n) {
                assert(tj.entry(n, i) == ps.entry(n, i));
            } else if n == r && i == idx {
                assert(tj.entry(r, idx) == interior_entry(c));  // pinned by construction
            } else {
                assert(pf.contains(n) && tj.entry(n, i) == pf.entry(n, i));
            }
        }
    }
}

/// A subtree view's `va_map` key (and its whole mapping range) lies in entry `idx`'s
/// window: the recording leaf is in the subtree, hence in the window.
pub proof fn lemma_ps_key_in_window<V: PtPage>(ps: PageTablePerms<V>, idx: nat, b: VPage)
    requires
        ps.store_wf(),
        ps.tree_inv(),
        ps.sub_idx() == Some::<nat>(idx),
        ps.xlate_base_consistent(),
        ps.xlate_base_aligned(),
        ps.mapping_inv(),
        ps.va_map().dom().contains(b),
    ensures
        idx * span(ROOT_LEVEL) <= b,
        b + ps.va_map()[b].size.pages() <= (idx + 1) * span(ROOT_LEVEL),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    let big = span(ROOT_LEVEL);
    let m = ps.va_map()[b];
    let ii = pt_index(b, level_of_size(m.size));
    let n = choose|n: PFN| ps.records_leaf(b, m, n, ii);  // mapping_inv (Q)
    assert(ps.records_leaf(b, m, n, ii));
    let l = ps.level(n);
    assert(l == level_of_size(m.size) && level_of_size(m.size) <= 2 && l < ROOT_LEVEL);
    lemma_subtree_nodes_in_window(ps, idx, n);  // base(n) in idx's window
    lemma_node_window_in_bucket(ps, n, idx);  // base(n) + span(l+1) <= (idx+1)*big
    lemma_size_level_roundtrip(l);  // span(l) == m.size.pages()
    lemma_span_pos(l);
    assert(span((l + 1) as nat) == 512 * span(l));
    assert(ii < ENTRIES);  // pt_index
    assert(b == ps.xlate_base(n) + ii * span(l));  // records_leaf: entry_vpn_base
    assert(idx * big <= b) by (nonlinear_arith)
        requires
            idx * big <= ps.xlate_base(n),
            b == ps.xlate_base(n) + ii * span(l),
            ii * span(l) >= 0,
            span(l) >= 0,
            ii >= 0,
    ;
    assert(b + m.size.pages() <= (idx + 1) * big) by (nonlinear_arith)
        requires
            b == ps.xlate_base(n) + ii * span(l),
            m.size.pages() == span(l),
            span((l + 1) as nat) == 512 * span(l),
            ps.xlate_base(n) + span((l + 1) as nat) <= (idx + 1) * big,
            ii + 1 <= 512,
            span(l) >= 0,
    ;
}

/// A full table with `root[idx]` absent has no `va_map` key in entry `idx`'s window:
/// any recording leaf would force the slot to be present.
pub proof fn lemma_pf_key_not_in_window<V: PtPage>(pf: PageTablePerms<V>, idx: nat, b: VPage)
    requires
        pf.store_wf(),
        pf.tree_inv(),
        pf.sub_idx() is None,
        pf.xlate_base_consistent(),
        pf.xlate_base_aligned(),
        pf.mapping_inv(),
        idx < ENTRIES,
        !pf.entry(pf.root(), idx).present,
        pf.va_map().dom().contains(b),
    ensures
        b + pf.va_map()[b].size.pages() <= idx * span(ROOT_LEVEL) || (idx + 1) * span(ROOT_LEVEL)
            <= b,
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    let big = span(ROOT_LEVEL);
    lemma_span_pos(ROOT_LEVEL);
    let m = pf.va_map()[b];
    let ii = pt_index(b, level_of_size(m.size));
    let n = choose|n: PFN| pf.records_leaf(b, m, n, ii);  // mapping_inv (Q)
    assert(pf.records_leaf(b, m, n, ii));
    let l = pf.level(n);
    assert(l == level_of_size(m.size) && level_of_size(m.size) <= 2 && l < ROOT_LEVEL);
    assert(pf.contains(n) && n != pf.root());  // a leaf node is below the root
    let w = lemma_base_has_window(pf.xlate_base(n));
    assert(!pf.interior_at(pf.root(), idx));  // slot absent
    assert(w != idx) by {
        if w == idx {
            lemma_window_implies_root_link(pf, idx, n);  // => interior_at(root, idx), absurd
        }
    }
    lemma_node_window_in_bucket(pf, n, w);  // base(n) + span(l+1) <= (w+1)*big
    lemma_size_level_roundtrip(l);
    lemma_span_pos(l);
    assert(span((l + 1) as nat) == 512 * span(l));
    assert(ii < ENTRIES);
    assert(b == pf.xlate_base(n) + ii * span(l));
    // the whole mapping range sits in w's window, which is not idx's.
    assert(w * big <= b) by (nonlinear_arith)
        requires
            w * big <= pf.xlate_base(n),
            b == pf.xlate_base(n) + ii * span(l),
            ii * span(l) >= 0,
    ;
    assert(b + m.size.pages() <= (w + 1) * big) by (nonlinear_arith)
        requires
            b == pf.xlate_base(n) + ii * span(l),
            m.size.pages() == span(l),
            span((l + 1) as nat) == 512 * span(l),
            pf.xlate_base(n) + span((l + 1) as nat) <= (w + 1) * big,
            ii + 1 <= 512,
            span(l) >= 0,
    ;
    if w < idx {
        assert((w + 1) * big <= idx * big) by (nonlinear_arith)
            requires
                w + 1 <= idx,
                big >= 0,
        ;
    } else {
        assert((idx + 1) * big <= w * big) by (nonlinear_arith)
            requires
                idx + 1 <= w,
                big >= 0,
        ;
    }
}

/// The merged table `tj` carries the user-mapping invariant `mapping_wf`. The only
/// cross-half obligation that is not geometric - frame disjointness between the two
/// halves' mappings - is a hypothesis (the caller must not have re-used data frames).
#[verifier::rlimit(100)]
pub proof fn lemma_join_mapping<V: PtPage>(
    pf: PageTablePerms<V>,
    ps: PageTablePerms<V>,
    tj: PageTablePerms<V>,
    idx: nat,
)
    requires
        pf.store_wf(),
        pf.wf(),
        pf.mapping_wf(),
        pf.sub_idx() is None,
        ps.store_wf(),
        ps.wf(),
        ps.mapping_wf(),
        ps.sub_idx() == Some::<nat>(idx),
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        !pf.entry(pf.root(), idx).present,
        pf.pages().dom().disjoint(ps.pages().dom()),
        tj.store_wf(),
        tj.tree_inv(),
        is_join(pf, ps, tj, idx),
        // data frames of the two halves' mappings are disjoint (the part split/map
        // does not guarantee on its own).
        forall|b1: VPage, b2: VPage|
            (#[trigger] pf.va_map().dom().contains(b1) && #[trigger] ps.va_map().dom().contains(b2))
                ==> {
                let f1 = pf.va_map()[b1].frame;
                let f2 = ps.va_map()[b2].frame;
                f1 + pf.va_map()[b1].size.pages() <= f2 || f2 + ps.va_map()[b2].size.pages() <= f1
            },
    ensures
        tj.mapping_wf(),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    lemma_join_bridge(pf, ps, tj, idx);
    let r = pf.root();
    let c = ps.root();
    let big = span(ROOT_LEVEL);
    lemma_span_pos(ROOT_LEVEL);
    assert(pf.level(r) == ROOT_LEVEL && !ps.contains(r) && tj.level(r) == ROOT_LEVEL);
    assert(ps.contains(c) && ps.level(c) == (ROOT_LEVEL - 1) as nat);
    assert(tj.contains(c) && tj.level(c) == ps.level(c));
    assert(ps.xlate_base(c) == ps.root_base() && ps.root_base() == idx * big);  // ps consistent
    assert(tj.xlate_base(c) == ps.xlate_base(c));  // is_join
    assert(tj.xlate_base(r) == pf.xlate_base(r) && pf.xlate_base(r) == 0);  // pf consistent

    // permissive interiors: pf side, the new permissive link, ps side.
    assert(tj.interiors_permissive()) by {
        assert forall|n: PFN, i: nat| #[trigger] tj.interior_at(n, i) implies permissive(
            tj.entry(n, i),
        ) by {
            lemma_join_edge_class(pf, ps, tj, idx, n, i);
            if ps.contains(n) {
                assert(ps.interior_at(n, i) && tj.entry(n, i) == ps.entry(n, i));
            } else if n == r && i == idx {
                assert(tj.entry(r, idx) == interior_entry(c));  // permissive by construction
            } else {
                assert(pf.interior_at(n, i) && tj.entry(n, i) == pf.entry(n, i));
            }
        }
    }
    // xlate_base_consistent.
    assert(tj.xlate_base_consistent()) by {
        assert(tj.xlate_base(tj.root()) == tj.root_base());  // both 0
        assert forall|p: PFN, i: nat| (#[trigger] tj.interior_at(p, i) && !tj.is_self_map(p, i))
            implies tj.xlate_base(tj.entry(p, i).target) == tj.entry_vpn_base(p, i) by {
            lemma_join_edge_class(pf, ps, tj, idx, p, i);
            if ps.contains(p) {
                let tgt = ps.entry(p, i).target;
                assert(ps.interior_at(p, i) && tj.entry(p, i) == ps.entry(p, i));
                assert(!ps.is_self_map(p, i));  // ps subtree
                assert(ps.contains(tgt) && tj.contains(tgt));
                assert(tj.xlate_base(tgt) == ps.xlate_base(tgt));  // is_join, tgt in ps
                assert(tj.level(p) == ps.level(p) && tj.xlate_base(p) == ps.xlate_base(p));
            } else if p == r && i == idx {
                assert(tj.entry(r, idx).target == c);
                assert(tj.xlate_base(c) == idx * big);
                assert(tj.entry_vpn_base(r, idx) == tj.xlate_base(r) + idx * span(tj.level(r)));
                assert(tj.entry_vpn_base(r, idx) == idx * big);
            } else {
                let tgt = pf.entry(p, i).target;
                assert(pf.interior_at(p, i) && tj.entry(p, i) == pf.entry(p, i));
                assert(tj.is_self_map(p, i) == pf.is_self_map(p, i));
                assert(!pf.is_self_map(p, i));
                assert(pf.contains(tgt) && tj.contains(tgt));
                assert(tj.xlate_base(tgt) == pf.xlate_base(tgt));  // is_join, tgt in pf
                assert(tj.level(p) == pf.level(p) && tj.xlate_base(p) == pf.xlate_base(p));
            }
        }
    }
    // xlate_base_aligned.
    assert(tj.xlate_base_aligned()) by {
        assert forall|n: PFN| #[trigger] tj.contains(n) implies tj.xlate_base(n) % span(
            (tj.level(n) + 1) as nat,
        ) == 0 by {
            if ps.contains(n) {
                assert(tj.xlate_base(n) == ps.xlate_base(n) && tj.level(n) == ps.level(n));
            } else {
                assert(pf.contains(n) && tj.xlate_base(n) == pf.xlate_base(n) && tj.level(n)
                    == pf.level(n));
            }
        }
    }

    lemma_join_mapping_inv(pf, ps, tj, idx);
}

/// The user-mapping invariant `mapping_inv` of the merged table: each half's records
/// and leaves survive; disjointness holds within each half and across (frames by
/// hypothesis, vpns because the two halves live in disjoint top-level windows).
#[verifier::rlimit(100)]
pub proof fn lemma_join_mapping_inv<V: PtPage>(
    pf: PageTablePerms<V>,
    ps: PageTablePerms<V>,
    tj: PageTablePerms<V>,
    idx: nat,
)
    requires
        pf.store_wf(),
        pf.wf(),
        pf.mapping_wf(),
        pf.sub_idx() is None,
        ps.store_wf(),
        ps.wf(),
        ps.mapping_wf(),
        ps.sub_idx() == Some::<nat>(idx),
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        !pf.entry(pf.root(), idx).present,
        pf.pages().dom().disjoint(ps.pages().dom()),
        tj.store_wf(),
        tj.tree_inv(),
        is_join(pf, ps, tj, idx),
        forall|b1: VPage, b2: VPage|
            (#[trigger] pf.va_map().dom().contains(b1) && #[trigger] ps.va_map().dom().contains(b2))
                ==> {
                let f1 = pf.va_map()[b1].frame;
                let f2 = ps.va_map()[b2].frame;
                f1 + pf.va_map()[b1].size.pages() <= f2 || f2 + ps.va_map()[b2].size.pages() <= f1
            },
    ensures
        tj.mapping_inv(),
{
    broadcast use lemma_node_level_bound, lemma_node_struct_wf;

    lemma_join_bridge(pf, ps, tj, idx);
    let r = pf.root();
    let big = span(ROOT_LEVEL);
    lemma_span_pos(ROOT_LEVEL);
    assert(tj.level(r) == ROOT_LEVEL) by {
        assert(!ps.contains(r) && tj.level(r) == pf.level(r) && pf.level(r) == ROOT_LEVEL);
    }
    // the two halves' key sets are disjoint (one in idx's window, the other not).
    assert forall|b: VPage|
        (#[trigger] pf.va_map().dom().contains(b) && #[trigger] ps.va_map().dom().contains(b))
            implies false by {
        lemma_pf_key_not_in_window(pf, idx, b);
        lemma_ps_key_in_window(ps, idx, b);
    }

    // (Q): every tj key is recorded by a surviving leaf of its own half.
    assert forall|b: VPage| #[trigger] tj.va_map().dom().contains(b) implies {
        let m = tj.va_map()[b];
        &&& in_user_region(b)
        &&& b % m.size.pages() == 0
        &&& m.frame % m.size.pages() == 0
        &&& exists|w: PFN| tj.records_leaf(b, m, w, pt_index(b, level_of_size(m.size)))
    } by {
        if ps.va_map().dom().contains(b) {
            let m = ps.va_map()[b];
            assert(tj.va_map()[b] == m);  // is_join
            let ii = pt_index(b, level_of_size(m.size));
            let w = choose|w: PFN| ps.records_leaf(b, m, w, ii);
            assert(ps.records_leaf(b, m, w, ii));
            assert(ps.contains(w) && tj.contains(w));
            assert(tj.level(w) == ps.level(w) && tj.xlate_base(w) == ps.xlate_base(w));
            assert(tj.records_leaf(b, m, w, ii));
        } else {
            assert(pf.va_map().dom().contains(b));  // union
            let m = pf.va_map()[b];
            assert(tj.va_map()[b] == m);
            let ii = pt_index(b, level_of_size(m.size));
            let w = choose|w: PFN| pf.records_leaf(b, m, w, ii);
            assert(pf.records_leaf(b, m, w, ii));
            assert(pf.contains(w) && w != r);  // a leaf is below the root
            assert(tj.contains(w));
            assert(tj.level(w) == pf.level(w) && tj.xlate_base(w) == pf.xlate_base(w));
            assert(tj.records_leaf(b, m, w, ii));
        }
    }
    // (P): every tj user-region leaf is recorded in its half.
    assert forall|n: PFN, i: nat|
        (#[trigger] tj.leaf_at(n, i) && in_user_region(tj.entry_vpn_base(n, i)))
            implies tj.va_map().dom().contains(tj.entry_vpn_base(n, i)) by {
        assert(tj.contains(n));
        assert(n != r) by {
            if n == r {
                assert(tj.node_wf(r));  // tj.tree_inv: no present leaf at ROOT_LEVEL
            }
        }
        if ps.contains(n) {
            assert(ps.leaf_at(n, i) && tj.entry_vpn_base(n, i) == ps.entry_vpn_base(n, i));
            assert(ps.va_map().dom().contains(ps.entry_vpn_base(n, i)));  // ps (P)
        } else {
            assert(pf.contains(n) && pf.leaf_at(n, i) && tj.entry_vpn_base(n, i)
                == pf.entry_vpn_base(n, i));
            assert(pf.va_map().dom().contains(pf.entry_vpn_base(n, i)));  // pf (P)
        }
    }
    // (C) frame disjointness and (D) vpn disjointness.
    assert forall|b1: VPage, b2: VPage|
        (b1 != b2 && #[trigger] tj.va_map().dom().contains(b1) && #[trigger] tj.va_map().dom().contains(
            b2,
        )) implies ({
            let f1 = tj.va_map()[b1].frame;
            let f2 = tj.va_map()[b2].frame;
            &&& (f1 + tj.va_map()[b1].size.pages() <= f2 || f2 + tj.va_map()[b2].size.pages() <= f1)
            &&& (b1 + tj.va_map()[b1].size.pages() <= b2 || b2 + tj.va_map()[b2].size.pages() <= b1)
        }) by {
        lemma_join_disjoint_pair(pf, ps, tj, idx, b1, b2);
    }
}

/// Frame- and vpn-disjointness for a pair of distinct `tj` keys: within a half it is
/// inherited; across halves frames are the hypothesis and vpns follow from the
/// disjoint windows.
proof fn lemma_join_disjoint_pair<V: PtPage>(
    pf: PageTablePerms<V>,
    ps: PageTablePerms<V>,
    tj: PageTablePerms<V>,
    idx: nat,
    b1: VPage,
    b2: VPage,
)
    requires
        pf.store_wf(),
        pf.wf(),
        pf.mapping_wf(),
        pf.sub_idx() is None,
        ps.store_wf(),
        ps.wf(),
        ps.mapping_wf(),
        ps.sub_idx() == Some::<nat>(idx),
        idx < ENTRIES,
        !pf.entry(pf.root(), idx).present,
        is_join(pf, ps, tj, idx),
        forall|c1: VPage, c2: VPage|
            (#[trigger] pf.va_map().dom().contains(c1) && #[trigger] ps.va_map().dom().contains(c2))
                ==> {
                let f1 = pf.va_map()[c1].frame;
                let f2 = ps.va_map()[c2].frame;
                f1 + pf.va_map()[c1].size.pages() <= f2 || f2 + ps.va_map()[c2].size.pages() <= f1
            },
        b1 != b2,
        tj.va_map().dom().contains(b1),
        tj.va_map().dom().contains(b2),
    ensures
        ({
            let f1 = tj.va_map()[b1].frame;
            let f2 = tj.va_map()[b2].frame;
            &&& (f1 + tj.va_map()[b1].size.pages() <= f2 || f2 + tj.va_map()[b2].size.pages() <= f1)
            &&& (b1 + tj.va_map()[b1].size.pages() <= b2 || b2 + tj.va_map()[b2].size.pages() <= b1)
        }),
{
    let big = span(ROOT_LEVEL);
    lemma_span_pos(ROOT_LEVEL);
    let in1_ps = ps.va_map().dom().contains(b1);
    let in2_ps = ps.va_map().dom().contains(b2);
    if in1_ps && in2_ps {
        assert(tj.va_map()[b1] == ps.va_map()[b1] && tj.va_map()[b2] == ps.va_map()[b2]);
    } else if !in1_ps && !in2_ps {
        assert(pf.va_map().dom().contains(b1) && pf.va_map().dom().contains(b2));
        assert(tj.va_map()[b1] == pf.va_map()[b1] && tj.va_map()[b2] == pf.va_map()[b2]);
    } else {
        // cross pair: one key in pf (window != idx), one in ps (window idx).
        let (pb, sb): (VPage, VPage) = if in1_ps { (b2, b1) } else { (b1, b2) };
        assert(pf.va_map().dom().contains(pb) && ps.va_map().dom().contains(sb));
        assert(tj.va_map()[pb] == pf.va_map()[pb] && tj.va_map()[sb] == ps.va_map()[sb]);
        lemma_pf_key_not_in_window(pf, idx, pb);  // pf range outside idx's window
        lemma_ps_key_in_window(ps, idx, sb);  // ps range inside idx's window
        assert(pb + pf.va_map()[pb].size.pages() <= sb || sb + ps.va_map()[sb].size.pages() <= pb)
            by (nonlinear_arith)
            requires
                big > 0,
                pb + pf.va_map()[pb].size.pages() <= idx * big || (idx + 1) * big <= pb,
                idx * big <= sb,
                sb + ps.va_map()[sb].size.pages() <= (idx + 1) * big,
        ;
    }
}

/// The subtree view `ps` merges back under entry `idx` of `pf` into a valid,
/// mapping-complete full table `tj` (inverse of `split`).
pub proof fn lemma_join<V: PtPage>(
    pf: PageTablePerms<V>,
    ps: PageTablePerms<V>,
    tj: PageTablePerms<V>,
    idx: nat,
)
    requires
        pf.store_wf(),
        pf.wf(),
        pf.mapping_wf(),
        pf.sub_idx() is None,
        ps.store_wf(),
        ps.wf(),
        ps.mapping_wf(),
        ps.sub_idx() == Some::<nat>(idx),
        idx < ENTRIES,
        idx != IDX_SELFMAP,
        !pf.entry(pf.root(), idx).present,
        pf.pages().dom().disjoint(ps.pages().dom()),
        tj.store_wf(),
        is_join(pf, ps, tj, idx),
        forall|b1: VPage, b2: VPage|
            (#[trigger] pf.va_map().dom().contains(b1) && #[trigger] ps.va_map().dom().contains(b2))
                ==> {
                let f1 = pf.va_map()[b1].frame;
                let f2 = ps.va_map()[b2].frame;
                f1 + pf.va_map()[b1].size.pages() <= f2 || f2 + ps.va_map()[b2].size.pages() <= f1
            },
    ensures
        tj.wf(),
        tj.mapping_wf(),
{
    lemma_join_tree(pf, ps, tj, idx);
    lemma_join_mapping(pf, ps, tj, idx);
}

} // verus!
