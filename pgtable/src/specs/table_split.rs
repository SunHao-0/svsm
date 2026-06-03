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

} // verus!
