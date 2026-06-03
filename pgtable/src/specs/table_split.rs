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

} // verus!
