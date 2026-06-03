// SPDX-License-Identifier: MIT OR Apache-2.0
//
//! Verified proofs for the page-table spec stack: the walk<->path bridge, the
//! per-op tree/mapping preservation arguments, and the supporting arithmetic. Split
//! out of `table.rs`, which keeps only the type, the invariants, and the operations.
#![allow(missing_debug_implementations)]
use crate::specs::node::*;
use crate::specs::perm::*;
use crate::specs::table::*;
use vstd::prelude::*;

verus! {

// =====================================================================
// The walk <-> path bridge: turn the global `walk` into a local leaf fact
// =====================================================================

/// Arithmetic: a vpn inside entry `idx`'s sub-range of a node based at `base`
/// (aligned to the node's stride `s2 = 512*s1`) has page-table index `idx` at the
/// node's level (`s1 = span(level)`). The numeric heart of `lemma_node_on_path_eq`.
pub proof fn lemma_pt_index_in_entry(base: nat, s1: nat, s2: nat, idx: nat, vpn: nat)
    requires
        s1 > 0,
        s2 == 512 * s1,
        idx < 512,
        base % s2 == 0,
        base + idx * s1 <= vpn,
        vpn < base + idx * s1 + s1,
    ensures
        (vpn / s1) % 512 == idx,
{
    let q = base / s2;
    assert(base == s2 * q) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(base as int, s2 as int);
    }
    let r = (vpn - (base + idx * s1)) as nat;
    assert(vpn == s1 * (512 * q + idx) + r) by (nonlinear_arith)
        requires
            base == s2 * q,
            s2 == 512 * s1,
            vpn == base + idx * s1 + r,
    ;
    assert((vpn / s1) == 512 * q + idx) by {
        vstd::arithmetic::div_mod::lemma_div_multiples_vanish_fancy(
            (512 * q + idx) as int,
            r as int,
            s1 as int,
        );
    }
    assert((512 * q + idx) % 512 == idx) by (nonlinear_arith)
        requires
            idx < 512,
    ;
}

/// `span` is always positive (every level covers at least one page).
pub proof fn lemma_span_pos(level: nat)
    ensures
        span(level) > 0,
    decreases level,
{
    if level == 0 {
    } else {
        lemma_span_pos((level - 1) as nat);
    }
}

/// For leaf levels (`<= 2`), size and level round-trip and the level's stride is
/// exactly the size's page count.
pub proof fn lemma_size_level_roundtrip(level: nat)
    requires
        level <= 2,
    ensures
        level_of_size(size_of_level(level)) == level,
        span(level) == size_of_level(level).pages(),
{
    // Definitional by cases on level in {0, 1, 2}.
    if level == 0 {
    } else if level == 1 {
        assert(span(1) == 512 * span(0));
    } else {
        assert(level == 2);
        assert(span(2) == 512 * span(1));
        assert(span(1) == 512 * span(0));
    }
}

/// The structural derivation: a live node sits at the end of the walk path for the
/// vpns in its range. Proven by walking UP from `n` to the root - each step uses
/// connectivity (the unique parent interior link) and `xlate_base_consistent` to
/// pin the parent index, with `lemma_pt_index_in_entry` doing the arithmetic. This
/// is why the structural ops only maintain the LOCAL `xlate_base_consistent`.
#[verifier::rlimit(50)]
pub proof fn lemma_node_on_path_eq<V: PtPage>(t: PageTablePerms<V>, n: PFN, vpn: VPage)
    requires
        t.store_wf(),
        t.contains(t.root()),
        t.tree_inv(),
        t.sub_idx() is None,
        t.xlate_base_consistent(),
        t.xlate_base_aligned(),
        t.contains(n),
        t.node_covers(n, vpn),
    ensures
        t.node_on_path(vpn, t.level(n)) == Some(n),
    decreases ROOT_LEVEL - t.level(n),
{
    broadcast use lemma_node_struct_wf, lemma_node_level_bound;

    let l = t.level(n);
    assert(t.pages()[n].wf());  // store_wf => the node level bound applies
    assert(t.level(t.root()) == ROOT_LEVEL);  // tree_inv + full table
    if l >= ROOT_LEVEL {
        assert(l == ROOT_LEVEL);
        assert(n == t.root());  // tree_wf: unique top-level node
    } else {
        // connectivity: n (!= root, being below the top) has a (unique) parent link.
        assert(t.tree_wf());
        assert(n != t.root());
        let (p, idx): (PFN, nat) = choose|p: PFN, idx: nat|
            #![trigger t.interior_at(p, idx)]
            t.interior_at(p, idx) && t.entry(p, idx).target == n;
        assert(t.interior_at(p, idx) && t.entry(p, idx).target == n);
        assert(t.contains(p) && idx < ENTRIES);
        // node_wf(p): the link is not the self-map (its target is the root, != n
        // since n is below the top), so it drops exactly one level.
        assert(t.node_wf(p));
        assert(n != t.root());
        assert(!t.is_self_map(p, idx));
        assert(t.level(p) == l + 1);
        // xlate_base_consistent pins n's base to the entry's base.
        assert(t.xlate_base(n) == t.entry_vpn_base(p, idx));
        assert(t.entry_vpn_base(p, idx) == t.xlate_base(p) + idx * span((l + 1) as nat));
        lemma_span_pos((l + 1) as nat);
        assert(span((l + 2) as nat) == 512 * span((l + 1) as nat));
        // n's range sits inside p's range, so p covers vpn too.
        assert(t.node_covers(p, vpn)) by {
            assert(idx * span((l + 1) as nat) + span((l + 1) as nat) == (idx + 1) * span(
                (l + 1) as nat,
            )) by (nonlinear_arith);
            assert((idx + 1) * span((l + 1) as nat) <= 512 * span((l + 1) as nat))
                by (nonlinear_arith)
                requires
                    idx < 512,
                    span((l + 1) as nat) >= 0,
            ;
        }
        lemma_node_on_path_eq::<V>(t, p, vpn);
        assert(t.node_on_path(vpn, l + 1) == Some(p));
        // The page-table index at p's level is exactly idx, so the path takes the
        // interior link into n.
        assert(pt_index(vpn, (l + 1) as nat) == idx) by {
            assert(t.xlate_base(p) % span((l + 2) as nat) == 0);  // xlate_base_aligned
            lemma_pt_index_in_entry(
                t.xlate_base(p),
                span((l + 1) as nat),
                span((l + 2) as nat),
                idx,
                vpn,
            );
        }
        assert(t.interior_at(p, pt_index(vpn, (l + 1) as nat)));
    }
}

/// Wrap the per-node derivation into the `reflects_walk` predicate `lemma_leaf_walk`
/// consumes - so `wf` need only carry the local `xlate_base_consistent`.
pub proof fn lemma_reflects_walk<V: PtPage>(t: PageTablePerms<V>)
    requires
        t.store_wf(),
        t.contains(t.root()),
        t.tree_inv(),
        t.sub_idx() is None,
        t.xlate_base_consistent(),
        t.xlate_base_aligned(),
    ensures
        t.xlate_base_reflects_walk(),
{
    assert forall|n: PFN, vpn: VPage|
        #![trigger t.node_covers(n, vpn)]
        (t.contains(n) && t.node_covers(n, vpn)) implies t.node_on_path(vpn, t.level(n)) == Some(n) by {
        lemma_node_on_path_eq::<V>(t, n, vpn);
    }
}

/// The keystone induction: the full `walk` from the root reaches the node the
/// path function names at `level`, with the accumulator the path function names.
/// Proven by induction down from the root; each step consumes one present interior
/// link (which `node_on_path(.., level)` being `Some` guarantees), and `links_wf`
/// keeps every on-path node live so `walk_from` never bails early.
pub proof fn lemma_walk_follows_path<V: PtPage>(t: PageTablePerms<V>, vpn: VPage, level: nat)
    requires
        t.contains(t.root()),
        t.links_wf(),
        level <= ROOT_LEVEL,
        t.node_on_path(vpn, level) is Some,
    ensures
        t.walk(vpn) == t.walk_from(
            t.node_on_path(vpn, level)->Some_0,
            level,
            vpn,
            t.path_acc(vpn, level),
        ),
    decreases ROOT_LEVEL - level,
{
    if level >= ROOT_LEVEL {
        // Base: node_on_path is the root, path_acc is the identity - definitional.
    } else {
        // The level just above is on the path too; recurse there.
        assert(t.node_on_path(vpn, level + 1) is Some);
        lemma_walk_follows_path::<V>(t, vpn, level + 1);
        let p = t.node_on_path(vpn, level + 1)->Some_0;
        let pidx = pt_index(vpn, level + 1);
        // node_on_path(level) Some => (p, pidx) is a present interior link to our node.
        assert(t.interior_at(p, pidx));
        assert(t.entry(p, pidx).target == t.node_on_path(vpn, level)->Some_0);
        // So walk_from at p takes the interior branch into our node.
        assert(t.contains(p));
        assert(!t.entry(p, pidx).leaf && t.level(p) != 0);
    }
}

/// Every interior link on the path is permissive (`interiors_permissive`), so the
/// x86 accumulator stays at the identity all the way down: the leaf alone decides
/// the permission. The induction backing the `perm` half of `lemma_leaf_walk`.
pub proof fn lemma_path_acc_identity<V: PtPage>(t: PageTablePerms<V>, vpn: VPage, level: nat)
    requires
        t.contains(t.root()),
        t.links_wf(),
        t.interiors_permissive(),
        level <= ROOT_LEVEL,
        t.node_on_path(vpn, level) is Some,
    ensures
        t.path_acc(vpn, level) == perm_identity(),
    decreases ROOT_LEVEL - level,
{
    if level >= ROOT_LEVEL {
        // Base: path_acc at the root is the identity - definitional.
    } else {
        lemma_path_acc_identity::<V>(t, vpn, level + 1);
        let p = t.node_on_path(vpn, level + 1)->Some_0;
        let pidx = pt_index(vpn, level + 1);
        assert(t.interior_at(p, pidx));  // node_on_path(level) Some
        assert(permissive(t.entry(p, pidx)));  // interiors_permissive
        lemma_permissive_keeps_top(t.entry(p, pidx));
    }
}

/// The local bridge `map`/`unmap` use: at a node the path reaches, a leaf entry
/// fixes the whole `walk` result. Leaf-direct fields (frame/size/enc) come straight
/// from the entry; `perm` reduces to the leaf's own (`leaf_only_perm`) because the
/// interiors on the path are permissive. Couples a single leaf write to `walk(vpn)`.
pub proof fn lemma_leaf_walk<V: PtPage>(t: PageTablePerms<V>, n: PFN, idx: nat, vpn: VPage)
    requires
        t.contains(t.root()),
        t.links_wf(),
        t.xlate_base_reflects_walk(),
        t.interiors_permissive(),
        t.contains(n),
        t.node_covers(n, vpn),
        idx == pt_index(vpn, t.level(n)),
        t.leaf_at(n, idx),
    ensures
        t.walk(vpn) is Some,
        t.walk(vpn)->Some_0.frame == (t.entry(n, idx).target + vpn % span(t.level(n))) as nat,
        t.walk(vpn)->Some_0.size == size_of_level(t.level(n)),
        t.walk(vpn)->Some_0.perm == leaf_only_perm(t.entry(n, idx)),
        t.walk(vpn)->Some_0.enc == t.entry(n, idx).enc,
{
    let l = t.level(n);
    // reflects_walk: the path reaches exactly this node for vpn.
    assert(t.node_on_path(vpn, l) == Some(n));
    lemma_walk_follows_path::<V>(t, vpn, l);
    // The accumulated permission is the identity (permissive interiors), so the leaf
    // entry decides frame/size/enc/perm.
    lemma_path_acc_identity::<V>(t, vpn, l);
    assert(t.entry(n, pt_index(vpn, l)).present);
    lemma_top_combine_is_leaf_only(t.entry(n, idx));
}

/// THE walk-consistency guarantee the page-table user gets: a recorded mapping is
/// realized by the MMU walk, page by page, in frame/size/perm/enc. The leaf-local
/// `mapping_inv` plus the bridge lemmas yield exactly the (former, global) clause
/// (A) - so the user reasons about `va_map`, and the hardware walk agrees.
#[verifier::rlimit(40)]
pub proof fn lemma_mapping_walk_coupling<V: PtPage>(t: PageTablePerms<V>, b: VPage, k: nat)
    requires
        t.store_wf(),
        t.tree_inv(),
        t.sub_idx() is None,
        t.xlate_base_consistent(),
        t.xlate_base_aligned(),
        t.interiors_permissive(),
        t.mapping_inv(),
        t.va_map().dom().contains(b),
        k < t.va_map()[b].size.pages(),
    ensures
        t.walk((b + k) as nat) is Some,
        t.walk((b + k) as nat)->Some_0.frame == (t.va_map()[b].frame + k) as nat,
        t.walk((b + k) as nat)->Some_0.size == t.va_map()[b].size,
        t.walk((b + k) as nat)->Some_0.perm == t.va_map()[b].perm,
        t.walk((b + k) as nat)->Some_0.enc == t.va_map()[b].enc,
{
    broadcast use lemma_node_struct_wf, lemma_node_level_bound;

    let m = t.va_map()[b];
    let l = level_of_size(m.size);
    let idx = pt_index(b, l);
    // mapping_inv (Q): a leaf at some node n records this mapping; pick that witness.
    let n = choose|n: PFN| t.records_leaf(b, m, n, idx);
    assert(t.records_leaf(b, m, n, idx));
    assert(t.contains(n) && t.level(n) == l && t.leaf_at(n, idx) && t.node_covers(n, b)
        && t.vmap_of_leaf(n, idx) == m && t.entry_vpn_base(n, idx) == b);
    // The leaf sits at level l (leaves are at level <= 2, so size<->level round-trips).
    assert(t.node_wf(n));
    assert(t.level(n) <= 2);
    lemma_size_level_roundtrip(t.level(n));
    assert(t.level(n) == l);
    lemma_span_pos(l);
    assert(span(l) == m.size.pages());
    assert(b % span(l) == 0);
    assert(t.xlate_base(n) + idx * span(l) == b);  // entry_vpn_base(n, idx) == b
    assert(t.xlate_base(n) % span((l + 1) as nat) == 0);  // xlate_base_aligned
    assert(span((l + 1) as nat) == 512 * span(l));

    let vpn = (b + k) as nat;
    // b+k stays inside entry idx of n, so n covers it and the index there is idx.
    assert(t.node_covers(n, vpn)) by {
        assert(idx * span(l) + span(l) == (idx + 1) * span(l)) by (nonlinear_arith);
        assert((idx + 1) * span(l) <= 512 * span(l)) by (nonlinear_arith)
            requires
                idx < 512,
                span(l) >= 0,
        ;
    }
    assert(idx == pt_index(vpn, l)) by {
        lemma_pt_index_in_entry(t.xlate_base(n), span(l), span((l + 1) as nat), idx, vpn);
    }
    assert(vpn % span(l) == k) by (nonlinear_arith)
        requires
            b % span(l) == 0,
            k < span(l),
            span(l) > 0,
            vpn == b + k,
    ;
    lemma_reflects_walk::<V>(t);
    lemma_leaf_walk::<V>(t, n, idx, vpn);
}

/// The framework's whole preservation argument for a leaf write: if `t1` is `t0`
/// with node `pfn`'s entry `idx` set to a leaf/absent `e` that satisfies
/// `valid_leaf_write` - and nothing else changed - then `t1` is still a valid
/// tree. Because a leaf write never touches an interior link, `interior_at` (and
/// hence the entire tree shape) is unchanged, so every `tree_wf` clause transfers
/// verbatim. The caller of `table_set_entry` never sees this.
#[verifier::rlimit(40)]
pub proof fn lemma_leaf_write_preserves_tree_inv<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    pfn: PFN,
    idx: nat,
    e: Entry,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.valid_leaf_write(pfn, idx, e),
        t1.root() == t0.root(),
        t1.sub_idx() == t0.sub_idx(),
        t1.pages().dom() == t0.pages().dom(),
        t1.node(pfn) == t0.node(pfn).update(idx, e),
        forall|m: PFN| m != pfn ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| #[trigger] t1.level(m) == t0.level(m),
    ensures
        t1.tree_inv(),
{
    broadcast use lemma_node_struct_wf;

    let r = t0.root();
    assert(t1.root_level() == t0.root_level() && t1.root_base() == t0.root_base());
    // node(pfn) has its full entry set, so inserting at idx (already present)
    // leaves its domain - and hence `contains` and node domains - unchanged.
    assert(t0.node(pfn).e.dom().contains(idx));
    assert forall|n: PFN| t1.contains(n) implies #[trigger] t1.node(n).e.dom() =~= t0.node(n).e.dom()
        by {
        if n == pfn {
            assert(t0.node(pfn).e.insert(idx, e).dom() =~= t0.node(pfn).e.dom());
        }
    }
    // Entries agree everywhere except (pfn, idx); at (pfn, idx) it is a leaf/absent.
    assert forall|n: PFN, i: nat| (n != pfn || i != idx) implies #[trigger] t1.entry(n, i)
        == t0.entry(n, i) by {
        if n == pfn {
            assert(t1.node(pfn).e[i] == t0.node(pfn).e.insert(idx, e)[i]);
        }
    }
    // Therefore interior_at is unchanged everywhere - the heart of the argument.
    assert forall|n: PFN, i: nat| #[trigger] t1.interior_at(n, i) == t0.interior_at(n, i) by {
        if !(n == pfn && i == idx) {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }
    assert(!t1.interior_at(pfn, idx));
    assert(!t0.interior_at(pfn, idx));
    // An interior entry of t1 is not the edited slot, so its entry is unchanged.
    assert forall|n: PFN, i: nat| t1.interior_at(n, i) implies #[trigger] t1.entry(n, i) == t0.entry(
        n,
        i,
    ) by {
        if n == pfn && i == idx {
        } else {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }

    // --- tree_wf, clause by clause -----------------------------------
    // root is still the unique node at its level (levels/contains/root fixed).
    assert forall|n: PFN| #![trigger t1.contains(n)]
        t1.contains(n) && t1.level(n) == t1.root_level() implies n == r by {
        assert(t0.contains(n));
    }
    // the self-map (full table only) is unchanged: it is interior in t0, hence not
    // the edited (leaf) slot.
    assert(t1.self_map_inv()) by {
        if t1.sub_idx() is None {
            assert(t0.interior_at(r, IDX_SELFMAP) && t0.entry(r, IDX_SELFMAP).target == r);
            assert(t1.interior_at(r, IDX_SELFMAP));
            assert(t1.entry(r, IDX_SELFMAP) == t0.entry(r, IDX_SELFMAP));
        }
    }
    // injectivity: an interior entry of t1 is one of t0 with the same target.
    assert forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
        (#[trigger] t1.interior_at(n1, i1) && #[trigger] t1.interior_at(n2, i2) && t1.entry(
            n1,
            i1,
        ).target == t1.entry(n2, i2).target) implies (n1 == n2 && i1 == i2) by {
        assert(t0.interior_at(n1, i1));
        assert(t0.interior_at(n2, i2));
    }
    // connectivity: t0's parent of c (!= root) is still a parent in t1.
    assert forall|c: PFN| #![trigger t1.contains(c)]
        (t1.contains(c) && c != r) implies exists|n: PFN, i: nat|
        #[trigger] t1.interior_at(n, i) && t1.entry(n, i).target == c by {
        assert(t0.contains(c));
        let w = choose|n: PFN, i: nat|
            #![trigger t0.interior_at(n, i)]
            t0.interior_at(n, i) && t0.entry(n, i).target == c;
        assert(t1.interior_at(w.0, w.1));
    }
    assert(t1.tree_wf());

    // links resolve: away from pfn unchanged; at pfn the edited slot is a valid leaf.
    assert forall|n: PFN| t1.contains(n) implies #[trigger] t1.node_wf(n) by {
        if n != pfn {
            assert(t0.node_wf(n));
        } else {
            assert(t0.node_wf(pfn));
        }
    }
    // A/D pinned: away from (pfn, idx) unchanged; at (pfn, idx) `e` is pinned.
    assert forall|n: PFN, i: nat|
        (t1.contains(n) && i < ENTRIES && t1.node(n).e.dom().contains(i)) implies entry_pinned(
            #[trigger] t1.entry(n, i),
        ) by {
        if !(n == pfn && i == idx) {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }
}

/// A leaf write preserves the mapping BACKING too: a `valid_leaf_write` never makes
/// an interior link, and leaves every node's base alone, so `interior_at` is
/// pointwise unchanged and `xlate_wf` transfers verbatim. (`mapping_inv` is NOT
/// preserved by a bare leaf write - `map`/`unmap` re-establish it after recording.)
#[verifier::rlimit(40)]
pub proof fn lemma_leaf_write_preserves_xlate_wf<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    pfn: PFN,
    idx: nat,
    e: Entry,
)
    requires
        t0.store_wf(),
        t0.xlate_wf(),
        t0.valid_leaf_write(pfn, idx, e),
        t1.root() == t0.root(),
        t1.sub_idx() == t0.sub_idx(),
        t1.pages().dom() == t0.pages().dom(),
        t1.node(pfn) == t0.node(pfn).update(idx, e),
        forall|m: PFN| m != pfn ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| #[trigger] t1.level(m) == t0.level(m),
        forall|m: PFN| #[trigger] t1.xlate_base(m) == t0.xlate_base(m),
    ensures
        t1.xlate_wf(),
{
    broadcast use lemma_node_struct_wf;

    assert(t0.node(pfn).e.dom().contains(idx));
    assert forall|n: PFN, i: nat| (n != pfn || i != idx) implies #[trigger] t1.entry(n, i)
        == t0.entry(n, i) by {
        if n == pfn {
            assert(t1.node(pfn).e[i] == t0.node(pfn).e.insert(idx, e)[i]);
        }
    }
    assert(!t0.interior_at(pfn, idx));  // valid_leaf_write
    assert(!t1.interior_at(pfn, idx));  // e is a leaf/absent
    assert forall|n: PFN, i: nat| #[trigger] t1.interior_at(n, i) == t0.interior_at(n, i) by {
        if !(n == pfn && i == idx) {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }
    assert(t1.interiors_permissive()) by {
        assert forall|n: PFN, i: nat| #[trigger] t1.interior_at(n, i) implies permissive(
            t1.entry(n, i),
        ) by {
            assert(t0.interior_at(n, i));
            assert(n != pfn || i != idx);
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }
    assert(t1.xlate_base_consistent()) by {
        assert(t1.root_base() == t0.root_base());
        assert(t1.xlate_base(t1.root()) == t1.root_base());
        assert forall|p: PFN, i: nat| (#[trigger] t1.interior_at(p, i) && !t1.is_self_map(p, i))
            implies t1.xlate_base(t1.entry(p, i).target) == t1.entry_vpn_base(p, i) by {
            assert(t0.interior_at(p, i));
            assert(p != pfn || i != idx);
            assert(t1.entry(p, i) == t0.entry(p, i));
            assert(!t0.is_self_map(p, i));
            let tgt = t0.entry(p, i).target;
            assert(t1.xlate_base(tgt) == t0.xlate_base(tgt));
            assert(t1.entry_vpn_base(p, i) == t0.entry_vpn_base(p, i));
        }
    }
    assert(t1.xlate_base_aligned()) by {
        assert forall|n: PFN| #[trigger] t1.contains(n) implies t1.xlate_base(n) % span(
            (t1.level(n) + 1) as nat,
        ) == 0 by {
            assert(t0.contains(n));
        }
    }
}

/// The framework proof behind `map`: writing a leaf into an ABSENT user-region slot
/// `(node, idx)` and recording the single mapping `b = entry_vpn_base(node, idx)`
/// preserves `mapping_inv`. The changed leaf IS the new mapping's, so every existing
/// recorded witness keeps its (unchanged) leaf; the new leaf is recorded at `b`; and
/// the caller's disjointness preconditions give the one-to-one clauses.
#[verifier::rlimit(60)]
pub proof fn lemma_map_records_mapping_inv<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    node: PFN,
    idx: nat,
    e: Entry,
    b: VPage,
)
    requires
        t0.store_wf(),
        t0.mapping_inv(),
        t0.xlate_base_aligned(),
        t0.contains(node),
        idx < ENTRIES,
        t0.level(node) <= 2,
        !t0.entry(node, idx).present,
        e.present,
        t0.level(node) == 0 || e.leaf,
        e.target % span(t0.level(node)) == 0,
        b == t0.entry_vpn_base(node, idx),
        in_user_region(b),
        t1.root() == t0.root(),
        t1.pages().dom() == t0.pages().dom(),
        t1.node(node) == t0.node(node).update(idx, e),
        forall|m: PFN| m != node ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| #[trigger] t1.level(m) == t0.level(m),
        forall|m: PFN| #[trigger] t1.xlate_base(m) == t0.xlate_base(m),
        t1.va_map() == t0.va_map().insert(b, t1.vmap_of_leaf(node, idx)),
        // the new mapping's vpn/frame ranges are disjoint from every existing one.
        forall|b2: VPage| #[trigger]
            t0.va_map().dom().contains(b2) ==> {
                let s = t1.vmap_of_leaf(node, idx).size.pages();
                let f = t1.vmap_of_leaf(node, idx).frame;
                &&& (b + s <= b2 || b2 + t0.va_map()[b2].size.pages() <= b)
                &&& (f + s <= t0.va_map()[b2].frame || t0.va_map()[b2].frame
                    + t0.va_map()[b2].size.pages() <= f)
            },
    ensures
        t1.mapping_inv(),
{
    broadcast use lemma_node_struct_wf;

    let l = t0.level(node);
    let m = t1.vmap_of_leaf(node, idx);
    lemma_span_pos(l);
    lemma_size_level_roundtrip(l);
    assert(t0.node(node).e.dom().contains(idx));
    assert forall|n: PFN, i: nat| (n != node || i != idx) implies #[trigger] t1.entry(n, i)
        == t0.entry(n, i) by {
        if n == node {
            assert(t1.node(node).e[i] == t0.node(node).e.insert(idx, e)[i]);
        }
    }
    assert(t1.entry(node, idx) == e);
    assert(t1.leaf_at(node, idx));
    assert forall|n: PFN, i: nat| (n != node || i != idx) implies #[trigger] t1.leaf_at(n, i)
        == t0.leaf_at(n, i) by {
        assert(t1.entry(n, i) == t0.entry(n, i));
    }
    // arithmetic for the new key b.
    assert(t1.level(node) == l && m.size == size_of_level(l) && m.size.pages() == span(l));
    assert(span((l + 1) as nat) == 512 * span(l));
    assert(b == t0.xlate_base(node) + idx * span(l));
    assert(t0.xlate_base(node) % span((l + 1) as nat) == 0);
    lemma_base_aligned(t0.xlate_base(node), span(l), span((l + 1) as nat), idx);
    assert(b % m.size.pages() == 0);
    lemma_pt_index_in_entry(t0.xlate_base(node), span(l), span((l + 1) as nat), idx, b);
    assert(pt_index(b, level_of_size(m.size)) == idx);
    assert(t1.node_covers(node, b)) by {
        assert((idx + 1) * span(l) <= 512 * span(l)) by (nonlinear_arith)
            requires
                idx < 512,
                span(l) >= 0,
        ;
        assert(idx * span(l) + span(l) == (idx + 1) * span(l)) by (nonlinear_arith);
    }
    assert(t1.records_leaf(b, m, node, pt_index(b, level_of_size(m.size))));
    assert(m.frame % m.size.pages() == 0);  // e.target % span(l) == 0
    assert(t0.entry_vpn_base(node, idx) == t1.entry_vpn_base(node, idx));

    // (Q): the new key records the new leaf; existing keys keep their (unchanged) leaf.
    assert forall|b2: VPage| #[trigger] t1.va_map().dom().contains(b2) implies {
        let m2 = t1.va_map()[b2];
        &&& in_user_region(b2)
        &&& b2 % m2.size.pages() == 0
        &&& m2.frame % m2.size.pages() == 0
        &&& exists|n: PFN| t1.records_leaf(b2, m2, n, pt_index(b2, level_of_size(m2.size)))
    } by {
        if b2 == b {
            assert(t1.va_map()[b] == m);
            assert(t1.records_leaf(b, m, node, pt_index(b, level_of_size(m.size))));
        } else {
            assert(t0.va_map().dom().contains(b2) && t1.va_map()[b2] == t0.va_map()[b2]);
            let m2 = t0.va_map()[b2];
            let ii = pt_index(b2, level_of_size(m2.size));
            let w = choose|n: PFN| t0.records_leaf(b2, m2, n, ii);
            assert(t0.records_leaf(b2, m2, w, ii));
            assert(t0.entry_vpn_base(w, ii) == b2 && b2 != b);  // so (w,ii) != (node,idx)
            assert(t1.records_leaf(b2, m2, w, ii));
        }
    }
    // (P): the new leaf is recorded at b; existing leaves stay recorded.
    assert forall|n: PFN, i: nat|
        (#[trigger] t1.leaf_at(n, i) && in_user_region(t1.entry_vpn_base(n, i)))
            implies t1.va_map().dom().contains(t1.entry_vpn_base(n, i)) by {
        if !(n == node && i == idx) {
            assert(t0.leaf_at(n, i));
            assert(t1.entry_vpn_base(n, i) == t0.entry_vpn_base(n, i));
        }
    }
    // (C) frame ranges disjoint, (D) vpn ranges disjoint.
    assert forall|b1: VPage, b2: VPage|
        (b1 != b2 && #[trigger] t1.va_map().dom().contains(b1) && #[trigger] t1.va_map().dom().contains(
            b2,
        )) implies {
            &&& t1.va_map()[b1].frame + t1.va_map()[b1].size.pages() <= t1.va_map()[b2].frame
                || t1.va_map()[b2].frame + t1.va_map()[b2].size.pages() <= t1.va_map()[b1].frame
            &&& b1 + t1.va_map()[b1].size.pages() <= b2 || b2 + t1.va_map()[b2].size.pages() <= b1
        } by {
        if b1 != b && b2 != b {
            assert(t1.va_map()[b1] == t0.va_map()[b1] && t1.va_map()[b2] == t0.va_map()[b2]);
        } else if b1 == b {
            assert(t0.va_map().dom().contains(b2) && t1.va_map()[b2] == t0.va_map()[b2]);
            assert(t1.va_map()[b] == m);
        } else {
            assert(t0.va_map().dom().contains(b1) && t1.va_map()[b1] == t0.va_map()[b1]);
            assert(t1.va_map()[b] == m);
        }
    }
}

/// The framework proof behind `unmap`: clearing the leaf at the recorded slot
/// `(node, idx)` and dropping its mapping key `b = entry_vpn_base(node, idx)`
/// preserves `mapping_inv`. The caller passes that `(node, idx)` is the UNIQUE leaf
/// based at `b` (it is, by the tree shape) - so after clearing it no leaf is left
/// unrecorded - and the surviving keys keep their (unchanged) leaves.
#[verifier::rlimit(60)]
pub proof fn lemma_unmap_clears_mapping_inv<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    node: PFN,
    idx: nat,
    b: VPage,
)
    requires
        t0.store_wf(),
        t0.mapping_inv(),
        t0.contains(node),
        idx < ENTRIES,
        t0.level(node) <= 2,
        t0.leaf_at(node, idx),
        b == t0.entry_vpn_base(node, idx),
        t0.va_map().dom().contains(b),
        forall|n2: PFN, i2: nat|
            (#[trigger] t0.leaf_at(n2, i2) && t0.entry_vpn_base(n2, i2) == b) ==> (n2 == node && i2
                == idx),
        t1.root() == t0.root(),
        t1.pages().dom() == t0.pages().dom(),
        t1.node(node) == t0.node(node).update(idx, entry_absent()),
        forall|m: PFN| m != node ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| #[trigger] t1.level(m) == t0.level(m),
        forall|m: PFN| #[trigger] t1.xlate_base(m) == t0.xlate_base(m),
        t1.va_map() == t0.va_map().remove(b),
    ensures
        t1.mapping_inv(),
{
    broadcast use lemma_node_struct_wf;

    assert(t0.node(node).e.dom().contains(idx));
    assert forall|n: PFN, i: nat| (n != node || i != idx) implies #[trigger] t1.entry(n, i)
        == t0.entry(n, i) by {
        if n == node {
            assert(t1.node(node).e[i] == t0.node(node).e.insert(idx, entry_absent())[i]);
        }
    }
    assert(t1.entry(node, idx) == entry_absent());
    assert(!t1.leaf_at(node, idx));
    assert forall|n: PFN, i: nat| (n != node || i != idx) implies #[trigger] t1.leaf_at(n, i)
        == t0.leaf_at(n, i) by {
        assert(t1.entry(n, i) == t0.entry(n, i));
    }
    assert forall|n: PFN, i: nat| t0.leaf_at(n, i) implies #[trigger] t1.entry_vpn_base(n, i)
        == t0.entry_vpn_base(n, i) by {}

    // (Q): surviving keys (!= b) keep their unchanged leaf witness.
    assert forall|b2: VPage| #[trigger] t1.va_map().dom().contains(b2) implies {
        let m2 = t1.va_map()[b2];
        &&& in_user_region(b2)
        &&& b2 % m2.size.pages() == 0
        &&& m2.frame % m2.size.pages() == 0
        &&& exists|n: PFN| t1.records_leaf(b2, m2, n, pt_index(b2, level_of_size(m2.size)))
    } by {
        assert(b2 != b && t0.va_map().dom().contains(b2) && t1.va_map()[b2] == t0.va_map()[b2]);
        let m2 = t0.va_map()[b2];
        let ii = pt_index(b2, level_of_size(m2.size));
        let w = choose|n: PFN| t0.records_leaf(b2, m2, n, ii);
        assert(t0.records_leaf(b2, m2, w, ii));
        assert(t0.entry_vpn_base(w, ii) == b2 && b2 != b);  // so (w,ii) != (node,idx)
        assert(t1.records_leaf(b2, m2, w, ii));
    }
    // (P): surviving leaves are recorded; uniqueness => their base != b, so still kept.
    assert forall|n: PFN, i: nat|
        (#[trigger] t1.leaf_at(n, i) && in_user_region(t1.entry_vpn_base(n, i)))
            implies t1.va_map().dom().contains(t1.entry_vpn_base(n, i)) by {
        assert(t0.leaf_at(n, i));
        assert(t0.entry_vpn_base(n, i) != b);  // uniqueness ((n,i) != (node,idx))
    }
    // (C)/(D): t1.va_map is a subset of t0.va_map, so disjointness is inherited.
    assert forall|b1: VPage, b2: VPage|
        (b1 != b2 && #[trigger] t1.va_map().dom().contains(b1) && #[trigger] t1.va_map().dom().contains(
            b2,
        )) implies {
            &&& t1.va_map()[b1].frame + t1.va_map()[b1].size.pages() <= t1.va_map()[b2].frame
                || t1.va_map()[b2].frame + t1.va_map()[b2].size.pages() <= t1.va_map()[b1].frame
            &&& b1 + t1.va_map()[b1].size.pages() <= b2 || b2 + t1.va_map()[b2].size.pages() <= b1
        } by {
        assert(t0.va_map().dom().contains(b1) && t0.va_map().dom().contains(b2));
        assert(t1.va_map()[b1] == t0.va_map()[b1] && t1.va_map()[b2] == t0.va_map()[b2]);
    }
}

/// The framework's preservation argument for linking a FRESH child: if `t1` is
/// `t0` with a fresh, empty child node inserted (at `level(parent)-1`) and
/// `parent[idx]` - previously absent - set to `interior_entry(child)`, then `t1`
/// is still a valid tree. Freshness is the crux: because `child` was not in `t0`,
/// no existing interior entry targets it (their targets are live nodes), so the
/// new link is `child`'s unique parent (injectivity) and gives it connectivity.
#[verifier::rlimit(60)]
pub proof fn lemma_link_child_preserves_tree_inv<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.contains(parent),
        idx < ENTRIES,
        t0.level(parent) >= 1,
        !t0.node(parent).e[idx].present,
        !(parent == t0.root() && idx == IDX_SELFMAP),
        !t0.contains(child),
        t1.store_wf(),
        t1.root() == t0.root(),
        t1.sub_idx() == t0.sub_idx(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c == child || t0.contains(c)),
        t1.node(child).empty(),
        t1.level(child) == t0.level(parent) - 1,
        t1.node(parent) == t0.node(parent).update(idx, interior_entry(child)),
        t1.level(parent) == t0.level(parent),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
    ensures
        t1.tree_inv(),
{
    broadcast use lemma_node_struct_wf, lemma_node_level_bound;

    let r = t0.root();
    let ei = interior_entry(child);
    assert(child != parent && child != r);
    assert(t0.node(parent).e.dom().contains(idx));
    assert(t0.level(parent) <= ROOT_LEVEL);
    assert(t1.level(child) < ROOT_LEVEL);

    // Entries: unchanged except (parent, idx) -> ei; child's entries are all absent.
    assert forall|n: PFN, i: nat| (n != parent || i != idx) && n != child implies
        #[trigger] t1.entry(n, i) == t0.entry(n, i) by {
        if n == parent {
            assert(t1.node(parent).e[i] == t0.node(parent).e.insert(idx, ei)[i]);
        }
    }
    assert(t1.entry(parent, idx) == ei);
    // interior_at: gains (parent, idx); child has none; unchanged elsewhere.
    assert(t1.interior_at(parent, idx));
    assert forall|i: nat| !#[trigger] t1.interior_at(child, i) by {}
    assert forall|n: PFN, i: nat| (n != parent || i != idx) implies
        #[trigger] t1.interior_at(n, i) == t0.interior_at(n, i) by {
        if n != child {
            assert(t1.entry(n, i) == t0.entry(n, i));
        } else {
            assert(!t1.interior_at(child, i));
            assert(!t0.interior_at(child, i));
        }
    }
    // A t0 interior entry targets a live t0 node (via node_wf), hence not `child`.
    assert forall|n: PFN, i: nat| t0.interior_at(n, i) implies
        (#[trigger] t0.contains(t0.entry(n, i).target) && t0.entry(n, i).target != child) by {
        assert(t0.node_wf(n));
    }

    // --- tree_wf, clause by clause -----------------------------------
    assert(t1.root_level() == t0.root_level() && t1.root_base() == t0.root_base());
    assert(t1.level(child) != t1.root_level());
    assert forall|n: PFN| #![trigger t1.contains(n)]
        t1.contains(n) && t1.level(n) == t1.root_level() implies n == r by {
        if n != child {
            assert(t0.contains(n));
        }
    }
    // the self-map (full table only) is unchanged: not the (parent, idx) slot.
    assert(t1.self_map_inv()) by {
        if t1.sub_idx() is None {
            assert(t0.interior_at(r, IDX_SELFMAP) && t0.entry(r, IDX_SELFMAP).target == r);
            assert(!(parent == r && idx == IDX_SELFMAP));
            assert(t1.interior_at(r, IDX_SELFMAP));
            assert(t1.entry(r, IDX_SELFMAP) == t0.entry(r, IDX_SELFMAP));
        }
    }
    // injectivity: each interior entry of t1 is (parent,idx)->child, or a t0
    // interior with target in t0's store (so != child) - the two never collide.
    assert forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
        (#[trigger] t1.interior_at(n1, i1) && #[trigger] t1.interior_at(n2, i2) && t1.entry(
            n1,
            i1,
        ).target == t1.entry(n2, i2).target) implies (n1 == n2 && i1 == i2) by {
        if (n1 == parent && i1 == idx) && !(n2 == parent && i2 == idx) {
            assert(t0.interior_at(n2, i2) && t1.entry(n2, i2) == t0.entry(n2, i2));
        } else if !(n1 == parent && i1 == idx) && (n2 == parent && i2 == idx) {
            assert(t0.interior_at(n1, i1) && t1.entry(n1, i1) == t0.entry(n1, i1));
        } else if !(n1 == parent && i1 == idx) && !(n2 == parent && i2 == idx) {
            assert(t0.interior_at(n1, i1) && t1.entry(n1, i1) == t0.entry(n1, i1));
            assert(t0.interior_at(n2, i2) && t1.entry(n2, i2) == t0.entry(n2, i2));
        }
    }
    // connectivity: child's parent is (parent, idx); t0 nodes keep their parents.
    assert forall|c: PFN| #![trigger t1.contains(c)]
        (t1.contains(c) && c != r) implies exists|n: PFN, i: nat|
        #[trigger] t1.interior_at(n, i) && t1.entry(n, i).target == c by {
        if c == child {
            assert(t1.interior_at(parent, idx) && t1.entry(parent, idx).target == child);
        } else {
            assert(t0.contains(c));
            let w = choose|n: PFN, i: nat|
                #![trigger t0.interior_at(n, i)]
                t0.interior_at(n, i) && t0.entry(n, i).target == c;
            assert(t1.interior_at(w.0, w.1) && t1.entry(w.0, w.1).target == c);
        }
    }
    assert(t1.tree_wf());

    // links resolve.
    assert forall|n: PFN| t1.contains(n) implies #[trigger] t1.node_wf(n) by {
        if n == child {
        } else if n == parent {
            assert(t0.node_wf(parent));
        } else {
            assert(t0.node_wf(n));
        }
    }
    // A/D pinned: the new interior entry is pinned; child's are absent; rest fixed.
    assert forall|n: PFN, i: nat|
        (t1.contains(n) && i < ENTRIES && t1.node(n).e.dom().contains(i)) implies entry_pinned(
            #[trigger] t1.entry(n, i),
        ) by {
        if (n != parent || i != idx) && n != child {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }
}

/// `xlate_wf` half of the link-child mapping preservation, in its own small proof
/// context (no `leaf_at`/`va_map` reasoning): the new interior is permissive, the
/// new link is consistent (child's base == the entry's base), and the child's base
/// is aligned. By freshness no existing interior targets `child`.
#[verifier::rlimit(50)]
pub proof fn lemma_link_child_xlate_wf<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.xlate_wf(),
        t0.contains(t0.root()),
        t0.level(parent) <= ROOT_LEVEL,
        t0.contains(parent),
        idx < ENTRIES,
        t0.level(parent) >= 1,
        !t0.node(parent).e[idx].present,
        !(parent == t0.root() && idx == IDX_SELFMAP),
        !t0.contains(child),
        t1.sub_idx() == t0.sub_idx(),
        // freshness: no existing interior targets `child` (derived from tree_inv by
        // the caller, passed here so this context stays free of the tree soup).
        forall|n: PFN, i: nat| #[trigger] t0.interior_at(n, i) ==> t0.entry(n, i).target != child,
        t1.root() == t0.root(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c == child || t0.contains(c)),
        t1.node(child).empty(),
        t1.level(child) == t0.level(parent) - 1,
        t1.node(parent) == t0.node(parent).update(idx, interior_entry(child)),
        t1.level(parent) == t0.level(parent),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
        t1.xlate_base(child) == t0.entry_vpn_base(parent, idx),
        forall|m: PFN| m != child ==> #[trigger] t1.xlate_base(m) == t0.xlate_base(m),
    ensures
        t1.xlate_wf(),
{
    broadcast use lemma_node_struct_wf;

    // Shared entry congruence: every slot but the freshly written (parent, idx) and
    // the empty child reads as in `t0`.
    let ei = interior_entry(child);
    assert(t0.node(parent).e.dom().contains(idx));
    assert forall|n: PFN, i: nat| (n != child && (n != parent || i != idx)) implies
        #[trigger] t1.entry(n, i) == t0.entry(n, i) by {
        if n == parent {
            assert(t1.node(parent).e[i] == t0.node(parent).e.insert(idx, ei)[i]);
        }
    }
    assert(t1.entry(parent, idx) == ei);

    // interiors_permissive: the new link is permissive; every other interior is a t0
    // interior, unchanged.
    assert(t1.interiors_permissive()) by {
        assert forall|n: PFN, i: nat| #[trigger] t1.interior_at(n, i) implies permissive(
            t1.entry(n, i),
        ) by {
            if !(n == parent && i == idx) {
                assert(n != child && t1.entry(n, i) == t0.entry(n, i) && t0.interior_at(n, i));
            }
        }
    }
    // xlate_base_consistent: the new link sets child's base to the entry base; the
    // root base is unchanged; other links are t0's (freshness keeps targets != child).
    assert(t1.xlate_base_consistent()) by {
        assert(t0.root() != child);  // child is fresh, root is live
        assert(t1.root_base() == t0.root_base() && t0.xlate_base(t0.root()) == t0.root_base());
        assert(t1.xlate_base(t1.root()) == t1.root_base());  // root != child, base unchanged
        assert forall|p: PFN, i: nat| (#[trigger] t1.interior_at(p, i) && !t1.is_self_map(p, i))
            implies t1.xlate_base(t1.entry(p, i).target) == t1.entry_vpn_base(p, i) by {
            if p == parent && i == idx {
                assert(t1.entry(parent, idx).target == child);
                assert(t1.entry_vpn_base(parent, idx) == t0.entry_vpn_base(parent, idx));
            } else {
                assert(p != child && t1.entry(p, i) == t0.entry(p, i));
                assert(t0.interior_at(p, i) && !t0.is_self_map(p, i));
                let tgt = t0.entry(p, i).target;
                assert(tgt != child);  // freshness
                assert(t1.xlate_base(tgt) == t0.xlate_base(tgt));
                assert(t1.entry_vpn_base(p, i) == t0.entry_vpn_base(p, i));
            }
        }
    }
    // xlate_base_aligned: child's base is the parent base plus idx strides, still
    // aligned (the only nonlinear step is delegated); other nodes keep t0's bases.
    assert(t1.xlate_base_aligned()) by {
        let lp = t0.level(parent);
        lemma_span_pos(lp);
        assert(span((lp + 1) as nat) == 512 * span(lp) && span(lp) > 0);
        assert(t1.level(child) == (lp - 1) as nat && (lp - 1 + 1) as nat == lp);
        assert(t1.xlate_base(child) == t0.xlate_base(parent) + idx * span(lp));
        lemma_base_aligned(t0.xlate_base(parent), span(lp), span((lp + 1) as nat), idx);
        assert forall|n: PFN| #[trigger] t1.contains(n) implies t1.xlate_base(n) % span(
            (t1.level(n) + 1) as nat,
        ) == 0 by {
            if n != child {
                assert(t1.xlate_base(n) == t0.xlate_base(n) && t1.level(n) == t0.level(n));
            }
        }
    }
}

/// Arithmetic, isolated so the nonlinear solver work stays out of the structural
/// proofs: a base aligned to the parent stride `s2 = 512*s` plus `idx` child strides
/// `s` is still aligned to `s`.
pub proof fn lemma_base_aligned(a: nat, s: nat, s2: nat, idx: nat)
    requires
        s2 == 512 * s,
        a % s2 == 0,
        s > 0,
    ensures
        (a + idx * s) % s == 0,
{
    let ai = a as int;
    let si = s as int;
    // Step 1: a % s == 0, since a % (512*s) == 0 and s | (512*s).
    vstd::arithmetic::div_mod::lemma_mod_mod(ai, si, 512);  // (ai % (si*512)) % si == ai % si
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(0, si);  // 0 % si == 0
    assert(si * 512 == s2 as int);
    assert(ai % (si * 512) == 0);  // si*512 == s2, and a % s2 == 0
    assert((ai % (si * 512)) % si == ai % si);  // lemma_mod_mod
    assert(ai % si == 0);
    // Step 2: adding idx whole strides of s does not change the residue.
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(idx as int, ai, si);  // (si*idx+ai)%si == ai%si
    assert((ai + (idx as int) * si) == si * (idx as int) + ai);
    assert((a + idx * s) as int == ai + (idx as int) * si);
}


/// `mapping_inv` half of the link-child preservation, in its own small context (no
/// `interior_at`/`tree_inv` reasoning): `child` is empty so `leaf_at` and every
/// leaf's base are unchanged; thus the recorded witnesses and the leaf->record
/// direction transfer, and `va_map` is untouched so the disjointness clauses hold.
#[verifier::rlimit(50)]
pub proof fn lemma_link_child_mapping_inv<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.mapping_inv(),
        t0.contains(parent),
        idx < ENTRIES,
        t0.level(parent) >= 1,
        !t0.node(parent).e[idx].present,
        !t0.contains(child),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c == child || t0.contains(c)),
        t1.node(child).empty(),
        t1.node(parent) == t0.node(parent).update(idx, interior_entry(child)),
        t1.level(parent) == t0.level(parent),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
        forall|m: PFN| m != child ==> #[trigger] t1.xlate_base(m) == t0.xlate_base(m),
        t1.va_map() == t0.va_map(),
    ensures
        t1.mapping_inv(),
{
    broadcast use lemma_node_struct_wf;

    let ei = interior_entry(child);
    assert(child != parent);
    assert(t0.node(parent).e.dom().contains(idx));
    assert forall|n: PFN, i: nat| (n != child && (n != parent || i != idx)) implies
        #[trigger] t1.entry(n, i) == t0.entry(n, i) by {
        if n == parent {
            assert(t1.node(parent).e[i] == t0.node(parent).e.insert(idx, ei)[i]);
        }
    }
    // leaf_at is unchanged everywhere: `child` is empty, the linked slot is interior.
    assert forall|n: PFN, i: nat| #[trigger] t1.leaf_at(n, i) == t0.leaf_at(n, i) by {
        if n == child {
            assert(!t1.leaf_at(child, i));
            assert(!t0.leaf_at(child, i));
        } else if n == parent && i == idx {
            assert(!t1.leaf_at(parent, idx));  // interior, level >= 1
            assert(!t0.leaf_at(parent, idx));  // absent
        } else {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }
    // a t0 leaf (n, i) is unchanged in t1 (n != child, (n,i) != (parent,idx)).
    assert forall|n: PFN, i: nat| t0.leaf_at(n, i) implies (n != child && #[trigger] t1.entry(n, i)
        == t0.entry(n, i) && t1.entry_vpn_base(n, i) == t0.entry_vpn_base(n, i)) by {}

    // (Q): the t0 witness leaf (!= child) still records b.
    assert forall|b: VPage| #[trigger] t1.va_map().dom().contains(b) implies {
        let m = t1.va_map()[b];
        &&& in_user_region(b)
        &&& b % m.size.pages() == 0
        &&& m.frame % m.size.pages() == 0
        &&& exists|n: PFN| t1.records_leaf(b, m, n, pt_index(b, level_of_size(m.size)))
    } by {
        let m = t0.va_map()[b];
        let ii = pt_index(b, level_of_size(m.size));
        let w = choose|n: PFN| t0.records_leaf(b, m, n, ii);
        assert(t0.records_leaf(b, m, w, ii));
        assert(t0.leaf_at(w, ii) && w != child);
        assert(t1.records_leaf(b, m, w, ii));
    }
    // (P): leaf_at and entry bases are unchanged, so every leaf is still recorded.
    assert forall|n: PFN, i: nat|
        (#[trigger] t1.leaf_at(n, i) && in_user_region(t1.entry_vpn_base(n, i)))
            implies t1.va_map().dom().contains(t1.entry_vpn_base(n, i)) by {
        assert(t0.leaf_at(n, i));
    }
}

/// The mapping-layer companion to `lemma_link_child_preserves_tree_inv`: linking a
/// fresh EMPTY child preserves `mapping_wf`. Kept THIN - each half in its own small
/// context (see the soup lesson).
pub proof fn lemma_link_child_preserves_mapping_wf<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.mapping_wf(),
        t0.contains(parent),
        idx < ENTRIES,
        t0.level(parent) >= 1,
        !t0.node(parent).e[idx].present,
        !(parent == t0.root() && idx == IDX_SELFMAP),
        !t0.contains(child),
        t1.root() == t0.root(),
        t1.sub_idx() == t0.sub_idx(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c == child || t0.contains(c)),
        t1.node(child).empty(),
        t1.level(child) == t0.level(parent) - 1,
        t1.node(parent) == t0.node(parent).update(idx, interior_entry(child)),
        t1.level(parent) == t0.level(parent),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
        t1.xlate_base(child) == t0.entry_vpn_base(parent, idx),
        forall|m: PFN| m != child ==> #[trigger] t1.xlate_base(m) == t0.xlate_base(m),
        t1.va_map() == t0.va_map(),
    ensures
        t1.mapping_wf(),
{
    broadcast use lemma_node_struct_wf, lemma_node_level_bound;

    // Derive the facts the xlate_wf half needs - freshness, root liveness/base - HERE
    // (where the tree soup lives) so the sub-lemma contexts stay clean.
    assert(t0.contains(t0.root()));
    assert(t0.level(parent) <= ROOT_LEVEL);
    assert forall|n: PFN, i: nat| #[trigger] t0.interior_at(n, i) implies t0.entry(n, i).target
        != child by {
        assert(t0.node_wf(n));
    }
    lemma_link_child_xlate_wf::<V>(t0, t1, parent, idx, child);
    lemma_link_child_mapping_inv::<V>(t0, t1, parent, idx, child);
}

/// `node_wf` transfer for unlink, isolated to a SMALL proof context so the (heavy)
/// `node_wf` unfolding does not interact with the main lemma's large proof state -
/// the difference between a 4s and a >75s check. Given that present entries are
/// unchanged, surviving interior targets are still live (`!= child`), and levels
/// are preserved off `child`, a node that was well-formed in `t0` still is in `t1`.
#[verifier::rlimit(40)]
pub proof fn lemma_unlink_node_wf<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
    n: PFN,
)
    requires
        t0.node_wf(n),
        t0.node(n).wf(),
        t1.node(n).wf(),
        t1.contains(n),
        n != child,
        t1.sub_idx() == t0.sub_idx(),
        t1.entry(parent, idx) == entry_absent(),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)),
        forall|m: PFN, j: nat|
            (m != child && (m != parent || j != idx)) ==> #[trigger] t1.entry(m, j) == t0.entry(
                m,
                j,
            ),
        forall|m: PFN, j: nat| #[trigger] t1.interior_at(m, j) ==> t1.entry(m, j).target != child,
    ensures
        t1.node_wf(n),
{
    assert(t1.level(n) == t0.level(n));
    assert forall|i: nat|
        #![trigger t1.entry(n, i)]
        (i < ENTRIES && t1.node(n).e.dom().contains(i) && t1.entry(n, i).present) implies {
            let e = t1.entry(n, i);
            if t1.level(n) == 0 || e.leaf {
                t1.level(n) <= 2 && e.target % span(t1.level(n)) == 0
            } else {
                &&& t1.contains(e.target)
                &&& if t1.is_self_map(n, i) {
                    e.target == n
                } else {
                    t1.level(n) >= 1 && t1.level(e.target) == t1.level(n) - 1
                }
            }
        } by {
        if n == parent && i == idx {
            assert(t1.entry(parent, idx) == entry_absent());  // !present: antecedent is false
        } else {
            assert(t1.entry(n, i) == t0.entry(n, i));  // surviving slot is unchanged
            let e = t1.entry(n, i);
            if t1.level(n) != 0 && !e.leaf {
                assert(t1.interior_at(n, i));  // present interior
                assert(e.target != child);  // surviving target is live
                assert(t0.contains(e.target));  // t0.node_wf at i
                assert(t1.contains(e.target));  // contains-iff (target != child)
                assert(t1.is_self_map(n, i) == t0.is_self_map(n, i));  // level(n) unchanged
                assert(t1.level(e.target) == t0.level(e.target));  // target != child
            }
        }
    }
}

/// `links_wf` transfer for unlink, in its OWN small proof context: the main lemma
/// accumulates a large quantifier set (the whole tree argument), which makes even
/// discharging this grind. Taking only the RAW structural relationship (the main
/// lemma's own hypotheses, so the call discharges verbatim) and re-deriving the
/// per-entry facts here keeps the context small and the check fast.
#[verifier::rlimit(40)]
pub proof fn lemma_unlink_links_wf<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.contains(parent),
        idx < ENTRIES,
        t0.interior_at(parent, idx),
        t0.entry(parent, idx).target == child,
        t0.node(child).empty(),
        t1.store_wf(),
        t1.sub_idx() == t0.sub_idx(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)),
        t1.node(parent) == t0.node(parent).update(idx, entry_absent()),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
    ensures
        t1.links_wf(),
{
    broadcast use lemma_node_struct_wf, lemma_node_level_bound;

    assert(t0.node_wf(parent));
    assert(t0.contains(child));
    assert(t0.node(parent).e.dom().contains(idx));
    assert(t1.entry(parent, idx) == entry_absent());
    // entries unchanged off the absent slot and the removed child:
    assert forall|n: PFN, i: nat| (n != child && (n != parent || i != idx)) implies
        #[trigger] t1.entry(n, i) == t0.entry(n, i) by {
        if n == parent {
            assert(t1.node(parent).e[i] == t0.node(parent).e.insert(idx, entry_absent())[i]);
        }
    }
    assert(!t1.interior_at(parent, idx));
    // a t1 interior entry is an unchanged t0 interior entry:
    assert forall|n: PFN, i: nat| t1.interior_at(n, i) implies (#[trigger] t0.interior_at(n, i)
        && t1.entry(n, i) == t0.entry(n, i)) by {
        assert(t1.contains(n));  // => n != child
        assert(n != parent || i != idx);
    }
    // (parent,idx) is the unique t0 interior targeting child; hence no surviving
    // interior entry targets child.
    assert forall|n: PFN, i: nat| (#[trigger] t0.interior_at(n, i) && t0.entry(n, i).target == child)
        implies (n == parent && i == idx) by {
        assert(t0.interior_at(parent, idx) && t0.entry(parent, idx).target == child);
    }
    assert forall|n: PFN, i: nat| #[trigger] t1.interior_at(n, i) implies t1.entry(n, i).target
        != child by {
        assert(t0.interior_at(n, i) && t1.entry(n, i) == t0.entry(n, i));
    }
    // node_wf per node, in the isolated node-level context.
    assert forall|n: PFN| #[trigger] t1.contains(n) implies t1.node_wf(n) by {
        assert(t0.contains(n));  // contains-iff
        assert(t0.node_wf(n));  // t0.links_wf
        lemma_unlink_node_wf::<V>(t0, t1, parent, idx, child, n);
    }
}

/// In any well-formed (sub)tree the only interior edge that can target the root is
/// the full table's self-map; a subtree root has no incoming edge at all. Used to
/// show a relinked/unlinked child is never the (sub)root.
pub proof fn lemma_root_incoming_is_self_map<V: PtPage>(t: PageTablePerms<V>, n: PFN, i: nat)
    requires
        t.store_wf(),
        t.tree_inv(),
        t.interior_at(n, i),
        t.entry(n, i).target == t.root(),
    ensures
        t.is_self_map(n, i),
{
    broadcast use lemma_node_struct_wf, lemma_node_level_bound;

    let r = t.root();
    assert(t.node_wf(n));
    if t.sub_idx() is None {
        // full table: the self-map targets the root; injectivity makes it unique.
        assert(t.level(r) == ROOT_LEVEL);  // tree_inv: level(root) == root_level()
        assert(t.interior_at(r, IDX_SELFMAP) && t.entry(r, IDX_SELFMAP).target == r);
        assert(n == r && i == IDX_SELFMAP);  // injectivity
    } else {
        // subtree: no interior may target the root. `is_self_map` is false here, so
        // `node_wf` puts the root one level below `n`, then `n` (!= root) would need
        // a parent above ROOT_LEVEL - impossible.
        assert(!t.is_self_map(n, i));
        assert(t.level(n) >= 1 && t.level(r) == t.level(n) - 1);
        assert(t.level(r) == t.root_level() && t.root_level() == (ROOT_LEVEL - 1) as nat);
        assert(t.level(n) == ROOT_LEVEL);
        assert(n != r);
        let w = choose|g: PFN, j: nat|
            #![trigger t.interior_at(g, j)]
            t.interior_at(g, j) && t.entry(g, j).target == n;
        assert(t.node_wf(w.0));
        assert(!t.is_self_map(w.0, w.1));
        assert(t.level(w.0) == t.level(n) + 1);  // > ROOT_LEVEL, contradicting the bound
        assert(false);
    }
}

/// `tree_wf` (+ root) transfer for unlink, in its own small context. By injectivity
/// `(parent, idx)` was `child`'s only parent and an empty `child` is nobody's
/// parent, so the surviving interior entries are an injective, fully-connected
/// subset of `t0`'s.
#[verifier::rlimit(40)]
pub proof fn lemma_unlink_tree_wf<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.contains(parent),
        idx < ENTRIES,
        t0.interior_at(parent, idx),
        t0.entry(parent, idx).target == child,
        !(parent == t0.root() && idx == IDX_SELFMAP),
        t0.node(child).empty(),
        t1.store_wf(),
        t1.root() == t0.root(),
        t1.sub_idx() == t0.sub_idx(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)),
        t1.node(parent) == t0.node(parent).update(idx, entry_absent()),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
    ensures
        t1.tree_wf(),
        t1.contains(t1.root()),
        t1.level(t1.root()) == t1.root_level(),
{
    broadcast use lemma_node_struct_wf, lemma_node_level_bound;

    let r = t0.root();
    assert(t1.root_level() == t0.root_level() && t1.root_base() == t0.root_base());
    assert(t0.node_wf(parent));
    assert(t0.contains(child));
    assert(child != parent);
    // `child` is not the (sub)root: the only edge that can target the root is the
    // full table's self-map, and (parent, idx) is not it.
    assert(child != r) by {
        if child == r {
            lemma_root_incoming_is_self_map::<V>(t0, parent, idx);
            // is_self_map(parent, idx): sub_idx None, level(parent)==ROOT_LEVEL, idx==SELFMAP.
            assert(idx == IDX_SELFMAP && t0.level(parent) == t0.root_level());
            assert(parent == r);  // root-unique then forces parent == r
        }
    }
    assert(t0.node(parent).e.dom().contains(idx));
    assert forall|n: PFN, i: nat| (n != child && (n != parent || i != idx)) implies
        #[trigger] t1.entry(n, i) == t0.entry(n, i) by {
        if n == parent {
            assert(t1.node(parent).e[i] == t0.node(parent).e.insert(idx, entry_absent())[i]);
        }
    }
    assert(t1.entry(parent, idx) == entry_absent());
    assert(!t1.interior_at(parent, idx));
    assert forall|i: nat| !#[trigger] t0.interior_at(child, i) by {}
    assert forall|i: nat| !#[trigger] t1.interior_at(child, i) by {}
    assert forall|n: PFN, i: nat| t1.interior_at(n, i) implies (#[trigger] t0.interior_at(n, i)
        && t1.entry(n, i) == t0.entry(n, i) && n != child) by {
        assert(t1.contains(n));  // => n != child
        assert(n != parent || i != idx);  // else contradicts !t1.interior_at(parent, idx)
    }
    // root stays live, at its level.
    assert(t1.contains(r));
    assert(t1.level(r) == t1.root_level());

    // --- tree_wf, clause by clause -----------------------------------
    assert forall|n: PFN| #![trigger t1.contains(n)]
        t1.contains(n) && t1.level(n) == t1.root_level() implies n == r by {
        assert(t0.contains(n));
    }
    // the self-map (full table only) survives: it is interior in t0 (so != the
    // cleared (parent, idx) slot, since the requires excludes the self-map).
    assert(t1.self_map_inv()) by {
        if t1.sub_idx() is None {
            assert(t0.interior_at(r, IDX_SELFMAP) && t0.entry(r, IDX_SELFMAP).target == r);
            assert(!(parent == r && idx == IDX_SELFMAP));
            assert(t1.interior_at(r, IDX_SELFMAP));
            assert(t1.entry(r, IDX_SELFMAP) == t0.entry(r, IDX_SELFMAP));
        }
    }
    // injectivity: t1's interior entries are a subset of t0's (unchanged), so inherit it.
    assert forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
        (#[trigger] t1.interior_at(n1, i1) && #[trigger] t1.interior_at(n2, i2) && t1.entry(
            n1,
            i1,
        ).target == t1.entry(n2, i2).target) implies (n1 == n2 && i1 == i2) by {
        assert(t0.interior_at(n1, i1) && t1.entry(n1, i1) == t0.entry(n1, i1));
        assert(t0.interior_at(n2, i2) && t1.entry(n2, i2) == t0.entry(n2, i2));
    }
    // connectivity: each surviving node (!= root) keeps its (unchanged) t0 parent.
    assert forall|c: PFN| #![trigger t1.contains(c)]
        (t1.contains(c) && c != r) implies exists|n: PFN, i: nat|
        #[trigger] t1.interior_at(n, i) && t1.entry(n, i).target == c by {
        assert(t0.contains(c) && c != child);
        let w = choose|n: PFN, i: nat|
            #![trigger t0.interior_at(n, i)]
            t0.interior_at(n, i) && t0.entry(n, i).target == c;
        // w is not in `child` (empty) and not (parent, idx) (it targets c != child),
        // so w is an unchanged t1 interior entry.
        assert(w.0 != child);  // `child` has no interior entries
        assert(w.0 != parent || w.1 != idx);  // (parent,idx) targets child != c
        assert(t1.entry(w.0, w.1) == t0.entry(w.0, w.1));
        assert(t1.interior_at(w.0, w.1) && t1.entry(w.0, w.1).target == c);
    }
    assert(t1.tree_wf());
}

/// `ad_pinned` transfer for unlink, in its own small context: the cleared slot is
/// now absent (vacuously pinned) and every other present entry of a live node is
/// unchanged from `t0`, where it was pinned.
#[verifier::rlimit(40)]
pub proof fn lemma_unlink_ad<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.contains(parent),
        idx < ENTRIES,
        t1.store_wf(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)),
        t1.node(parent) == t0.node(parent).update(idx, entry_absent()),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
    ensures
        t1.ad_pinned(),
{
    broadcast use lemma_node_struct_wf;

    assert(t0.node(parent).e.dom().contains(idx));
    assert(t1.entry(parent, idx) == entry_absent());
    assert forall|n: PFN, i: nat| (n != child && (n != parent || i != idx)) implies
        #[trigger] t1.entry(n, i) == t0.entry(n, i) by {
        if n == parent {
            assert(t1.node(parent).e[i] == t0.node(parent).e.insert(idx, entry_absent())[i]);
        }
    }
    assert forall|n: PFN, i: nat|
        (t1.contains(n) && i < ENTRIES && t1.node(n).e.dom().contains(i)) implies entry_pinned(
            #[trigger] t1.entry(n, i),
        ) by {
        if n != parent || i != idx {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }
}

/// The framework's preservation argument for unlinking and freeing an EMPTY
/// child: if `t1` is `t0` with `parent[idx]` (an interior link to `child`) cleared
/// and `child` removed from the store, then `t1` is still a valid tree. Kept THIN
/// - each conjunct of `tree_inv` is discharged by a sub-lemma with its own small
/// proof context, so no single check drowns in the combined quantifier set.
#[verifier::rlimit(40)]
pub proof fn lemma_unlink_free_preserves_tree_inv<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.contains(parent),
        idx < ENTRIES,
        t0.interior_at(parent, idx),
        t0.entry(parent, idx).target == child,
        !(parent == t0.root() && idx == IDX_SELFMAP),
        t0.node(child).empty(),
        t1.store_wf(),
        t1.root() == t0.root(),
        t1.sub_idx() == t0.sub_idx(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)),
        t1.node(parent) == t0.node(parent).update(idx, entry_absent()),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
    ensures
        t1.tree_inv(),
{
    lemma_unlink_links_wf::<V>(t0, t1, parent, idx, child);
    lemma_unlink_ad::<V>(t0, t1, parent, idx, child);
    lemma_unlink_tree_wf::<V>(t0, t1, parent, idx, child);
}

/// `mapping_inv` for unlink: `child` is empty (no leaves) and the cleared slot is
/// absent, so `leaf_at`/bases are unchanged; recorded witnesses (!= child) survive.
#[verifier::rlimit(40)]
pub proof fn lemma_unlink_mapping_inv<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.mapping_inv(),
        t0.contains(parent),
        idx < ENTRIES,
        t0.interior_at(parent, idx),
        t0.node(child).empty(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)),
        t1.node(parent) == t0.node(parent).update(idx, entry_absent()),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
        forall|m: PFN| m != child ==> #[trigger] t1.xlate_base(m) == t0.xlate_base(m),
        t1.va_map() == t0.va_map(),
    ensures
        t1.mapping_inv(),
{
    broadcast use lemma_node_struct_wf;

    assert(t0.node(parent).e.dom().contains(idx));
    assert(t1.entry(parent, idx) == entry_absent());
    assert forall|n: PFN, i: nat| (n != child && (n != parent || i != idx)) implies
        #[trigger] t1.entry(n, i) == t0.entry(n, i) by {
        if n == parent {
            assert(t1.node(parent).e[i] == t0.node(parent).e.insert(idx, entry_absent())[i]);
        }
    }
    // leaf_at is unchanged: `child` empty (and gone in t1), the cleared slot is absent.
    assert forall|n: PFN, i: nat| #[trigger] t1.leaf_at(n, i) == t0.leaf_at(n, i) by {
        if n == child {
            assert(!t1.leaf_at(child, i));
            assert(!t0.leaf_at(child, i));
        } else if n == parent && i == idx {
            assert(!t1.leaf_at(parent, idx));
            assert(!t0.leaf_at(parent, idx));
        } else {
            assert(t1.entry(n, i) == t0.entry(n, i));
        }
    }
    assert forall|n: PFN, i: nat| t0.leaf_at(n, i) implies (n != child && #[trigger] t1.entry(n, i)
        == t0.entry(n, i) && t1.entry_vpn_base(n, i) == t0.entry_vpn_base(n, i)) by {
        if n == child {
            assert(!t0.leaf_at(child, i));  // child empty
        } else if n == parent && i == idx {
            assert(!t0.leaf_at(parent, idx));  // interior, not leaf
        }
    }

    assert forall|b: VPage| #[trigger] t1.va_map().dom().contains(b) implies {
        let m = t1.va_map()[b];
        &&& in_user_region(b)
        &&& b % m.size.pages() == 0
        &&& m.frame % m.size.pages() == 0
        &&& exists|n: PFN| t1.records_leaf(b, m, n, pt_index(b, level_of_size(m.size)))
    } by {
        let m = t0.va_map()[b];
        let ii = pt_index(b, level_of_size(m.size));
        let w = choose|n: PFN| t0.records_leaf(b, m, n, ii);
        assert(t0.records_leaf(b, m, w, ii));
        assert(t0.leaf_at(w, ii) && w != child);
        assert(t1.records_leaf(b, m, w, ii));
    }
    assert forall|n: PFN, i: nat|
        (#[trigger] t1.leaf_at(n, i) && in_user_region(t1.entry_vpn_base(n, i)))
            implies t1.va_map().dom().contains(t1.entry_vpn_base(n, i)) by {
        assert(t0.leaf_at(n, i));
    }
}

/// `free_child`'s mapping-layer preservation: clearing the parent slot and removing
/// the empty `child` preserves `mapping_wf`. Thin combiner (soup lesson).
pub proof fn lemma_unlink_child_preserves_mapping_wf<V: PtPage>(
    t0: PageTablePerms<V>,
    t1: PageTablePerms<V>,
    parent: PFN,
    idx: nat,
    child: PFN,
)
    requires
        t0.store_wf(),
        t0.tree_inv(),
        t0.mapping_wf(),
        t0.contains(parent),
        idx < ENTRIES,
        t0.interior_at(parent, idx),
        t0.entry(parent, idx).target == child,
        !(parent == t0.root() && idx == IDX_SELFMAP),
        t0.node(child).empty(),
        t1.root() == t0.root(),
        t1.sub_idx() == t0.sub_idx(),
        forall|c: PFN| #[trigger] t1.contains(c) <==> (c != child && t0.contains(c)),
        t1.node(parent) == t0.node(parent).update(idx, entry_absent()),
        forall|m: PFN| m != child && m != parent ==> #[trigger] t1.node(m) == t0.node(m),
        forall|m: PFN| m != child ==> #[trigger] t1.level(m) == t0.level(m),
        forall|m: PFN| m != child ==> #[trigger] t1.xlate_base(m) == t0.xlate_base(m),
        t1.va_map() == t0.va_map(),
    ensures
        t1.mapping_wf(),
{
    broadcast use lemma_node_struct_wf, lemma_node_level_bound;

    // surviving interiors don't target `child`: (parent, idx) was the unique one
    // (injectivity), and it is now absent.
    assert(t0.contains(t0.root()));
    assert(t0.root() != child) by {
        if child == t0.root() {
            lemma_root_incoming_is_self_map::<V>(t0, parent, idx);
            assert(idx == IDX_SELFMAP && t0.level(parent) == t0.root_level());
            assert(parent == t0.root());  // root-unique
        }
    }
    assert(t0.node(parent).e.dom().contains(idx));
    assert(t1.entry(parent, idx) == entry_absent());
    assert(!t1.interior_at(parent, idx));
    assert forall|n: PFN, i: nat| (n != child && (n != parent || i != idx)) implies
        #[trigger] t1.entry(n, i) == t0.entry(n, i) by {
        if n == parent {
            assert(t1.node(parent).e[i] == t0.node(parent).e.insert(idx, entry_absent())[i]);
        }
    }
    assert forall|n: PFN, i: nat| (#[trigger] t0.interior_at(n, i) && t0.entry(n, i).target == child)
        implies (n == parent && i == idx) by {
        assert(t0.interior_at(parent, idx) && t0.entry(parent, idx).target == child);
    }
    assert forall|n: PFN, i: nat| #[trigger] t1.interior_at(n, i) implies t1.entry(n, i).target
        != child by {
        assert(t1.contains(n));
        assert(n != parent || i != idx);
        assert(t1.entry(n, i) == t0.entry(n, i));
        assert(t0.interior_at(n, i));
    }
    // xlate_wf: t1's interiors/nodes are a subset of t0's with unchanged entries and
    // bases (reusing the entry congruence above), and no surviving link targets child.
    assert(t1.interiors_permissive()) by {
        assert forall|n: PFN, i: nat| #[trigger] t1.interior_at(n, i) implies permissive(
            t1.entry(n, i),
        ) by {
            assert(t1.contains(n) && (n != parent || i != idx));
            assert(t1.entry(n, i) == t0.entry(n, i) && t0.interior_at(n, i));
        }
    }
    assert(t1.xlate_base_aligned()) by {
        assert forall|n: PFN| #[trigger] t1.contains(n) implies t1.xlate_base(n) % span(
            (t1.level(n) + 1) as nat,
        ) == 0 by {
            assert(t0.contains(n) && t1.xlate_base(n) == t0.xlate_base(n) && t1.level(n) == t0.level(
                n,
            ));
        }
    }
    assert(t1.xlate_base_consistent()) by {
        assert(t1.root_base() == t0.root_base() && t0.xlate_base(t0.root()) == t0.root_base());
        assert(t1.xlate_base(t1.root()) == t1.root_base());
        assert forall|p: PFN, i: nat| (#[trigger] t1.interior_at(p, i) && !t1.is_self_map(p, i))
            implies t1.xlate_base(t1.entry(p, i).target) == t1.entry_vpn_base(p, i) by {
            assert(t1.contains(p) && (p != parent || i != idx) && t1.entry(p, i) == t0.entry(p, i));
            assert(t0.interior_at(p, i) && !t0.is_self_map(p, i));
            let tgt = t0.entry(p, i).target;
            assert(t1.xlate_base(tgt) == t0.xlate_base(tgt) && t1.entry_vpn_base(p, i)
                == t0.entry_vpn_base(p, i));
        }
    }
    lemma_unlink_mapping_inv::<V>(t0, t1, parent, idx, child);
}

/// `wf` and `xlate_wf` read only `pages_`/`root_`/`xlate_base_`, never `va_map_`, so
/// recording a mapping (a `va_map` change) preserves them. Proven once by congruence
/// over the structural accessors, used by `map`/`unmap`.
#[verifier::rlimit(40)]
pub proof fn lemma_va_map_irrelevant<V: PtPage>(t: PageTablePerms<V>, t2: PageTablePerms<V>)
    requires
        t.store_wf(),
        t.wf(),
        t.xlate_wf(),
        t2.pages() == t.pages(),
        t2.root() == t.root(),
        t2.sub_idx() == t.sub_idx(),
        forall|n: PFN| #[trigger] t2.xlate_base(n) == t.xlate_base(n),
    ensures
        t2.wf(),
        t2.xlate_wf(),
{
    broadcast use lemma_node_struct_wf;

    assert(t2.root_level() == t.root_level() && t2.root_base() == t.root_base());
    assert forall|p: PFN| #[trigger] t2.contains(p) == t.contains(p) by {}
    assert forall|p: PFN| #[trigger] t2.level(p) == t.level(p) by {}
    assert forall|p: PFN| #[trigger] t2.node(p) == t.node(p) by {}
    assert forall|n: PFN, i: nat| #[trigger] t2.entry(n, i) == t.entry(n, i) by {}
    assert forall|n: PFN, i: nat| #[trigger] t2.interior_at(n, i) == t.interior_at(n, i) by {}
    assert forall|n: PFN, i: nat| #[trigger] t2.is_self_map(n, i) == t.is_self_map(n, i) by {}
    assert forall|n: PFN, i: nat| #[trigger] t2.entry_vpn_base(n, i) == t.entry_vpn_base(n, i) by {}

    assert(t2.store_wf()) by {
        assert forall|p: PFN| t2.contains(p) implies (#[trigger] t2.pages()[p].wf()
            && t2.pages()[p].pfn() == p) by {
            assert(t.contains(p));
        }
    }
    assert(t2.tree_inv()) by {
        assert(t2.contains(t2.root()));
        assert(t2.links_wf()) by {
            assert forall|n: PFN| t2.contains(n) implies #[trigger] t2.node_wf(n) by {
                assert(t.contains(n) && t.node_wf(n));
            }
        }
        assert(t2.tree_wf()) by {
            assert forall|n: PFN| #![trigger t2.contains(n)]
                t2.contains(n) && t2.level(n) == t2.root_level() implies n == t2.root() by {
                assert(t.contains(n));
            }
            assert(t2.self_map_inv()) by {
                if t2.sub_idx() is None {
                    assert(t.interior_at(t.root(), IDX_SELFMAP) && t.entry(
                        t.root(),
                        IDX_SELFMAP,
                    ).target == t.root());
                }
            }
            assert forall|n1: PFN, i1: nat, n2: PFN, i2: nat|
                (#[trigger] t2.interior_at(n1, i1) && #[trigger] t2.interior_at(n2, i2) && t2.entry(
                    n1,
                    i1,
                ).target == t2.entry(n2, i2).target) implies (n1 == n2 && i1 == i2) by {
                assert(t.interior_at(n1, i1) && t.interior_at(n2, i2));
            }
            assert forall|c: PFN| #![trigger t2.contains(c)]
                (t2.contains(c) && c != t2.root()) implies exists|n: PFN, i: nat|
                #[trigger] t2.interior_at(n, i) && t2.entry(n, i).target == c by {
                assert(t.contains(c));
                let w = choose|n: PFN, i: nat|
                    #![trigger t.interior_at(n, i)]
                    t.interior_at(n, i) && t.entry(n, i).target == c;
                assert(t2.interior_at(w.0, w.1) && t2.entry(w.0, w.1).target == c);
            }
        }
        assert(t2.ad_pinned()) by {
            assert forall|n: PFN, i: nat|
                (t2.contains(n) && i < ENTRIES && t2.node(n).e.dom().contains(i)) implies entry_pinned(
                    #[trigger] t2.entry(n, i),
                ) by {}
        }
    }
    assert(t2.interiors_permissive()) by {
        assert forall|n: PFN, i: nat| #[trigger] t2.interior_at(n, i) implies permissive(
            t2.entry(n, i),
        ) by {
            assert(t.interior_at(n, i));
        }
    }
    assert(t2.xlate_base_consistent()) by {
        assert(t.xlate_base(t.root()) == t.root_base());  // t.xlate_wf
        assert(t2.xlate_base(t2.root()) == t2.root_base());
        assert forall|p: PFN, i: nat| (#[trigger] t2.interior_at(p, i) && !t2.is_self_map(p, i))
            implies t2.xlate_base(t2.entry(p, i).target) == t2.entry_vpn_base(p, i) by {
            assert(t.interior_at(p, i) && !t.is_self_map(p, i));
        }
    }
    assert(t2.xlate_base_aligned()) by {
        assert forall|n: PFN| #[trigger] t2.contains(n) implies t2.xlate_base(n) % span(
            (t2.level(n) + 1) as nat,
        ) == 0 by {
            assert(t.contains(n));
        }
    }
}

/// A permissive interior entry leaves the (x86) identity accumulator unchanged.
pub proof fn lemma_permissive_keeps_top(e: Entry)
    requires
        permissive(e),
    ensures
        combine_step(perm_identity(), e) == perm_identity(),
{
}

/// With the identity accumulator, the leaf alone decides the permission.
pub proof fn lemma_top_combine_is_leaf_only(e: Entry)
    ensures
        combine_step(perm_identity(), e) == leaf_only_perm(e),
{
}

/// THE A/D-pin fact (per entry). Under the pinned invariant the MMU's only
/// permitted write (raise ACCESSED) leaves the entry unchanged, so the sole
/// concurrent writer is neutralized and exclusive `&mut` reasoning is sound.
pub proof fn lemma_entry_pin_accessed_noop(e: Entry)
    requires
        entry_pinned(e),
        e.present,
    ensures
        (Entry { accessed: true, ..e }) == e,
{
}

} // verus!
