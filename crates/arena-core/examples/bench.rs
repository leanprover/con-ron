//! `bench` — the Rust twin of `proof/ConRon/Arena/Bench.lean`
//! (DESIGN.md §8, task #97-P4b).
//!
//!     cargo run --release --example bench
//!
//! The same four measurements as `con-ron-arena-bench`, on the same four
//! shapes, at the same sizes, printed in the same order — so that a
//! Rust-vs-Lean ratio can be read off line by line.  An *example*, not a
//! crate module: Charon never sees it, and it is therefore outside DESIGN.md
//! §3.4 — it may loop, print and unwrap.  The release profile is the shipped
//! one, `overflow-checks = true` included, because that is the configuration
//! the Aeneas model describes.
//!
//! **The four shapes**, from `Bench.lean`'s own note:
//!
//! * **the spine** `((… ((bvar 1) x) x) …) x`, 50 000 `app` nodes deep — no
//!   sharing at all, so a walk over it does 50 000 interns and the memo never
//!   hits.  The worst case for the memo and the honest baseline for "what does
//!   one pass cost".
//! * **the telescope** `∀ ty, ∀ ty, … (bvar 10000)`, 10 000 binders — the
//!   shape `openPisAtFvars` walks one binder at a time, and the shape whose
//!   cursor moves under every binder.
//! * **the DAG tower** `t₀ = bvar 1`, `t_{k+1} = app t_k t_k`, k = 24 — 25
//!   arena nodes denoting a tree of 2^24 = 16.7 M nodes.  **The measurement
//!   the memo exists for.**  Without a memo this line never finishes, which is
//!   a better regression test than an assertion.
//! * **con-leche's task #215 workload** — peel a 1000-binder telescope one
//!   binder at a time, which is the call pattern that made `instantiate1`
//!   memoized in the first place.
//!
//! **The stack.**  The spine is 50 000 nodes deep and every twin is a
//! recursion, so the walk is 50 000 Rust frames.  `con-ron` already runs its
//! checker on a thread with a 1 GB stack (`bin/con-ron.rs`, `pool.rs`) for
//! exactly this reason; this benchmark does the same.  The Lean twin does not
//! need to: Lean's own runtime grows its stack.

use arena_core::arena::expr_ops::*;
use arena_core::arena::handle::{EIdx, LsIdx, NIdx};
use arena_core::arena::monad::{
    intern_e, intern_l_node, intern_ls_node, intern_n_node, view, AState,
};
use arena_core::arena::store::{ENodeView, EStore, LNodeView, NNodeView};
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::expr;
use con_ron_core::kernel::prop_when;
use con_ron_core::ron::hashmap::Dup;
use std::time::Instant;

/// `Bench.lean:44 benchFuel` — the deepest shape is 50 000 nodes, so 200 000
/// is a comfortable margin and no run below ever reaches it.
const BENCH_FUEL: u64 = 200_000;

/// 1 GB, as `con-ron`'s own checker threads use.
const STACK_BYTES: usize = 1 << 30;

fn take<T>(r: Result<T, CheckError>) -> T {
    match r {
        Ok(x) => x,
        Err(_) => panic!("the arena declined an operation"),
    }
}

fn vm_hwm_kb() -> u64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    for line in s.lines() {
        if let Some(rest) = line.strip_prefix("VmHWM:") {
            let t: Vec<&str> = rest.split_whitespace().collect();
            if !t.is_empty() {
                return t[0].parse::<u64>().unwrap_or(0);
            }
        }
    }
    0
}

fn cp(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

/// `Bench.lean:48-53 mkSpine` — a left-nested application spine of `n` `app`
/// nodes over a fixed argument.
fn mk_spine(st: &mut AState, arg: &EIdx, n: u64, acc: EIdx) -> EIdx {
    let mut a = acc;
    for _ in 0..n {
        a = take(intern_e(st, ENodeView::App(a, arg.dup2())));
    }
    a
}

/// `Bench.lean:57-62 mkTele` — a `∀`-telescope of `n` binders over a fixed
/// domain, innermost body first.
fn mk_tele(st: &mut AState, dom: &EIdx, n: u64, body: EIdx) -> EIdx {
    let mut b = body;
    for _ in 0..n {
        b = take(intern_e(
            st,
            ENodeView::ForallE(dom.dup2(), b, expr::binder_meta(prop_when::never())),
        ));
    }
    b
}

/// `Bench.lean:66-70 mkTower` — the DAG tower `t_{k+1} = app t_k t_k`: `k`
/// arena nodes, `2^k` tree nodes.
fn mk_tower(st: &mut AState, k: u64, t: EIdx) -> EIdx {
    let mut x = t;
    for _ in 0..k {
        x = take(intern_e(st, ENodeView::App(x.dup2(), x)));
    }
    x
}

/// `Bench.lean:74-83 Fixture` — the arena the runs share, and the handles they
/// name.
struct Fixture {
    spine: EIdx,
    plain: EIdx,
    tele: EIdx,
    peel: EIdx,
    tower: EIdx,
    sub: EIdx,
    fv: EIdx,
    u_name: NIdx,
    us_zero: LsIdx,
}

/// `Bench.lean:94-112 build` — build the four shapes.  Chosen so that no
/// cutoff fires at the root: the spine's head is `bvar 1` and its argument an
/// `fvar`, the telescope's body is `bvar n`, the tower's leaf is `bvar 1`.
fn build(st: &mut AState, spine_n: u64, tele_n: u64, tower_k: u64) -> Fixture {
    let anon = take(intern_n_node(st, NNodeView::Anonymous));
    let u_name = take(intern_n_node(st, NNodeView::Str(anon.dup2(), cp("u"))));
    let zero = take(intern_l_node(st, LNodeView::Zero));
    let pu = take(intern_l_node(st, LNodeView::Param(u_name.dup2())));
    let us_zero = take(intern_ls_node(st, vec![zero.dup2()]));
    let s0 = take(intern_e(st, ENodeView::Sort(zero.dup2())));
    let su = take(intern_e(st, ENodeView::Sort(pu.dup2())));
    let fv = take(intern_e(st, ENodeView::FVar(0, su.dup2())));
    let b1 = take(intern_e(st, ENodeView::BVar(1)));
    let spine = mk_spine(st, &fv, spine_n, b1.dup2());
    let plain = mk_spine(st, &s0, spine_n, b1.dup2());
    let bn = take(intern_e(st, ENodeView::BVar(tele_n)));
    let tele = mk_tele(st, &su, tele_n, bn);
    let bp = take(intern_e(st, ENodeView::BVar(1000)));
    let peel = mk_tele(st, &s0, 1000, bp);
    let tower = mk_tower(st, tower_k, b1);
    let sub = take(intern_e(st, ENodeView::Const(u_name.dup2(), us_zero.dup2())));
    Fixture { spine, plain, tele, peel, tower, sub, fv, u_name, us_zero }
}

/// `Bench.lean:120-127 peelPis` — **con-leche's task #215 workload**:
/// `openPisAtFvars` opens a `∀`-telescope ONE BINDER AT A TIME, so a telescope
/// of `n` binders costs `n` instantiations over a body that is still `O(n)`
/// wide.
fn peel_pis(st: &mut AState, fuel: u64, arg: &EIdx, n: u64, h: &EIdx) -> u64 {
    let mut cur = h.dup2();
    for _ in 0..n {
        match take(view(st, &cur)) {
            ENodeView::ForallE(_, body, _) => {
                cur = take(instantiate1_fast(st, fuel, &body, arg, 0));
            }
            _ => return cur.word as u64,
        }
    }
    cur.word as u64
}

/// `Bench.lean:131-144 timed` — run one action against the state, time it and
/// print.
fn timed<F>(label: &str, st: &mut AState, f: F)
where
    F: FnOnce(&mut AState) -> Result<u64, CheckError>,
{
    let t0 = Instant::now();
    let r = f(st);
    let dt = t0.elapsed();
    match r {
        Ok(n) => println!(
            "  {label}: {:.4} ms   (result {n})",
            dt.as_secs_f64() * 1000.0
        ),
        Err(_) => println!("  {label}: FAILED after {:.4} ms", dt.as_secs_f64() * 1000.0),
    }
}

fn run() {
    let spine_n: u64 = 50_000;
    let tele_n: u64 = 10_000;
    let tower_k: u64 = 24;
    let rss0 = vm_hwm_kb();
    println!("con-ron arena ExprOps micro-benchmark (Rust)");
    println!(
        "  spine {spine_n} apps, telescope {tele_n} binders, DAG tower 2^{tower_k}"
    );

    let mut st = AState::init(EStore::empty());
    let t0 = Instant::now();
    let fx = build(&mut st, spine_n, tele_n, tower_k);
    let t_build = t0.elapsed();
    println!(
        "  intern (all four shapes): {:.4} ms, {} nodes",
        t_build.as_secs_f64() * 1000.0,
        st.store.node_count()
    );

    println!("the spine (no sharing: the memo never hits)");
    timed("instantiate1Fast  ", &mut st, |s| {
        instantiate1_fast(s, BENCH_FUEL, &fx.spine, &fx.sub, 1).map(|r| r.word as u64)
    });
    timed("abstract1Fast     ", &mut st, |s| {
        abstract1_fast(s, BENCH_FUEL, &fx.spine, 0, 0).map(|r| r.word as u64)
    });
    timed("instLPFast        ", &mut st, |s| {
        inst_lp_fast(
            s,
            BENCH_FUEL,
            &vec![fx.u_name.dup2()],
            &fx.us_zero,
            &fx.spine,
        )
        .map(|r| r.word as u64)
    });
    timed("bvarBoundMemo     ", &mut st, |s| {
        bvar_bound_memo(s, BENCH_FUEL, &fx.spine)
    });
    timed("sizeB             ", &mut st, |s| {
        size_b(s, BENCH_FUEL, &fx.spine)
    });
    println!("  arena now {} nodes", st.store.node_count());

    println!("the telescope (the cursor moves under every binder)");
    timed("instantiate1Fast  ", &mut st, |s| {
        instantiate1_fast(s, BENCH_FUEL, &fx.tele, &fx.sub, 0).map(|r| r.word as u64)
    });
    timed("abstract1Fast     ", &mut st, |s| {
        abstract1_fast(s, BENCH_FUEL, &fx.tele, 0, 0).map(|r| r.word as u64)
    });
    timed("instLPFast        ", &mut st, |s| {
        inst_lp_fast(s, BENCH_FUEL, &vec![fx.u_name.dup2()], &fx.us_zero, &fx.tele)
            .map(|r| r.word as u64)
    });
    timed("liftLooseBVarsFast", &mut st, |s| {
        lift_loose_bvars_fast(s, BENCH_FUEL, 1, 0, &fx.tele).map(|r| r.word as u64)
    });
    println!("  arena now {} nodes", st.store.node_count());

    println!("the DAG tower ({tower_k} arena nodes, 2^{tower_k} tree nodes)");
    println!("  -- without the memo every one of these is exponential");
    timed("instantiate1Fast  ", &mut st, |s| {
        instantiate1_fast(s, BENCH_FUEL, &fx.tower, &fx.sub, 1).map(|r| r.word as u64)
    });
    timed("instantiate1LiftF ", &mut st, |s| {
        instantiate1_lift_fast(s, BENCH_FUEL, &fx.tower, &fx.sub, 1).map(|r| r.word as u64)
    });
    timed("instLPFast        ", &mut st, |s| {
        inst_lp_fast(
            s,
            BENCH_FUEL,
            &vec![fx.u_name.dup2()],
            &fx.us_zero,
            &fx.tower,
        )
        .map(|r| r.word as u64)
    });
    timed("bvarBoundMemo     ", &mut st, |s| {
        bvar_bound_memo(s, BENCH_FUEL, &fx.tower)
    });
    println!("  arena now {} nodes", st.store.node_count());

    println!("con-leche's task #215 workload: peel a 1000-binder telescope");
    println!("  one binder at a time (`openPisAtFvars`) -- 1000 instantiations");
    timed("peelPis x1000     ", &mut st, |s| {
        Ok(peel_pis(s, BENCH_FUEL, &fx.fv, 1000, &fx.peel))
    });
    println!("  arena now {} nodes", st.store.node_count());

    println!("the cutoffs (the subject is answered without a walk)");
    timed("instantiate1 (cut)", &mut st, |s| {
        instantiate1_fast(s, BENCH_FUEL, &fx.tele, &fx.sub, 5000).map(|r| r.word as u64)
    });
    timed("abstract1    (cut)", &mut st, |s| {
        abstract1_fast(s, BENCH_FUEL, &fx.plain, 7, 0).map(|r| r.word as u64)
    });
    timed("instLP       (cut)", &mut st, |s| {
        inst_lp_fast(
            s,
            BENCH_FUEL,
            &vec![fx.u_name.dup2()],
            &fx.us_zero,
            &fx.plain,
        )
        .map(|r| r.word as u64)
    });
    println!("the same three on a subject the cutoff does NOT answer");
    timed("instantiate1 (run)", &mut st, |s| {
        instantiate1_fast(s, BENCH_FUEL, &fx.plain, &fx.sub, 1).map(|r| r.word as u64)
    });
    timed("abstract1    (run)", &mut st, |s| {
        abstract1_fast(s, BENCH_FUEL, &fx.spine, 0, 0).map(|r| r.word as u64)
    });
    timed("instLP       (run)", &mut st, |s| {
        inst_lp_fast(
            s,
            BENCH_FUEL,
            &vec![fx.u_name.dup2()],
            &fx.us_zero,
            &fx.spine,
        )
        .map(|r| r.word as u64)
    });
    println!("  arena now {} nodes", st.store.node_count());
    println!("  peak RSS delta {} kB", vm_hwm_kb() - rss0);
}

fn main() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(run)
        .unwrap()
        .join()
        .unwrap();
}
