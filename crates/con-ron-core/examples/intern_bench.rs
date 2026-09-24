//! `intern_bench` — the P4a micro-benchmark (DESIGN.md §8, task #97-P4a).
//!
//! Interns a base of leaves and then N distinct `app` nodes over them, and
//! reports nanoseconds per intern and bytes per node (peak RSS over the node
//! count).  An *example*, not a crate module: Charon never sees it, and it is
//! therefore outside DESIGN.md §3.4 — it may loop and print.
//!
//!     cargo run --release --example intern_bench -- [nodes] [base]
//!
//! The release profile is the shipped one, `overflow-checks = true` included
//! (workspace `Cargo.toml`), because that is the configuration the Aeneas
//! model describes.
//!
//! **What it measures.**  `base` leaves (`bvar i`) into the persistent tier,
//! then `nodes` applications `app(leaf[i], leaf[j])` over the pairs `(i, j)`
//! in row-major order, each one distinct, each one a cons-table miss followed
//! by an append: the worst case for the store, and the operation the parser
//! and the checker spend most of their time in.  A second pass over the same
//! pairs measures the *hit* path, which is what `whnf` and `infer` do.
//!
//! Peak RSS is `VmHWM` from `/proc/self/status`, i.e. the high-water mark of
//! the whole process, leaves and base vector included; at ten million nodes
//! those are noise.

use con_ron_core::arena::handle::EIdx;
use con_ron_core::arena::store::ENodeView;
use con_ron_core::arena::store::EStore;
use con_ron_core::ron::hashmap::Dup;
use std::time::Instant;
use con_ron_core::arena::store::PersTier;

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

fn take<T>(r: Result<T, con_ron_core::kernel::core_types::CheckError>) -> T {
    match r {
        Ok(x) => x,
        Err(_) => panic!("the store declined a node"),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let nodes: usize = if args.len() > 1 { args[1].parse().unwrap() } else { 10_000_000 };
    let base: usize = if args.len() > 2 { args[2].parse().unwrap() } else { 4096 };
    assert!(base * base >= nodes, "the base is too small for {nodes} distinct apps");

    let rss0 = vm_hwm_kb();
    let mut st = EStore::empty();
    // the store is owned here and read through the empty stand-in tier (not
    // `frozen`), so every persistent read goes to the store's
    // own tier and this one is never consulted (task #97-P6-6b).
    let pers: &PersTier = &PersTier::empty();

    let t_base = Instant::now();
    let mut leaves: Vec<EIdx> = Vec::with_capacity(base);
    for i in 0..base {
        leaves.push(take(st.intern(pers, ENodeView::BVar(i as u64))));
    }
    let base_ns = t_base.elapsed().as_nanos();

    // --- the miss path: `nodes` distinct applications ----------------------
    let t = Instant::now();
    let mut k = 0usize;
    let mut last = leaves[0].dup2();
    while k < nodes {
        let i = k / base;
        let j = k % base;
        last = take(st.intern(pers, ENodeView::App(leaves[i].dup2(), leaves[j].dup2())));
        k += 1;
    }
    let miss = t.elapsed();
    let rss1 = vm_hwm_kb();

    // --- the hit path: the same nodes again --------------------------------
    let t = Instant::now();
    let mut k = 0usize;
    while k < nodes {
        let i = k / base;
        let j = k % base;
        last = take(st.intern(pers, ENodeView::App(leaves[i].dup2(), leaves[j].dup2())));
        k += 1;
    }
    let hit = t.elapsed();

    let total_nodes = st.node_count(pers);
    let rss_bytes = (rss1 - rss0) * 1024;

    println!("arena-core intern_bench");
    println!(
        "  sizeof AppNode {} B, EIdx {} B, derived word 8 B, AList<AppNode,EIdx> {} B",
        std::mem::size_of::<con_ron_core::arena::store::AppNode>(),
        std::mem::size_of::<EIdx>(),
        std::mem::size_of::<con_ron_core::ron::hashmap::AList<con_ron_core::arena::store::AppNode, EIdx>>()
    );
    println!("  base leaves            {base} in {} ns ({} ns/node)", base_ns, base_ns / base as u128);
    println!("  app nodes interned     {nodes}");
    println!("  store node count       {total_nodes}");
    println!(
        "  miss (intern new)      {:.3} s  =  {:.1} ns/intern",
        miss.as_secs_f64(),
        miss.as_nanos() as f64 / nodes as f64
    );
    println!(
        "  hit  (re-intern)       {:.3} s  =  {:.1} ns/intern",
        hit.as_secs_f64(),
        hit.as_nanos() as f64 / nodes as f64
    );
    println!("  peak RSS delta         {} kB", rss1 - rss0);
    println!(
        "  bytes per app node     {:.1}",
        rss_bytes as f64 / nodes as f64
    );
    // keep `last` alive so nothing above is optimised away
    println!("  (last handle word      {})", last.word);
}
