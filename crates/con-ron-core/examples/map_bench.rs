//! `map_bench` — `ron::HashMap` against `ron::HashMap2` on the ARENA's key
//! shapes (DESIGN.md §8, task #97-P6-4b).
//!
//!     cargo run --release --example map_bench -- [scale]
//!
//! An *example*, not a crate module: Charon never sees it, so it is outside
//! DESIGN.md §3.4 and may loop, print and use `std`.  The release profile is
//! the shipped one, `overflow-checks = true` included.
//!
//! **The three shapes, and why these three.**  Task #97-P6-4b instrumented
//! `con-ron-arena` on `Init` and counted 1.23 G `get`s, 0.63 G `insert`s and
//! **36.1 M `clear`s that walked 2.94 G buckets**.  The three benchmarks below
//! are those three numbers' workloads:
//!
//! 1. `cons` — an `AppNode` (two `u32` handles) cons table: N distinct
//!    inserts, then N hits, then N misses.  This is `ETables::find`/`push`,
//!    the intern path, and it is where the arena's memory goes.
//! 2. `cache` — an `EIdx → EIdx` memo under the checker's real rhythm: fill a
//!    few hundred rows, probe them, **clear**, repeat.  This is `inst1_clear`
//!    and its ten siblings, and `Caches::reset`'s eleven tables; the chained
//!    map pays `O(capacity)` per round here and the epoch map pays `O(1)`.
//! 3. `names` — a `StrNode` (a `Vec<u32>` of code points behind a prefix
//!    handle) cons table: the one key shape that is not scalar.
//!
//! Peak RSS is `VmHWM` from `/proc/self/status`; each map's block runs in its
//! own process phase and prints the delta it caused, so the two are
//! comparable.

use con_ron_core::arena::handle::EIdx;
use con_ron_core::arena::handle::NIdx;
use con_ron_core::arena::store::AppNode;
use con_ron_core::arena::store::StrNode;
use con_ron_core::ron::hashmap::HashMap;
use con_ron_core::ron::hashmap2::HashMap2;
use std::time::Instant;

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

fn rss_kb() -> u64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    for line in s.lines() {
        if let Some(rest) = line.strip_prefix("VmRSS:") {
            let t: Vec<&str> = rest.split_whitespace().collect();
            if !t.is_empty() {
                return t[0].parse::<u64>().unwrap_or(0);
            }
        }
    }
    0
}

fn e(w: u32) -> EIdx {
    EIdx { word: w }
}

fn app(i: usize, base: usize) -> AppNode {
    AppNode { f: e((i % base) as u32), a: e((i / base) as u32) }
}

fn str_node(i: usize) -> StrNode {
    // three or four code points, as a real `Name` component has
    let mut s: Vec<u32> = Vec::with_capacity(4);
    s.push(97 + (i % 26) as u32);
    s.push(97 + ((i / 26) % 26) as u32);
    s.push(97 + ((i / 676) % 26) as u32);
    if i % 3 == 0 {
        s.push(48 + (i % 10) as u32);
    }
    StrNode { pre: NIdx { word: (i % 97) as u32 }, s }
}

fn ns(d: std::time::Duration, n: usize) -> f64 {
    d.as_secs_f64() * 1e9 / (n as f64)
}

// ---------------------------------------------------------------------------
// 1. the cons table
// ---------------------------------------------------------------------------

fn cons_chained(n: usize, base: usize) -> (f64, f64, f64, u64) {
    let r0 = rss_kb();
    let mut m: HashMap<AppNode, EIdx> = HashMap::new();
    let t = Instant::now();
    for i in 0..n {
        m.insert(app(i, base), e(i as u32));
    }
    let ins = ns(t.elapsed(), n);
    let peak = rss_kb().saturating_sub(r0);
    let t = Instant::now();
    let mut acc: u64 = 0;
    for i in 0..n {
        match m.get(&app(i, base)) {
            None => acc += 1,
            Some(v) => acc += v.word as u64,
        }
    }
    let hit = ns(t.elapsed(), n);
    let t = Instant::now();
    for i in 0..n {
        match m.get(&app(i + n, base)) {
            None => acc += 1,
            Some(v) => acc += v.word as u64,
        }
    }
    let miss = ns(t.elapsed(), n);
    std::hint::black_box(acc);
    std::hint::black_box(&m);
    (ins, hit, miss, peak)
}

fn cons_open(n: usize, base: usize) -> (f64, f64, f64, u64) {
    let r0 = rss_kb();
    let mut m: HashMap2<AppNode, EIdx> = HashMap2::new();
    let t = Instant::now();
    for i in 0..n {
        m.insert(app(i, base), e(i as u32));
    }
    let ins = ns(t.elapsed(), n);
    let peak = rss_kb().saturating_sub(r0);
    let t = Instant::now();
    let mut acc: u64 = 0;
    for i in 0..n {
        match m.get(&app(i, base)) {
            None => acc += 1,
            Some(v) => acc += v.word as u64,
        }
    }
    let hit = ns(t.elapsed(), n);
    let t = Instant::now();
    for i in 0..n {
        match m.get(&app(i + n, base)) {
            None => acc += 1,
            Some(v) => acc += v.word as u64,
        }
    }
    let miss = ns(t.elapsed(), n);
    std::hint::black_box(acc);
    std::hint::black_box(&m);
    (ins, hit, miss, peak)
}

// ---------------------------------------------------------------------------
// 2. the per-call memo cache: fill, probe, CLEAR, repeat
// ---------------------------------------------------------------------------
//
// `rounds` rounds of `rows` inserts and `3 * rows` probes (two thirds of them
// misses, which is what the instrumented `Init` run measured: 1.23 G gets,
// 0.58 G hits).  One round in ten is a large one, because that is the
// asymmetry task #97-P6-1's `RESET_KEEP_SLACK` exists for: one big
// `instantiate1` leaves an array every later small call then walks.

fn cache_chained(rounds: usize, rows: usize) -> (f64, u64) {
    let mut m: HashMap<EIdx, EIdx> = HashMap::new();
    let mut acc: u64 = 0;
    let t = Instant::now();
    for r in 0..rounds {
        let k = if r % 10 == 0 { rows * 16 } else { rows };
        for i in 0..k {
            m.insert(e((i * 2654435761 % 4000000) as u32), e(i as u32));
        }
        for i in 0..(3 * k) {
            match m.get(&e((i * 2654435761 % 4000000) as u32)) {
                None => acc += 1,
                Some(v) => acc += v.word as u64,
            }
        }
        m.clear();
    }
    let per = t.elapsed().as_secs_f64() * 1e9 / (rounds as f64);
    std::hint::black_box(acc);
    (per, m.capacity() as u64)
}

fn cache_open(rounds: usize, rows: usize) -> (f64, u64) {
    let mut m: HashMap2<EIdx, EIdx> = HashMap2::new();
    let mut acc: u64 = 0;
    let t = Instant::now();
    for r in 0..rounds {
        let k = if r % 10 == 0 { rows * 16 } else { rows };
        for i in 0..k {
            m.insert(e((i * 2654435761 % 4000000) as u32), e(i as u32));
        }
        for i in 0..(3 * k) {
            match m.get(&e((i * 2654435761 % 4000000) as u32)) {
                None => acc += 1,
                Some(v) => acc += v.word as u64,
            }
        }
        m.clear();
    }
    let per = t.elapsed().as_secs_f64() * 1e9 / (rounds as f64);
    std::hint::black_box(acc);
    (per, m.capacity() as u64)
}

// ---------------------------------------------------------------------------
// 3. the name cons table
// ---------------------------------------------------------------------------

fn names_chained(n: usize) -> (f64, f64) {
    let mut m: HashMap<StrNode, NIdx> = HashMap::new();
    let t = Instant::now();
    for i in 0..n {
        m.insert(str_node(i), NIdx { word: i as u32 });
    }
    let ins = ns(t.elapsed(), n);
    let t = Instant::now();
    let mut acc: u64 = 0;
    for i in 0..n {
        match m.get(&str_node(i)) {
            None => acc += 1,
            Some(v) => acc += v.word as u64,
        }
    }
    let get = ns(t.elapsed(), n);
    std::hint::black_box(acc);
    std::hint::black_box(&m);
    (ins, get)
}

fn names_open(n: usize) -> (f64, f64) {
    let mut m: HashMap2<StrNode, NIdx> = HashMap2::new();
    let t = Instant::now();
    for i in 0..n {
        m.insert(str_node(i), NIdx { word: i as u32 });
    }
    let ins = ns(t.elapsed(), n);
    let t = Instant::now();
    let mut acc: u64 = 0;
    for i in 0..n {
        match m.get(&str_node(i)) {
            None => acc += 1,
            Some(v) => acc += v.word as u64,
        }
    }
    let get = ns(t.elapsed(), n);
    std::hint::black_box(acc);
    std::hint::black_box(&m);
    (ins, get)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let scale: usize = if args.len() > 1 { args[1].parse().unwrap_or(1) } else { 1 };

    let n = 4_000_000 * scale;
    let base = 2048;
    let rounds = 20_000 * scale;
    let rows = 200;
    let names = 400_000 * scale;

    println!("map_bench: slot sizes");
    println!(
        "  AList<AppNode, EIdx>   {} B     Slot<AppNode, EIdx>   {} B",
        std::mem::size_of::<con_ron_core::ron::hashmap::AList<AppNode, EIdx>>(),
        std::mem::size_of::<con_ron_core::ron::hashmap2::Slot<AppNode, EIdx>>()
    );
    println!(
        "  AList<EIdx, EIdx>      {} B     Slot<EIdx, EIdx>      {} B",
        std::mem::size_of::<con_ron_core::ron::hashmap::AList<EIdx, EIdx>>(),
        std::mem::size_of::<con_ron_core::ron::hashmap2::Slot<EIdx, EIdx>>()
    );
    println!(
        "  AList<EIdx, bool>      {} B     Slot<EIdx, bool>      {} B",
        std::mem::size_of::<con_ron_core::ron::hashmap::AList<EIdx, bool>>(),
        std::mem::size_of::<con_ron_core::ron::hashmap2::Slot<EIdx, bool>>()
    );

    println!("\nmap_bench: 1. cons table, {} distinct AppNode keys", n);
    let (i1, h1, m1, p1) = cons_chained(n, base);
    println!(
        "  chained   insert {:7.1} ns   hit {:7.1} ns   miss {:7.1} ns   +{} KB ({:.1} B/entry)",
        i1,
        h1,
        m1,
        p1,
        (p1 as f64) * 1024.0 / (n as f64)
    );
    let (i2, h2, m2, p2) = cons_open(n, base);
    println!(
        "  open      insert {:7.1} ns   hit {:7.1} ns   miss {:7.1} ns   +{} KB ({:.1} B/entry)",
        i2,
        h2,
        m2,
        p2,
        (p2 as f64) * 1024.0 / (n as f64)
    );

    println!(
        "\nmap_bench: 2. memo cache, {} rounds of {} rows (every tenth {}x), cleared each round",
        rounds, rows, 16
    );
    let (c1, cap1) = cache_chained(rounds, rows);
    println!("  chained   {:9.0} ns/round   final capacity {}", c1, cap1);
    let (c2, cap2) = cache_open(rounds, rows);
    println!("  open      {:9.0} ns/round   final capacity {}", c2, cap2);
    println!("  ratio     {:.2}x", c1 / c2);

    println!("\nmap_bench: 3. name cons table, {} distinct StrNode keys", names);
    let (ni1, ng1) = names_chained(names);
    println!("  chained   insert {:7.1} ns   get {:7.1} ns", ni1, ng1);
    let (ni2, ng2) = names_open(names);
    println!("  open      insert {:7.1} ns   get {:7.1} ns", ni2, ng2);

    println!("\nmap_bench: process peak RSS {} KB", vm_hwm_kb());
}
