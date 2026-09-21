//! `arena-parse` — the P4e measurement driver (DESIGN.md §8, task #97-P4e
//! part 1).
//!
//!     cargo run --release --example arena_parse -- FILE.ndjson [--skip-modelled] [--tree]
//!
//! Parses a lean4export stream into ONE `EStore` and reports what the Lean
//! twin's `runPipelineM` reports: the FILE's declaration record count (the
//! modeller's generated records subtracted), the three stores' node counts,
//! and peak RSS.  An *example*, not a crate module: Charon never sees it, so
//! it is outside DESIGN.md §3.4 and may loop, print and read files.
//!
//! **It is the twin's pipeline, minus the fold** (`Arena/Main.lean:150-175`):
//! `builtinPreludeE`, then the stream's chunks, then `preparePrelude` — three
//! steps against one store, which is the point of the persistent tier (the
//! prelude's nodes and the stream's are hash-consed together).  There is no
//! fold to run: P2c/P2d and P4c/P4d are what come next.
//!
//! **The modeller is the declining stub** (`frontend::types::DeclineModeller`),
//! as it is in the twin, so a mutual or nested block stops the parse with
//! `declined: in-process model of <block>` — on `Init` that is line 78 503,
//! `Lean.Syntax`.  `--skip-modelled` is con-leche's own `CON_LECHE_INMODEL=0`,
//! i.e. `inModel := false`: the block is pushed bare and the parse runs to the
//! end of the file, which is the measurement build the twin's `Init` numbers
//! were taken on.
//!
//! **The reads are interleaved with the parse**, in 4 MiB chunks
//! (`export_c::CHUNK_SIZE`): this is `parseExportHandleD`'s loop, whose pure
//! meaning is `parse_chunks` of the chunks the handle hands out
//! (con-leche's `parseChunks_eq_parseExportD`).  The twin's driver reads the
//! whole file into a chunk list first and its own task section flags that as
//! the one memory problem it found — 0.33 GB of `Init`'s 0.82 GB peak — so
//! the RSS this prints is the store plus the parse tables and one 4 MiB
//! buffer, and is the number to compare with the twin's 0.49 GB rather than
//! with its 0.82.
//!
//! **`--tree` runs the same loop against `con_ron_core::frontend::export_c`**,
//! the `Expr`-tree parser this one is the handle twin of, so that the price of
//! hash-consing every node is a measured Rust-against-Rust number on the same
//! machine and not a quoted one.  It reports the declaration count and peak
//! RSS; there is no store to count nodes in, which is exactly the difference
//! the rewrite exists to make.

use arena_core::arena::monad::AState;
use arena_core::arena::store::EStore;
use arena_core::frontend::export_c;
use arena_core::frontend::prelude::builtin_prelude_e;
use arena_core::frontend::prepare;
use arena_core::frontend::types::DeclineModeller;
use con_ron_core::kernel::core_types::CheckError;
use std::io::Read;
use std::time::Instant;
use arena_core::arena::store::PersTier;

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

fn cps(v: &[u32]) -> String {
    v.iter().filter_map(|c| char::from_u32(*c)).collect()
}

/// The twin's `CheckError.message` and `CheckError.exitCode`, in one.
fn render(e: &CheckError) -> (String, i32) {
    match e {
        CheckError::NotImplemented(w) => (format!("declined: {}", cps(w)), 2),
        CheckError::Invalid(w) => (format!("invalid: {}", cps(w)), 1),
        CheckError::Internal(w) => (format!("internal: {}", cps(w)), 3),
        CheckError::Native(w) => (format!("native: {}", cps(w)), 3),
    }
}

/// Thousands separators, so that a six-million node count is readable.
fn group(n: u64) -> String {
    let s = n.to_string();
    let b = s.as_bytes();
    let mut out = String::new();
    for (i, c) in b.iter().enumerate() {
        if i > 0 && (b.len() - i) % 3 == 0 {
            out.push(' ');
        }
        out.push(*c as char);
    }
    out
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut path: Option<String> = None;
    let mut in_model = true;
    let mut tree = false;
    for a in args.iter() {
        if a == "--skip-modelled" {
            in_model = false;
        } else if a == "--tree" {
            tree = true;
        } else if a.starts_with("--") {
            eprintln!("arena-parse: unknown flag {}", a);
            std::process::exit(3);
        } else {
            path = Some(a.clone());
        }
    }
    let path = match path {
        Some(p) => p,
        None => {
            eprintln!("usage: arena-parse FILE.ndjson [--skip-modelled] [--tree]");
            std::process::exit(3);
        }
    };

    if tree {
        tree_parse(&path, in_model);
        return;
    }

    let t0 = Instant::now();
    // one `AState` for the whole run: since task #97-P4e part 2 the parser's
    // projection rewrite runs `ExprOps`' memoised walks, so the frontend takes
    // the checker state and not the bare store (DESIGN.md §8.4: the twin's one
    // monad is `StateT AState (Except CheckError)` throughout).
    let mut ar = AState::init(EStore::empty());
    // `shared_on` is false here, so every persistent read goes to the store's
    // own tier and this one is never consulted (task #97-P6-6b).
    let pers: &PersTier = &PersTier::empty();
    // The reserved-name pins, exactly as the driver interns them (task
    // #97-P6-4a): before the parse, while the scratch tier is still closed.
    match arena_core::arena::pins::intern_reserved_pins(pers, &mut ar) {
        Ok(()) => (),
        Err(_) => {
            eprintln!("arena_parse: the reserved-name pins do not intern");
            std::process::exit(3);
        }
    }
    let md = DeclineModeller {};

    // 1. the built-in prelude, into the same store
    let pre = match builtin_prelude_e(pers, &md, &mut ar) {
        Ok(p) => p,
        Err((e, line)) => {
            let (m, c) = render(&e);
            eprintln!("arena-parse: the built-in prelude: {} (line {})", m, line);
            std::process::exit(c);
        }
    };
    let (pre_e, pre_l, pre_n) = (
        ar.store.node_count(pers),
        ar.store.ls().node_count(pers),
        ar.store.ns().node_count(pers),
    );

    // 2. the stream, read and parsed in lockstep
    let mut f = match std::fs::File::open(&path) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("arena-parse: {}: {}", path, e);
            std::process::exit(3);
        }
    };
    let mut st = match export_c::state_d_init(pers, &mut ar.store, in_model, false) {
        Ok(s) => s,
        Err(e) => {
            let (m, c) = render(&e);
            eprintln!("arena-parse: {}", m);
            std::process::exit(c);
        }
    };
    let mut buf = vec![0u8; export_c::CHUNK_SIZE];
    let mut carry: Vec<u8> = Vec::new();
    let mut line_no: u64 = 0;
    let mut total: u64 = 0;
    let mut bytes: u64 = 0;
    let mut failed: Option<(CheckError, u64)> = None;
    loop {
        let n = match f.read(&mut buf[..]) {
            Ok(n) => n,
            Err(e) => {
                eprintln!("arena-parse: {}: {}", path, e);
                std::process::exit(3);
            }
        };
        if n == 0 {
            break;
        }
        bytes += n as u64;
        match export_c::chunk_step(pers, &md, &mut ar, &mut st, carry, line_no, total, &buf[..n]) {
            Ok((c2, l, t)) => {
                carry = c2;
                line_no = l;
                total = t;
            }
            Err(e) => {
                failed = Some(e);
                carry = Vec::new();
                break;
            }
        }
    }
    let r = match failed {
        Some(e) => Err(e),
        None => export_c::chunk_finish(pers, &md, &mut ar, st, &carry[..], line_no),
    };

    let (n_e, n_l, n_n) = (
        ar.store.node_count(pers),
        ar.store.ls().node_count(pers),
        ar.store.ns().node_count(pers),
    );
    let wall = t0.elapsed();

    match r {
        Err((e, line)) => {
            let (m, code) = render(&e);
            println!("arena-parse: {}", path);
            println!("  stopped at line {}: {}", group(line), m);
            println!("  bytes read           {}", group(bytes));
            println!(
                "  store                {} expression, {} level, {} name nodes",
                group(n_e as u64),
                group(n_l as u64),
                group(n_n as u64)
            );
            println!(
                "  of which the prelude {} / {} / {} (before the stream)",
                group(pre_e as u64),
                group(pre_l as u64),
                group(pre_n as u64)
            );
            println!("  wall                 {:.2} s", wall.as_secs_f64());
            println!("  peak RSS             {:.2} GB", vm_hwm_kb() as f64 / 1048576.0);
            std::process::exit(code);
        }
        Ok(res) => {
            // 3. `preparePrelude`, as the twin's `runPipelineM` runs it
            let records = res.decls.len() as u64 - res.gen_records;
            // `prepare_d` takes the whole state since task #97-P4d: step 2 of
            // `preparePrelude` is the real ground hoist, whose trigger set is
            // the kernel's pinned `Nat` operation names.
            let mut ast = ar;
            let prepared = match prepare::prepare_d(pers, &mut ast, pre, res.decls) {
                Ok(p) => p,
                Err(e) => {
                    let (m, c) = render(&e);
                    eprintln!("arena-parse: {}", m);
                    std::process::exit(c);
                }
            };
            let ar = ast.store;
            let (n_e, n_l, n_n) =
                (ar.node_count(pers), ar.ls().node_count(pers), ar.ns().node_count(pers));
            let wall = t0.elapsed();
            println!("arena-parse: {}", path);
            println!("  declarations parsed  {}", group(records));
            println!("  lines                {}", group(line_no));
            println!("  bytes read           {}", group(bytes));
            println!(
                "  prepared stream      {} records ({} synthesised from the prelude)",
                group(prepared.decls.len() as u64),
                group(prepared.synthesised)
            );
            println!(
                "  store                {} expression, {} level, {} name nodes",
                group(n_e as u64),
                group(n_l as u64),
                group(n_n as u64)
            );
            println!(
                "  of which the prelude {} / {} / {} (before the stream)",
                group(pre_e as u64),
                group(pre_l as u64),
                group(pre_n as u64)
            );
            println!("  wall                 {:.2} s", wall.as_secs_f64());
            println!("  peak RSS             {:.2} GB", vm_hwm_kb() as f64 / 1048576.0);
        }
    }
}

/// A modeller that declines every block, for `con_ron_core`'s parser: the
/// `DeclineModeller` of the other crate, with the same sentence.
struct TreeDecline;

impl con_ron_core::frontend::in_model_rec::Modeller for TreeDecline {
    fn generate(
        &self,
        _ctx: &con_ron_core::frontend::in_model_rec::ModelCtx,
        _b: &con_ron_core::frontend::in_model_rec::BlockRec,
    ) -> Result<Vec<con_ron_core::kernel::env::Declaration>, Vec<u32>> {
        Err("the arena's in-process modeller is not ported yet"
            .chars()
            .map(|c| c as u32)
            .collect())
    }
}

/// `--tree`: the same read loop against `con_ron_core::frontend::export_c`,
/// the `Expr`-tree parser, for the side-by-side.
fn tree_parse(path: &str, in_model: bool) {
    use con_ron_core::frontend::export_c as tc;
    let t0 = Instant::now();
    let md = TreeDecline;
    let pre = match con_ron_core::frontend::prelude::builtin_prelude_e(&md) {
        Ok(p) => p,
        Err((e, line)) => {
            let (m, c) = render(&e);
            eprintln!("arena-parse --tree: the built-in prelude: {} (line {})", m, line);
            std::process::exit(c);
        }
    };
    let mut f = match std::fs::File::open(path) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("arena-parse --tree: {}: {}", path, e);
            std::process::exit(3);
        }
    };
    let mut st = tc::state_d_init(in_model, false);
    let mut buf = vec![0u8; tc::CHUNK_SIZE];
    let mut carry: Vec<u8> = Vec::new();
    let mut line_no: u64 = 0;
    let mut total: u64 = 0;
    let mut bytes: u64 = 0;
    let mut failed: Option<(CheckError, u64)> = None;
    loop {
        let n = match f.read(&mut buf[..]) {
            Ok(n) => n,
            Err(e) => {
                eprintln!("arena-parse --tree: {}: {}", path, e);
                std::process::exit(3);
            }
        };
        if n == 0 {
            break;
        }
        bytes += n as u64;
        match tc::chunk_step(&md, &mut st, carry, line_no, total, &buf[..n]) {
            Ok((c2, l, t)) => {
                carry = c2;
                line_no = l;
                total = t;
            }
            Err(e) => {
                failed = Some(e);
                carry = Vec::new();
                break;
            }
        }
    }
    let r = match failed {
        Some(e) => Err(e),
        None => tc::chunk_finish(&md, st, &carry[..], line_no),
    };
    match r {
        Err((e, line)) => {
            let (m, code) = render(&e);
            println!("arena-parse --tree: {}", path);
            println!("  stopped at line {}: {}", group(line), m);
            println!("  peak RSS             {:.2} GB", vm_hwm_kb() as f64 / 1048576.0);
            std::process::exit(code);
        }
        Ok(res) => {
            let records = res.decls.len() as u64 - res.gen_records;
            let prepared = con_ron_core::frontend::prepare::prepare_d(pre, res.decls);
            let wall = t0.elapsed();
            println!("arena-parse --tree: {}", path);
            println!("  declarations parsed  {}", group(records));
            println!("  lines                {}", group(line_no));
            println!("  bytes read           {}", group(bytes));
            println!(
                "  prepared stream      {} records ({} synthesised from the prelude)",
                group(prepared.decls.len() as u64),
                group(prepared.synthesised)
            );
            println!("  wall                 {:.2} s", wall.as_secs_f64());
            println!("  peak RSS             {:.2} GB", vm_hwm_kb() as f64 / 1048576.0);
        }
    }
}
