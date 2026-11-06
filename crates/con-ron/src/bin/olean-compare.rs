//! `olean-compare` — the `.olean` reader against lean4export (task #142), upstream's
//! `OleanCompare.lean` over the arena.
//!
//! ```text
//! olean-compare [--constant=NAME]... EXPORT.ndjson SEARCHPATH MODULE...
//! olean-compare --views SEARCHPATH MODULE...
//! ```
//!
//! Parses a lean4export stream of `MODULE...` and the same modules' import closure
//! into ONE store, and compares the two record arrays as maps from a record's first
//! declared name.  Over one hash-consed store a handle IS the term, so the comparison
//! needs no walk of a term, where upstream's needs `Expr.beq`'s memo.  Two orders
//! lean4export takes from hash-map iteration are normalised: the record order (hence
//! the map) and the order of the recursors inside a block.
//!
//! `--views` reads every module of the closure at its home (`read_all_views`) and
//! compares each view with `read_view`'s; exit 0, or the first failure's exit code.
//!
//! A development tool, outside the theorems, like `crate::driver`.

use std::collections::HashMap;
use std::process::ExitCode;

use con_ron::driver;
use con_ron::olean_fs;
use con_ron::olean_fs::StdFs;
use con_ron::render;

use con_ron_core::arena::canon;
use con_ron_core::arena::env::{IConstantInfo, IDeclaration};
use con_ron_core::arena::handle::NIdx;
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::store::PersTier;
use con_ron_core::frontend::export_c;
use con_ron_core::frontend::olean::{closure, files, module, records, spec, view};
use con_ron_core::frontend::olean::view::OLeanLevel;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env as cenv;

/// con-leche: OleanCompare.lean:38-45 normalize
/// The first declared name of a record, as text; the recursors of a block sorted by
/// name, as a list of positions.
fn rec_order(pers: &PersTier, st: &AState, block: &[IConstantInfo]) -> Vec<usize> {
    let is_rec = |c: &IConstantInfo| matches!(c, IConstantInfo::RecInfo(..));
    let mut rest: Vec<usize> = (0..block.len()).filter(|i| !is_rec(&block[*i])).collect();
    let mut recs: Vec<usize> = (0..block.len()).filter(|i| is_rec(&block[*i])).collect();
    recs.sort_by_key(|i| driver::name_of(pers, &st.store, &con_ron_core::arena::env::i_constant_info_name(&block[*i])));
    rest.append(&mut recs);
    rest
}

/// con-leche: OleanCompare.lean:77-85 declEq
/// Two records, field by field, by handle.
fn decl_eq(pers: &PersTier, st: &AState, a: &IDeclaration, b: &IDeclaration) -> bool {
    use con_ron_core::ron::hashmap::Eq2;
    use IDeclaration::*;
    match (a, b) {
        (AxiomDecl(v), AxiomDecl(w)) => canon::i_constant_val_beq(v, w),
        (DefnDecl(v, e, h), DefnDecl(w, e2, h2)) => {
            canon::i_constant_val_beq(v, w) && e.eq2(e2) && cenv::reducibility_hint_beq(h, h2)
        }
        (ThmDecl(v, e), ThmDecl(w, e2)) => canon::i_constant_val_beq(v, w) && e.eq2(e2),
        (OpaqueDecl(v, e), OpaqueDecl(w, e2)) => canon::i_constant_val_beq(v, w) && e.eq2(e2),
        (IndDecl(x, n), IndDecl(y, m)) => {
            let ox = rec_order(pers, st, x);
            let oy = rec_order(pers, st, y);
            n == m
                && x.len() == y.len()
                && ox.iter().zip(oy.iter()).all(|(i, j)| canon::i_constant_info_beq(&x[*i], &y[*j]))
        }
        (QuotDecl(k, v), QuotDecl(k2, w)) => {
            std::mem::discriminant(k) == std::mem::discriminant(k2) && canon::i_constant_val_beq(v, w)
        }
        _ => false,
    }
}

/// con-leche: OleanCompare.lean:116-119 toMap
/// The records by first name, and how many shared one.
fn to_map(ds: &[IDeclaration]) -> (HashMap<u32, usize>, usize) {
    let mut m: HashMap<u32, usize> = HashMap::new();
    let mut dup = 0usize;
    for (i, d) in ds.iter().enumerate() {
        let names: Vec<NIdx> = con_ron_core::arena::env::i_declaration_names(d);
        let k = match names.first() {
            Some(n) => n.word,
            None => u32::MAX,
        };
        if m.contains_key(&k) {
            dup += 1;
        } else {
            m.insert(k, i);
        }
    }
    (m, dup)
}

/// con-leche: OleanCompare.lean:121-124 viewsEq
/// A view's constants by the checker's equality.
fn views_eq(a: &spec::ModDecoded, b: &spec::ModDecoded) -> bool {
    a.is_module == b.is_module
        && spec::imports_beq(&a.imports, &b.imports)
        && a.constants.len() == b.constants.len()
        && a.constants.iter().zip(b.constants.iter()).all(|(x, y)| module::entry_same(x, y))
}

/// con-leche: none — the rendering of a failure's exit, `driver::exit_code` as a process code
fn fail_with(e: &CheckError) -> u8 {
    eprintln!("{}", driver::message(e));
    driver::exit_code(e)
}

/// con-leche: OleanCompare.lean:127-144 runViews
/// `--views`: every module of the closure.
fn run_views(sp: &[String], mods: &[String]) -> u8 {
    let pers: &PersTier = &PersTier::empty();
    let mut st = AState::empty();
    let req = match olean_fs::OleanRequest::new(sp, mods, &[]) {
        Ok(r) => r,
        Err(m) => {
            eprintln!("{}", m);
            return 3;
        }
    };
    let (roots, _) = match req.intern(pers, &mut st) {
        Ok(p) => p,
        Err(e) => return fail_with(&e),
    };
    let pk = match spec::olean_pins(pers, &mut st.store) {
        Ok(p) => p,
        Err(e) => return fail_with(&e),
    };
    let order = match closure::closure_order(&StdFs, &pk, pers, &mut st.store, &req.search_path, &roots) {
        Ok(o) => o,
        Err(e) => return fail_with(&e),
    };
    for m in &order {
        let (v, _) = match files::read_all_views(&StdFs, &pk, pers, &mut st.store, &req.search_path, m) {
            Ok(x) => x,
            Err(e) => return fail_with(&e),
        };
        for level in [OLeanLevel::Exported, OLeanLevel::Server, OLeanLevel::Private] {
            let d = match files::read_view(&StdFs, &pk, pers, &mut st.store, &req.search_path, m, &level) {
                Ok(d) => d,
                Err(e) => return fail_with(&e),
            };
            if !views_eq(&d, view::all_views_at(&v, &level)) {
                eprintln!(
                    "module {}: the {} view differs from the home's",
                    driver::name_of(pers, &st.store, m),
                    render::name_str(&con_ron_core::kernel::name::anonymous())
                );
                return 3;
            }
        }
    }
    println!("{} modules: every view read, one memo, agrees", order.len());
    0
}

/// con-leche: OleanCompare.lean:146-151 internalName
/// Lean's `Name.isInternal`: lean4export's default roots leave out the constants so
/// named, which the reader starts from, so a record only the reader has must be so
/// named.
fn internal_name(pers: &PersTier, st: &AState, n: u32) -> bool {
    let shown = driver::name_of(pers, &st.store, &NIdx::of_word(n));
    shown.split('.').any(|c| c.starts_with('_') || c.starts_with("\u{ab}_"))
}

/// con-leche: OleanCompare.lean:153-207 main
/// The record for record comparison.
fn run_compare(file: &str, sp: &[String], mods: &[String], constants: &[String]) -> u8 {
    let pers: &PersTier = &PersTier::empty();
    let mut st = AState::empty();
    let t0 = std::time::Instant::now();
    let js = match driver::parse_export_stream_d(pers, &mut st, file, export_c::CHUNK_SIZE) {
        Err(e) => {
            eprintln!("stream: {}", e);
            return 3;
        }
        Ok((Err((e, l)), _)) => {
            eprintln!("stream: {} at line {}", driver::message(&e), l);
            return 3;
        }
        Ok((Ok(r), _)) => r.decls,
    };
    let t1 = t0.elapsed().as_millis();
    let req = match olean_fs::OleanRequest::new(sp, mods, constants) {
        Ok(r) => r,
        Err(m) => {
            eprintln!("{}", m);
            return 3;
        }
    };
    let (roots, cs) = match req.intern(pers, &mut st) {
        Ok(p) => p,
        Err(e) => return fail_with(&e),
    };
    let os = match records::read_oleans(&StdFs, pers, &mut st.store, &req.search_path, &roots, &cs) {
        Err((e, l)) => {
            eprintln!("oleans: {} at record {}", driver::message(&e), l);
            return 3;
        }
        Ok(r) => r.decls,
    };
    let t2 = t0.elapsed().as_millis();
    println!("stream: {} records ({} ms); oleans: {} records ({} ms)", js.len(), t1, os.len(), t2 - t1);
    let (jm, jd) = to_map(&js);
    let (om, od) = to_map(&os);
    println!("duplicate keys: stream {}, oleans {}", jd, od);
    let mut bad = 0usize;
    let mut shown = 0usize;
    for (k, i) in &jm {
        match om.get(k) {
            None => {
                bad += 1;
                if shown < 20 {
                    println!("only in the stream: {}", driver::name_of(pers, &st.store, &NIdx::of_word(*k)));
                    shown += 1;
                }
            }
            Some(j) => {
                if !decl_eq(pers, &st, &js[*i], &os[*j]) {
                    bad += 1;
                    if shown < 20 {
                        println!("differs: {}", driver::name_of(pers, &st.store, &NIdx::of_word(*k)));
                        shown += 1;
                    }
                }
            }
        }
    }
    let mut extra = 0usize;
    for k in om.keys() {
        if !jm.contains_key(k) {
            if constants.is_empty() && internal_name(pers, &st, *k) {
                extra += 1;
            } else {
                bad += 1;
                if shown < 40 {
                    println!("only in the oleans: {}", driver::name_of(pers, &st.store, &NIdx::of_word(*k)));
                    shown += 1;
                }
            }
        }
    }
    let count_diff = js.len() + extra != os.len();
    println!("{} records under internal names, which the export's default leaves out", extra);
    println!(
        "{} stream keys, {} olean keys, {} differences, {} duplicate keys, {} / {} records",
        jm.len(),
        om.len(),
        bad,
        jd + od,
        js.len(),
        os.len()
    );
    if bad == 0 && jd == 0 && od == 0 && !count_diff {
        0
    } else {
        1
    }
}

/// con-leche: OleanCompare.lean:153-207 main
/// The entry point: one thread with the checker's stack, as the binary's.
fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let h = std::thread::Builder::new().stack_size(driver::STACK_BYTES).spawn(move || {
        let (flags, args): (Vec<String>, Vec<String>) =
            argv.into_iter().partition(|s| s.starts_with("--constant="));
        let constants: Vec<String> =
            flags.iter().map(|s| s["--constant=".len()..].to_string()).collect();
        let split = |sp: &str| -> Vec<String> {
            sp.split(':').filter(|d| !d.is_empty()).map(|d| d.to_string()).collect()
        };
        if args.len() >= 3 && args[0] == "--views" {
            run_views(&split(&args[1]), &args[2..])
        } else if args.len() >= 3 {
            run_compare(&args[0], &split(&args[1]), &args[2..], &constants)
        } else {
            eprintln!("usage: olean-compare EXPORT.ndjson SEARCHPATH MODULE...");
            3
        }
    });
    match h {
        Ok(t) => match t.join() {
            Ok(code) => {
                // no free cascade on the way out
                std::process::exit(code as i32)
            }
            Err(_) => ExitCode::from(3),
        },
        Err(_) => ExitCode::from(3),
    }
}
