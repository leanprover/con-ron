//! `con-ron-dump-check` — read `con-ron-decls/1` dumps and report.
//!
//! The Rust half of DESIGN.md §3.6's differential-testing seam (task #19).
//! `lake exe con-ron-dump` writes the dumps (task #10) and validates the
//! format in Lean; this tool validates that *the Rust reader* agrees, before
//! any of the core's checker is wired up:
//!
//! ```text
//! con-ron-dump-check [--roundtrip] [--parse-only] [--sizes] [--quiet]
//!                    <dump.decls|dump.pins>...
//! ```
//!
//! A `con-ron-pins/1` file (FORMAT.md §7) is recognised by its header and
//! goes through `parse_pins_counted`/`dump_pins` instead, with the same two
//! checks.  That is the cross-check of the pin reader against Lean's writer:
//! `lake exe con-ron-dump-pins` produces the file, and this tool says whether
//! the Rust side reads it back node for node and byte for byte.
//!
//! Per file it prints the record census — declarations by kind, interned nodes
//! per id space, bytes — and checks two things beyond "it parsed":
//!
//! * **the DAG is exact** (always): the number of distinct `Name`, `Level` and
//!   `Expr` heap nodes the declarations reach equals the file's `N`, `L` and `E`
//!   record counts, i.e. the reader allocated one node per record and shared it
//!   everywhere else (`con_ron_dump::dag`);
//! * **the round trip is byte-identical** (`--roundtrip`): the dump written back
//!   out with `con_ron_dump::dump_decls` equals the input, which pins every id,
//!   every list length, every escape and the whole emission order to Lean's
//!   writer.
//!
//! `--parse-only` (task #36) is the *measurement* mode: the dump is streamed
//! through `parse_decls_file`, one line at a time, and neither the text nor
//! the census's pointer set nor a re-dump is ever held, so the peak resident
//! set the run reports is the reader's own — the terms plus the id tables
//! plus one line buffer.  `--sizes` prints what one node of each kind weighs
//! (`con_ron_dump::node_sizes`), which is the multiplier in that accounting.
//!
//! Every report ends with the run's peak RSS (`VmHWM`), so the memory numbers
//! in DESIGN.md's task log can be reproduced without `time -v`.
//!
//! Exit status is `0` only if every file passed.

use std::process::ExitCode;
use std::time::Instant;

use con_ron_dump::dag;
use con_ron_dump::dump_decls;
use con_ron_dump::dump_pins;
use con_ron_dump::node_sizes;
use con_ron_dump::parse_decls_counted;
use con_ron_dump::parse_decls_file;
use con_ron_dump::peak_rss_kb;
use con_ron_dump::parse_pins_counted;
use con_ron_dump::Counts;
use con_ron_dump::PINS_HEADER;

const USAGE: &str = "usage: con-ron-dump-check [--roundtrip] [--parse-only] [--sizes] \
                     [--quiet] <dump.decls|dump.pins>...";

/// The running totals across all the files on the command line.
#[derive(Default)]
struct Totals {
    files: usize,
    ok: usize,
    failed: usize,
    bytes: u64,
    counts: Counts,
    parse_ms: f64,
    write_ms: f64,
}

fn add(a: &mut Counts, b: &Counts) {
    a.names += b.names;
    a.levels += b.levels;
    a.pws += b.pws;
    a.exprs += b.exprs;
    a.cvs += b.cvs;
    a.rules += b.rules;
    a.caps += b.caps;
    a.tables += b.tables;
    a.infos += b.infos;
    a.decls += b.decls;
    a.axiom_decls += b.axiom_decls;
    a.defn_decls += b.defn_decls;
    a.thm_decls += b.thm_decls;
    a.opaque_decls += b.opaque_decls;
    a.basis_decls += b.basis_decls;
    a.ind_decls += b.ind_decls;
    a.block_infos += b.block_infos;
    a.pin_sets += b.pin_sets;
}

/// Where the two strings first differ, as a `line:column` plus the two lines.
fn first_difference(want: &str, got: &str) -> String {
    let mut wl = want.split('\n');
    let mut gl = got.split('\n');
    let mut n = 0usize;
    loop {
        n += 1;
        match (wl.next(), gl.next()) {
            (None, None) => return "the two dumps are equal".to_string(),
            (Some(a), Some(b)) if a == b => continue,
            (a, b) => {
                return format!(
                    "line {}:\n  input:  {}\n  re-dump: {}",
                    n,
                    a.map(|s| format!("{:?}", s)).unwrap_or("<eof>".to_string()),
                    b.map(|s| format!("{:?}", s)).unwrap_or("<eof>".to_string())
                )
            }
        }
    }
}

/// The dump's first line, without reading the rest of it — how
/// `--parse-only` tells a declaration dump from a pin dump before deciding
/// to stream.
fn header_of(path: &str) -> Result<String, String> {
    use std::io::BufRead;
    let f = match std::fs::File::open(path) {
        Ok(f) => f,
        Err(e) => return Err(format!("{}", e)),
    };
    let mut l = String::new();
    match std::io::BufReader::new(f).read_line(&mut l) {
        Ok(_) => Ok(l.trim_end_matches('\n').to_string()),
        Err(e) => Err(format!("{}", e)),
    }
}

/// `--parse-only`: stream the dump through the reader and report the census
/// the reader itself counted, with no DAG census, no re-dump and no copy of
/// the text (task #36).  This is the mode the memory budget is measured in;
/// `check_one` is still what the fixture gate runs, because the DAG check and
/// the byte-exact round trip are the properties FORMAT.md §6 asks for.
fn check_one_streamed(path: &str, quiet: bool, t: &mut Totals) -> bool {
    t.files += 1;
    t.bytes += std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);
    let t0 = Instant::now();
    let (ds, counts) = match parse_decls_file(path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("FAIL {}: {}", path, e);
            t.failed += 1;
            return false;
        }
    };
    let parse_ms = t0.elapsed().as_secs_f64() * 1e3;
    t.parse_ms += parse_ms;
    add(&mut t.counts, &counts);
    t.ok += 1;
    if !quiet {
        println!(
            "OK   {}  decls {}  N{} L{} W{} E{}  V{} R{} C{} P{} I{}  \
             parse {:.1} ms  peak RSS {} MB  (streamed: no census, no re-dump)",
            path,
            counts.decls,
            counts.names,
            counts.levels,
            counts.pws,
            counts.exprs,
            counts.cvs,
            counts.rules,
            counts.caps,
            counts.tables,
            counts.infos,
            parse_ms,
            peak_rss_kb() / 1024,
        );
    }
    // `ds` is dropped here, after the peak is read: freeing it cannot lower
    // `VmHWM`, and holding it to this point is what the checker does.
    drop(ds);
    true
}

fn check_one(path: &str, roundtrip: bool, quiet: bool, t: &mut Totals) -> bool {
    t.files += 1;
    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("FAIL {}: {}", path, e);
            t.failed += 1;
            return false;
        }
    };
    t.bytes += bytes.len() as u64;
    // The format is pure ASCII (FORMAT.md §1), so anything else is corruption
    // and is said so rather than mangled into a UTF-8 error.
    if let Some(i) = bytes.iter().position(|b| !b.is_ascii()) {
        eprintln!(
            "FAIL {}: byte {} is 0x{:02x}, but a dump is pure ASCII",
            path, i, bytes[i]
        );
        t.failed += 1;
        return false;
    }
    let text = match String::from_utf8(bytes) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("FAIL {}: {}", path, e);
            t.failed += 1;
            return false;
        }
    };

    if text.starts_with(PINS_HEADER) {
        return check_pins(path, &text, roundtrip, quiet, t);
    }

    let t0 = Instant::now();
    let (ds, counts) = match parse_decls_counted(&text) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("FAIL {}: {}", path, e);
            t.failed += 1;
            return false;
        }
    };
    let parse_ms = t0.elapsed().as_secs_f64() * 1e3;
    t.parse_ms += parse_ms;
    add(&mut t.counts, &counts);

    // FORMAT.md §6.1: the reader must hand back the *DAG*, one allocation per
    // interned record.  Counting distinct heap nodes is what says so; a
    // byte-identical re-dump would not, since the writer re-interns by value.
    let cen = dag::census(&ds);
    if cen.names != counts.names || cen.levels != counts.levels || cen.exprs != counts.exprs {
        eprintln!(
            "FAIL {}: the term is not the dump's DAG -- reached {} name / {} level / {} expr \
             nodes, the file has {} / {} / {} records (a duplicated node, or an \
             unreferenced record)",
            path, cen.names, cen.levels, cen.exprs, counts.names, counts.levels, counts.exprs
        );
        t.failed += 1;
        return false;
    }

    let mut write_ms = 0.0;
    if roundtrip {
        let t1 = Instant::now();
        let again = dump_decls(&ds);
        write_ms = t1.elapsed().as_secs_f64() * 1e3;
        t.write_ms += write_ms;
        if again != text {
            eprintln!(
                "FAIL {}: the re-dump differs from the input at {}",
                path,
                first_difference(&text, &again)
            );
            t.failed += 1;
            return false;
        }
    }

    t.ok += 1;
    if !quiet {
        println!(
            "OK   {}  {} B  decls {} (a{} d{} t{} o{} b{} i{}/{} infos)  \
             N{} L{} W{} E{}  V{} R{} C{} P{} I{}  DAG exact  parse {:.1} ms{}",
            path,
            text.len(),
            counts.decls,
            counts.axiom_decls,
            counts.defn_decls,
            counts.thm_decls,
            counts.opaque_decls,
            counts.basis_decls,
            counts.ind_decls,
            counts.block_infos,
            counts.names,
            counts.levels,
            counts.pws,
            counts.exprs,
            counts.cvs,
            counts.rules,
            counts.caps,
            counts.tables,
            counts.infos,
            parse_ms,
            if roundtrip {
                format!("  write {:.1} ms  round trip EXACT", write_ms)
            } else {
                String::new()
            }
        );
    }
    true
}

/// A `con-ron-pins/1` file: the same two checks on the `S` payload.  The
/// bytes are already read and known to be ASCII.
fn check_pins(path: &str, text: &str, roundtrip: bool, quiet: bool, t: &mut Totals) -> bool {
    let t0 = Instant::now();
    let (ss, counts) = match parse_pins_counted(text) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("FAIL {}: {}", path, e);
            t.failed += 1;
            return false;
        }
    };
    let parse_ms = t0.elapsed().as_secs_f64() * 1e3;
    t.parse_ms += parse_ms;
    add(&mut t.counts, &counts);

    let cen = dag::census_pins(&ss);
    if cen.names != counts.names || cen.levels != counts.levels || cen.exprs != counts.exprs {
        eprintln!(
            "FAIL {}: the pins are not the dump\'s DAG -- reached {} name / {} level / {} expr \
             nodes, the file has {} / {} / {} records",
            path, cen.names, cen.levels, cen.exprs, counts.names, counts.levels, counts.exprs
        );
        t.failed += 1;
        return false;
    }

    let mut write_ms = 0.0;
    if roundtrip {
        let t1 = Instant::now();
        let again = dump_pins(&ss);
        write_ms = t1.elapsed().as_secs_f64() * 1e3;
        t.write_ms += write_ms;
        if again != text {
            eprintln!(
                "FAIL {}: the re-dump differs from the input at {}",
                path,
                first_difference(text, &again)
            );
            t.failed += 1;
            return false;
        }
    }

    t.ok += 1;
    if !quiet {
        println!(
            "OK   {}  {} B  pin sets {}  N{} L{} W{} E{}  DAG exact  parse {:.1} ms{}",
            path,
            text.len(),
            counts.pin_sets,
            counts.names,
            counts.levels,
            counts.pws,
            counts.exprs,
            parse_ms,
            if roundtrip {
                format!("  write {:.1} ms  round trip EXACT", write_ms)
            } else {
                String::new()
            }
        );
    }
    true
}

fn main() -> ExitCode {
    let mut roundtrip = false;
    let mut parse_only = false;
    let mut sizes = false;
    let mut quiet = false;
    let mut paths: Vec<String> = Vec::new();
    for a in std::env::args().skip(1) {
        match a.as_str() {
            "--roundtrip" => roundtrip = true,
            "--parse-only" => parse_only = true,
            "--sizes" => sizes = true,
            "--quiet" => quiet = true,
            "-h" | "--help" => {
                println!("{}", USAGE);
                return ExitCode::SUCCESS;
            }
            _ if a.starts_with('-') => {
                eprintln!("unknown option '{}'\n{}", a, USAGE);
                return ExitCode::from(2);
            }
            _ => paths.push(a),
        }
    }
    if sizes {
        println!("node sizes (bytes; `heap` includes the reference counts in front \
             of a `ron::ptr::P` node)");
        for r in node_sizes() {
            println!(
                "  {:<30} size {:>3}{}",
                r.what,
                r.size,
                if r.heap > 0 { format!("   heap {:>3}", r.heap) } else { String::new() }
            );
        }
        println!();
    }
    if paths.is_empty() {
        if sizes {
            return ExitCode::SUCCESS;
        }
        eprintln!("{}", USAGE);
        return ExitCode::from(2);
    }
    if parse_only && roundtrip {
        eprintln!("con-ron: --parse-only and --roundtrip are exclusive\n{}", USAGE);
        return ExitCode::from(2);
    }

    let mut t = Totals::default();
    let t0 = Instant::now();
    for p in &paths {
        // A pin dump is tiny and its reader has no streaming driver, so
        // `--parse-only` falls back to the in-memory path for one.
        let streamed = parse_only && header_of(p).map(|h| h != PINS_HEADER).unwrap_or(false);
        if streamed {
            check_one_streamed(p, quiet, &mut t);
        } else {
            check_one(p, roundtrip, quiet, &mut t);
        }
    }
    let wall = t0.elapsed().as_secs_f64();

    let c = &t.counts;
    println!();
    println!("files               {}", t.files);
    println!("  parsed            {}", t.ok);
    println!("  FAILED            {}", t.failed);
    println!("total dump bytes    {}", t.bytes);
    println!(
        "declarations        {}  (axiom {}, defn {}, thm {}, opaque {}, basis {}, ind {})",
        c.decls, c.axiom_decls, c.defn_decls, c.thm_decls, c.opaque_decls, c.basis_decls,
        c.ind_decls
    );
    println!("  block infos       {}", c.block_infos);
    if c.pin_sets > 0 {
        println!("pin sets            {}", c.pin_sets);
    }
    println!("interned  names     {}   (all DAG-exact: one allocation per record)", c.names);
    println!("          levels    {}", c.levels);
    println!("          propwhens {}", c.pws);
    println!("          exprs     {}", c.exprs);
    println!("numbered  constvals {}", c.cvs);
    println!("          recrules  {}", c.rules);
    println!("          indcaps   {}", c.caps);
    println!("          projtable {}", c.tables);
    println!("          constinfo {}", c.infos);
    println!("parse time          {:.2} s", t.parse_ms / 1e3);
    if roundtrip {
        println!("re-dump time        {:.2} s  (round trip: byte-identical)", t.write_ms / 1e3);
    }
    println!("wall                {:.2} s", wall);
    println!("peak RSS            {} MB  (VmHWM)", peak_rss_kb() / 1024);

    if t.failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
