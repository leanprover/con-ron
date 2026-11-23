//! `driver::compare_json` — con-leche's `Driver/CompareJson.lean`:
//! `--compare [--] CHALLENGE.ndjson SOLUTION.ndjson` over `CheckerIo`
//! (DESIGN.md §3.9, task #171).
//!
//! The solution's file is checked as any input is, and its index is the
//! **solution** of the challenge's check: the challenge's axioms other than
//! the built-in ones, and its records whose value uses `sorryAx`, take the
//! justification route (`arena::justify`).  Both files are read and prepared
//! into the ONE store of the run, so a handle of the challenge and one of the
//! solution are equal exactly when what they denote is; the challenge's index
//! is built after the solution's check phase thawed the tier, on the same
//! store, which only grows.
//!
//! ```text
//! intern_reserved_pins → builtin_prelude_e → parse_source (the challenge)
//!   → parse_source (the solution) → prelude_ix_dup → prepare_d (the solution)
//!   → decode_embedded → intern_all_pins → check_phase (the solution, no solution)
//!   → prepare_d (the challenge) → side_records → solution_of
//!   → check_phase (the challenge, with the solution)
//! ```
//!
//! — one call per step premise of `ConRon.MainTheorem.Stages.model_exists_compare`, in
//! that order (`h1` … `h8`), on one `AState::empty()` and one
//! `PersTier::empty()`.

use crate::arena::checker;
use crate::arena::env::IDeclaration;
use crate::arena::justify;
use crate::arena::justify::Solution;
use crate::arena::monad::AState;
use crate::arena::pins;
use crate::arena::store::PersTier;
use crate::arena::stream_index::IStreamIndex;
use crate::driver::check_main::check_phase;
use crate::driver::check_main::exit_code;
use crate::driver::check_main::jobs_for_run;
use crate::driver::check_main::embedded_pins;
use crate::driver::check_main::Note;
use crate::driver::cli::Args;
use crate::driver::cli::Bad;
use crate::frontend::checker_io::CheckerIo;
use crate::frontend::checker_io::FileChunks;
use crate::frontend::export_c;
use crate::frontend::export_c::ParseResultD;
use crate::frontend::nat_op_ground::DeclUsedConsts;
use crate::frontend::prelude;
use crate::frontend::prepare;
use crate::frontend::text::cps_beq;
use crate::kernel::core_types::CheckError;
use crate::kernel::env::CheckMode;
use crate::kernel::expr::str_copy;
use crate::kernel::nat_op_pins::NatOpPinSet;

/// con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
/// **One lean4export file, read and parsed** into the run's store: the
/// stream parse over the file's positional reads (`FileChunks`).  A failed
/// read is reported in place of what the parse of the truncated input said
/// (exit 3); a failed parse is its verdict.
pub fn read_export<I: CheckerIo>(
    io: &I,
    pers: &PersTier,
    st: &mut AState,
    file: &Vec<u32>,
    verified: bool,
) -> Result<ParseResultD, u8> {
    let (read, err) = {
        let mut src = FileChunks { fs: io, path: file, off: 0, reads: 0, err: None };
        let read = export_c::parse_source(pers, st, &mut src);
        (read, src.err)
    };
    match err {
        Some(m) => {
            io.note(&Note::ReadFailed(str_copy(file), m));
            return Err(3);
        }
        None => (),
    }
    match read {
        Err((e, line)) => {
            let c = exit_code(&e);
            io.note(&Note::Parse(e, line, str_copy(file), verified));
            Err(c)
        }
        Ok(p) => Ok(p),
    }
}

/// con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
/// **The justified records**: the positions `k < n` whose checked record
/// `checked[k]` offers a statement (`justify::justifiable`), so that the
/// record the challenge declares at `k` took the justification route.
pub fn justified(st: &mut AState, checked: &Vec<IDeclaration>, n: usize) -> Result<Vec<usize>, CheckError> {
    let mut out: Vec<usize> = Vec::new();
    let mut k = 0usize;
    while k < n {
        match justify::justifiable(st, &checked[k]) {
            Err(e) => return Err(e),
            Ok(Some(_)) => out.push(k),
            Ok(None) => (),
        }
        k += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
/// **The verdict on the challenge**: its failure line and exit code, or the
/// accept line, one line per justified record (labelled as the challenge
/// declares it, `prepared`), and 0.  The heap goes to the instance (con-leche
/// task #336).
#[allow(clippy::too_many_arguments)]
pub fn compare_verdict<I: CheckerIo>(
    io: &mut I,
    pers: &PersTier,
    st: AState,
    ds_s: Vec<IDeclaration>,
    prepared: Vec<IDeclaration>,
    recs: Vec<IDeclaration>,
    sol: Solution,
    verdict: Result<IStreamIndex, (CheckError, u64)>,
    records: usize,
    solution: &Vec<u32>,
    records_s: usize,
    verified: bool,
) -> u8 {
    match verdict {
        Err((e, i)) => {
            let c = exit_code(&e);
            io.verdict_failure(pers, &st.store, &recs, &e, i, verified);
            io.keep_solution(ds_s, prepared, sol);
            io.keep_heap(st, recs, None);
            c
        }
        Ok(ix) => {
            let mut st = st;
            let n = if recs.len() < prepared.len() { recs.len() } else { prepared.len() };
            match justified(&mut st, &recs, n) {
                Err(e) => {
                    let c = exit_code(&e);
                    io.note(&Note::Frontend(e, verified));
                    io.keep_solution(ds_s, prepared, sol);
                    io.keep_heap(st, recs, Some(ix));
                    c
                }
                Ok(holes) => {
                    io.compare_accepted(pers, &st.store, &prepared, &holes, records, solution, records_s, verified);
                    io.keep_solution(ds_s, prepared, sol);
                    io.keep_heap(st, recs, Some(ix));
                    0
                }
            }
        }
    }
}

/// con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
/// **The solution failed its check**: the failure line, as the solution's, and
/// its exit code; the heap goes to the instance.
pub fn solution_failed<I: CheckerIo>(
    io: &mut I,
    pers: &PersTier,
    st: AState,
    ds: Vec<IDeclaration>,
    e: CheckError,
    i: u64,
    solution: &Vec<u32>,
    verified: bool,
) -> u8 {
    let c = exit_code(&e);
    io.solution_failure(pers, &st.store, &ds, &e, i, verified, solution);
    io.keep_heap(st, ds, None);
    c
}

/// con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
/// **A lean4export file checked with a solution** (module note): the
/// challenge's file and the solution's parsed into one store, the solution
/// prepared and checked, then the challenge prepared, its records read with
/// the solution (`side_records`) and checked with it; the exit code.
pub fn compare_json<I: CheckerIo>(io: &mut I, a: &Args, challenge: &Vec<u32>, solution: &Vec<u32>) -> u8 {
    let verified = a.verified;
    let mode = if verified { CheckMode::Verified } else { CheckMode::Trusted };
    let mut st = AState::empty();
    let pers = PersTier::empty();
    // ConRon.MainTheorem.Stages: h1
    match pins::intern_reserved_pins(&pers, &mut st) {
        Err(e) => {
            io.note(&Note::ReservedPins(e, verified));
            return 3;
        }
        Ok(()) => (),
    }
    // ConRon.MainTheorem.Stages: h2
    let pre = match prelude::builtin_prelude_e(&pers, &mut st) {
        Err((e, line)) => {
            io.note(&Note::Prelude(e, line, verified));
            return 3;
        }
        Ok(p) => p,
    };
    // THE CHALLENGE'S FILE, then the solution's, into the one store.
    io.read_starts(&a.progress, challenge);
    // ConRon.MainTheorem.Stages: hreadsC, h3
    let rc: ParseResultD = match read_export(&*io, &pers, &mut st, challenge, verified) {
        Err(c) => return c,
        Ok(r) => r,
    };
    io.read_starts(&a.progress, solution);
    // ConRon.MainTheorem.Stages: hreadsS, h3S
    let rs: ParseResultD = match read_export(&*io, &pers, &mut st, solution, verified) {
        Err(c) => return c,
        Ok(r) => r,
    };
    let records_c = rc.decls.len();
    let records_s = rs.decls.len();
    // THE SOLUTION, checked as any input.
    // ConRon.MainTheorem.Stages: hdup
    let pre_c = prepare::prelude_ix_dup(&pre);
    // ConRon.MainTheorem.Stages: h4S
    let prep_s = match prepare::prepare_d(&pers, &mut st, pre, rs.decls, &DeclUsedConsts) {
        Err(e) => {
            let c = exit_code(&e);
            io.note(&Note::Frontend(e, verified));
            return c;
        }
        Ok(p) => p,
    };
    if prep_s.hoisted.len() > 0 {
        io.hoisted(&pers, &st.store, &prep_s.hoisted);
    }
    // ConRon.MainTheorem.Stages: hpins
    let pins: Vec<NatOpPinSet> = match embedded_pins(&*io) {
        None => return 3,
        Some(ps) => ps,
    };
    // ConRon.MainTheorem.Stages: h5
    let ipins = match checker::intern_all_pins(&pers, &mut st, &pins, &a.max_nat_size) {
        Err(e) => {
            let c = exit_code(&e);
            io.note(&Note::Frontend(e, verified));
            return c;
        }
        Ok(p) => p,
    };
    let jobs: u64 = jobs_for_run(io, a);
    // ConRon.MainTheorem.Stages: h6S, h7S, h8S
    let ix_s = match check_phase(io, &pers, &mut st, &mode, &ipins, None, &prep_s.decls, jobs, records_s, prep_s.synthesised) {
        Err((e, i)) => return solution_failed(io, &pers, st, prep_s.decls, e, i, solution, verified),
        Ok(ix) => ix,
    };
    // THE CHALLENGE, checked with the solution.
    // ConRon.MainTheorem.Stages: h4
    let prep_c = match prepare::prepare_d(&pers, &mut st, pre_c, rc.decls, &DeclUsedConsts) {
        Err(e) => {
            let c = exit_code(&e);
            io.note(&Note::Frontend(e, verified));
            return c;
        }
        Ok(p) => p,
    };
    if prep_c.hoisted.len() > 0 {
        io.hoisted(&pers, &st.store, &prep_c.hoisted);
    }
    // ConRon.MainTheorem.Stages: hside
    let recs_c = match justify::side_records(&pers, &mut st, &prep_c.decls, 0, Vec::new()) {
        Err(e) => {
            let c = exit_code(&e);
            io.note(&Note::Frontend(e, verified));
            return c;
        }
        Ok(v) => v,
    };
    // ConRon.MainTheorem.Stages: hsol
    let sol: Solution = justify::solution_of(ix_s, &recs_c);
    // ConRon.MainTheorem.Stages: h6, h7, h8
    let verdict = check_phase(io, &pers, &mut st, &mode, &ipins, Some(&sol), &recs_c, jobs, records_c, prep_c.synthesised);
    compare_verdict(io, &pers, st, prep_s.decls, prep_c.decls, recs_c, sol, verdict, records_c, solution, records_s, verified)
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// **`--compare` on two lean4export files, from the parsed arguments**:
/// con-leche's usage checks of the mode in its order (no flag of `--olean`'s,
/// two files, two different ones), then the run.
pub fn compare_args<I: CheckerIo>(io: &mut I, a: &Args) -> u8 {
    if a.search_path.len() > 0
        || a.constants.len() > 0
        || a.module
        || a.modular
        || a.scheduled
        || a.trusted_path.len() > 0
    {
        io.usage(&Bad::CompareTakeOlean);
        return 3;
    }
    if a.files.len() != 2 {
        io.usage(&Bad::CompareTwoFiles);
        return 3;
    }
    if cps_beq(&a.files[0], &a.files[1]) {
        io.usage(&Bad::CompareSameFile);
        return 3;
    }
    compare_json(io, a, &a.files[0], &a.files[1])
}
