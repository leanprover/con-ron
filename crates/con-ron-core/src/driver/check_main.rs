//! `driver::check_main` — con-leche's `Driver/CheckMain.lean` on a lean4export
//! file: the pipeline `crates/con-ron/src/bin/con-ron.rs`'s `check_main` ran
//! (DESIGN.md §3.9, task #171), now over `CheckerIo`.
//!
//! ```text
//! intern_reserved_pins → builtin_prelude_e → parse_source (FileChunks)
//!   → prepare_d → decode_embedded → intern_all_pins
//!   → build_index → freeze_tier → par_map_workers (JobStep) → thaw_tier
//! ```
//!
//! — one call per step premise of the capstone (`ConRon.Capstone`'s
//! `h1`…`h8`), in that order, on one `AState::empty()` and one
//! `PersTier::empty()`.  What a run prints goes through the instance's
//! notifications (`Note` and the store-reading ones), whose rendering is the
//! binary's text.

use crate::arena::checker;
use crate::arena::core::enter_record;
use crate::arena::core::leave_record;
use crate::arena::env;
use crate::arena::handle::NIdx;
use crate::arena::handle::ETAG_BVAR;
use crate::arena::monad;
use crate::arena::env::IDeclaration;
use crate::arena::justify::Solution;
use crate::arena::monad::AState;
use crate::arena::nat_op_pin_set::INatOpPinSet;
use crate::arena::pins;
use crate::arena::pins::Pins;
use crate::arena::store::EStore;
use crate::arena::store::PersTier;
use crate::arena::stream_index;
use crate::arena::stream_index::IStreamIndex;
use crate::driver::cli::Args;
use crate::frontend::checker_io::CheckerFs;
use crate::frontend::checker_io::CheckerIo;
use crate::frontend::checker_io::FileChunks;
use crate::frontend::checker_io::Step;
use crate::frontend::export_c;
use crate::frontend::nat_op_ground::DeclUsedConsts;
use crate::frontend::olean::files::Roots;
use crate::frontend::olean::records;
use crate::frontend::olean::records::ModRef;
use crate::frontend::olean::records::OleanRead;
use crate::frontend::olean::records::ValueCache;
use crate::frontend::olean::spec::OleanPins;
use crate::frontend::prelude;
use crate::frontend::prepare;
use crate::kernel::core_types::CheckError;
use crate::kernel::env::CheckMode;
use crate::kernel::expr::str_copy;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::nat_op_pins::NatOpPinSet;
use crate::kernel::pins_decode;

/// con-leche: ConLeche/Driver/CheckMain.lean:70-75 diagLine
/// **A line of the run that reads no store**, as a structured event; `bool` is
/// the mode (`true`: `--verified`).  The instance renders each in the binary's
/// words (`StdIo::note`).
pub enum Note {
    /// no arguments: the invocation forms, and the pointer to `--help`
    Synopsis,
    /// the reserved-name pins did not intern
    ReservedPins(CheckError, bool),
    /// the built-in prelude failed, at its line
    Prelude(CheckError, u64, bool),
    /// a read of the file failed: the file, the message
    ReadFailed(Vec<u32>, Vec<u32>),
    /// the stream failed, at its line: the file
    Parse(CheckError, u64, Vec<u32>, bool),
    /// the preparation or the pin walk failed
    Frontend(CheckError, bool),
    /// `--pins FILE` did not read
    PinsFile(Vec<u32>),
    /// the embedded pin text did not decode
    EmbeddedPins(CheckError),
    /// the accept line: the file's record count
    Accepted(u64, bool),
    /// the `.olean` read failed, at its line: the roots
    OleanRead(CheckError, u64, Vec<Name>, bool),
    /// the graph check's reserved-name pins did not intern
    GraphPins(CheckError),
    /// the graph check failed
    GraphFailed(CheckError),
    /// `--modular`'s graph is checked: its module count (at a pace that is on)
    ModularGraph(u64),
    /// `--modular`'s modules could not be run: the message
    ModularThreads(Vec<u32>),
    /// `--modular`'s modules are done (at a pace that is on)
    ModularDone,
    /// `--modular`'s accept line: the module count
    ModularAccepted(u64, bool),
    /// `--modular`'s failure line: the modules not accepted, of how many, the
    /// first in the graph's order
    ModularFailed(u64, u64, Name, bool),
}

/// con-leche: ConLeche/Driver/CheckMain.lean:36-49 ConLeche.CheckError.exitCode
/// The cited three codes, plus the port's fourth constructor (`Native`, a
/// machine-word limit): a DECLINE, exit 2, as "not implemented" is.  Never 0.
pub fn exit_code(e: &CheckError) -> u8 {
    match e {
        CheckError::NotImplemented(_) => 2,
        CheckError::Invalid(_) => 1,
        CheckError::Internal(_) => 3,
        CheckError::Native(_) => 2,
    }
}

/// con-leche: ConLeche/Driver/CheckPool.lean:208-218 poolName
/// The worker count a run reports and the pool spawns: `max 1 (min jobs m)`.
pub fn workers_for(jobs: u64, m: usize) -> usize {
    let j = jobs as usize;
    let w = if j < m { j } else { m };
    if w < 1 {
        1
    } else {
        w
    }
}

/// con-leche: ConLeche/Driver/CheckPool.lean:128-135 runAt
/// **A job of the check phase**: `checker::run_job` at a record position, on
/// the frozen tier, from `checker::worker_state` of the driver's pins, with
/// the solution a compared run's challenge is checked with.
pub struct JobStep<'a> {
    /// the frozen persistent tier
    pub tier: &'a PersTier,
    /// the check mode
    pub mode: &'a CheckMode,
    /// the interned `Nat`-operation pins
    pub pins: &'a Vec<INatOpPinSet>,
    /// the driver's pin handles, which every worker's state copies
    pub apins: &'a Pins,
    /// the solution (a compared run's challenge), or none
    pub sol: Option<&'a Solution>,
    /// the records
    pub ds: &'a Vec<IDeclaration>,
}

/// con-leche: ConLeche/Driver/CheckPool.lean:128-135 runAt
impl<'a, F: CheckerFs> Step<F, AState> for JobStep<'a> {
    /// con-leche: ConLeche/Driver/CheckPool.lean:128-135 runAt
    /// A worker's state: a frozen store over the tier, the driver's pins.
    fn init(&self) -> AState {
        checker::worker_state(self.apins)
    }

    /// con-leche: ConLeche/Driver/CheckPool.lean:128-135 runAt
    /// The record's job at its position, with the solution.
    fn step(&self, _fs: &F, s: &mut AState, k: usize) -> Result<(), (CheckError, u64)> {
        checker::run_job(self.tier, s, self.mode, self.pins, self.sol, self.ds, k as u64)
    }

    /// con-leche: ConLeche/Driver/CheckPool.lean:101-111 jobLabel
    fn view<'b>(&'b self, s: &'b AState) -> (&'b PersTier, &'b EStore, &'b Vec<IDeclaration>, usize) {
        (self.tier, &s.store, self.ds, 0)
    }
}

/// con-leche: ConLeche/Driver/CheckMain.lean:120-134 oleanJobRun
/// **One job of an `.olean` run**, from the module region the worker kept
/// (`cache`): a theorem whose value is still in its file (`.thmDecl cv (.bvar
/// code)`, a reference) reads it into the worker's scratch tier and is checked
/// with it in place, any other record as it stands.  The value goes with the
/// tier when the job ends.  The read is inside the job's bracket
/// (`enter_record` … `leave_record`, `stream_index::record_job`'s), so that what
/// it interns is the job's.  Upstream's `sp : Roots` (the closure's resolved
/// roots) is the lookup without its map here (`files::find_module`'s note).
pub fn olean_job<F: CheckerFs>(
    fs: &F,
    tier: &PersTier,
    w: &mut AState,
    cache: &mut ValueCache,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
    pk: &OleanPins,
    values: &Vec<ModRef>,
    sp: &Roots,
    k: usize,
) -> Result<(), (CheckError, u64)> {
    let ku = k as u64;
    if k >= ds.len() {
        return checker::run_job(tier, w, mode, pins, None, ds, ku);
    }
    match &ds[k] {
        IDeclaration::ThmDecl(cv, v) => {
            // a theorem's value is a reference only if its handle is a `bvar`: the
            // store's projection reads the bvar table at the handle's slot whatever
            // its tag
            let code: Option<u64> = if v.tag() == ETAG_BVAR { w.store.view_bvar(tier, v) } else { None };
            match code {
                None => checker::run_job(tier, w, mode, pins, None, ds, ku),
                Some(code) => {
                    enter_record(w);
                    let r = match records::read_value(fs, pk, tier, &mut w.store, sp, values, cache, code) {
                        Err(e) => Err((e, ku)),
                        Ok(v) => {
                            let pd = IDeclaration::ThmDecl(env::i_constant_val_dup(cv), v);
                            match stream_index::record_check(tier, w, mode, pins, None, ku, &pd) {
                                Err(e) => Err((e, ku)),
                                Ok(()) => Ok(()),
                            }
                        }
                    };
                    leave_record(w);
                    r
                }
            }
        }
        _ => checker::run_job(tier, w, mode, pins, None, ds, ku),
    }
}

/// con-leche: ConLeche/Driver/CheckMain.lean:120-134 oleanJobRun
/// **A job of an `.olean` run's check phase**: `olean_job` at position
/// `start + k`, on the frozen tier, from `checker::worker_state` of the driver's
/// pins and an empty region (con-leche's `OleanWorker`).  `start` is 0 but at a
/// module's worker, whose context's records are no jobs.
pub struct OleanJobStep<'a> {
    /// the frozen persistent tier
    pub tier: &'a PersTier,
    /// the check mode
    pub mode: &'a CheckMode,
    /// the interned `Nat`-operation pins
    pub pins: &'a Vec<INatOpPinSet>,
    /// the driver's pin handles, which every worker's state copies
    pub apins: &'a Pins,
    /// the records
    pub ds: &'a Vec<IDeclaration>,
    /// the reader's pins
    pub pk: &'a OleanPins,
    /// the modules a theorem's value is read from
    pub values: &'a Vec<ModRef>,
    /// the lookup the values are read through
    pub sp: &'a Roots,
    /// the position of job 0 among the records
    pub start: usize,
}

/// con-leche: ConLeche/Driver/CheckMain.lean:120-134 oleanJobRun
impl<'a, F: CheckerFs> Step<F, (AState, ValueCache)> for OleanJobStep<'a> {
    /// con-leche: ConLeche/Driver/CheckMain.lean:120-134 oleanJobRun
    /// A worker's state: a frozen store over the tier, the driver's pins, no
    /// region yet.
    fn init(&self) -> (AState, ValueCache) {
        (checker::worker_state(self.apins), records::value_cache_empty())
    }

    /// con-leche: ConLeche/Driver/CheckMain.lean:120-134 oleanJobRun
    /// The record's job at position `start + k`.
    fn step(&self, fs: &F, s: &mut (AState, ValueCache), k: usize) -> Result<(), (CheckError, u64)> {
        olean_job(fs, self.tier, &mut s.0, &mut s.1, self.mode, self.pins, self.ds, self.pk, self.values, self.sp, self.start + k)
    }

    /// con-leche: ConLeche/Driver/CheckPool.lean:101-111 jobLabel
    fn view<'b>(&'b self, s: &'b (AState, ValueCache)) -> (&'b PersTier, &'b EStore, &'b Vec<IDeclaration>, usize) {
        (self.tier, &s.0.store, self.ds, self.start)
    }
}

/// con-leche: none — `filterMap parseModName`, over handles
/// **The names, interned**, each from the state the last left; the first
/// failure.
pub fn intern_names(pers: &PersTier, st: &mut AState, ns: &Vec<Name>) -> Result<Vec<NIdx>, CheckError> {
    let mut out: Vec<NIdx> = Vec::new();
    let mut i = 0usize;
    while i < ns.len() {
        match monad::intern_name(pers, st, &ns[i]) {
            Err(e) => return Err(e),
            Ok(h) => out.push(h),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Cli.lean:383-385 Args.rootConstants
/// The constants to start from, interned: none where none is named (every
/// constant of the closure).
pub fn intern_consts(pers: &PersTier, st: &mut AState, cs: &Vec<Name>) -> Result<Option<Vec<NIdx>>, CheckError> {
    if cs.len() == 0 {
        return Ok(None);
    }
    match intern_names(pers, st, cs) {
        Err(e) => Err(e),
        Ok(c) => Ok(Some(c)),
    }
}

/// con-leche: ConLeche/Driver/Run.lean:85-106 checkDeclsIO
/// con-leche: ConLeche/Driver/CheckPool.lean:220-242 checkPool
/// **The check phase**: the stream's index, built once from the records alone
/// (`stream_index::build_index`), the tier frozen with it, every record's job
/// on the worker map with the solution `sol`, the tier thawed.  On `Ok` the
/// thawed index.
pub fn check_phase<I: CheckerIo>(
    io: &mut I,
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    ipins: &Vec<INatOpPinSet>,
    sol: Option<&Solution>,
    ds: &Vec<IDeclaration>,
    jobs: u64,
    file_records: usize,
    synthesised: u64,
) -> Result<IStreamIndex, (CheckError, u64)> {
    io.index_starts();
    let ix = match stream_index::build_index(pers, st, stream_index::stream_index_empty(), ds, 0) {
        Err(e) => return Err(e),
        Ok(ix) => ix,
    };
    io.parse_done(pers, &st.store, ds.len(), file_records, synthesised);
    let n = ds.len();
    let workers = workers_for(jobs, n);
    io.check_starts(n, workers);
    let tier: PersTier = checker::freeze_tier(&mut st.store, ix);
    let r = {
        let step = JobStep { tier: &tier, mode, pins: ipins, apins: &st.pins, sol, ds };
        io.par_map_workers(&step, n, workers)
    };
    let ix: IStreamIndex = checker::thaw_tier(&mut st.store, tier);
    match r {
        Ok(()) => {
            io.check_done(n, &None);
            Ok(ix)
        }
        Err((e, pos)) => {
            io.check_done(n, &Some(pos));
            Err((e, pos))
        }
    }
}

/// con-leche: ConLeche/Driver/CheckMain.lean:154-177 checkOleansG
/// **The check phase of an `.olean` run**: `check_phase` with every record's job
/// `olean_job` (`OleanJobStep` from 0), a theorem's value read from its file
/// through the lookup `sp`.
pub fn check_phase_olean<I: CheckerIo>(
    io: &mut I,
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    ipins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
    pk: &OleanPins,
    values: &Vec<ModRef>,
    sp: &Roots,
    jobs: u64,
    file_records: usize,
    synthesised: u64,
) -> Result<IStreamIndex, (CheckError, u64)> {
    io.index_starts();
    let ix = match stream_index::build_index(pers, st, stream_index::stream_index_empty(), ds, 0) {
        Err(e) => return Err(e),
        Ok(ix) => ix,
    };
    io.parse_done(pers, &st.store, ds.len(), file_records, synthesised);
    let n = ds.len();
    let workers = workers_for(jobs, n);
    io.check_starts(n, workers);
    let tier: PersTier = checker::freeze_tier(&mut st.store, ix);
    let r = {
        let step = OleanJobStep { tier: &tier, mode, pins: ipins, apins: &st.pins, ds, pk, values, sp, start: 0 };
        io.par_map_workers(&step, n, workers)
    };
    let ix: IStreamIndex = checker::thaw_tier(&mut st.store, tier);
    match r {
        Ok(()) => {
            io.check_done(n, &None);
            Ok(ix)
        }
        Err((e, pos)) => {
            io.check_done(n, &Some(pos));
            Err((e, pos))
        }
    }
}

/// con-leche: none — how a run chooses the pin list, which con-leche's driver
/// does not have to (it passes `natOpPinSets`): the embedded text, decoded by
/// the verified decoder (`pins_decode::decode_embedded`), unless `--no-pins`
/// (the empty list) or `--pins FILE` (the instance's unverified reader), the
/// port's two testing overrides.  A failure is noted, and `None`.
pub fn pins_for_run<I: CheckerIo>(io: &mut I, a: &Args) -> Option<Vec<NatOpPinSet>> {
    if a.no_pins {
        return Some(Vec::new());
    }
    match &a.pins {
        Some(p) => match io.read_pins_file(p) {
            Err(m) => {
                io.note(&Note::PinsFile(m));
                None
            }
            Ok(ps) => Some(ps),
        },
        None => match pins_decode::decode_embedded() {
            Err(e) => {
                io.note(&Note::EmbeddedPins(e));
                None
            }
            Ok(ps) => Some(ps),
        },
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// The worker count: `--jobs=<n>`, or the instance's hardware default.
pub fn jobs_for_run<I: CheckerIo>(io: &mut I, a: &Args) -> u64 {
    match a.jobs {
        Some(n) => n,
        None => io.hardware_jobs(),
    }
}

/// con-leche: ConLeche/Driver/CheckMain.lean:180-266 verdictG
/// **The verdict**: the accept line (the FILE's record count, which nothing the
/// preparation does moves) and 0, or the failure line and its exit code; the
/// heap goes to the instance (con-leche task #336).
pub fn verdict_of<I: CheckerIo>(
    io: &mut I,
    pers: &PersTier,
    st: AState,
    ds: Vec<IDeclaration>,
    verdict: Result<IStreamIndex, (CheckError, u64)>,
    file_records: usize,
    verified: bool,
) -> u8 {
    match verdict {
        Ok(ix) => {
            io.note(&Note::Accepted(file_records as u64, verified));
            io.keep_heap(st, ds, Some(ix));
            0
        }
        Err((e, i)) => {
            let c = exit_code(&e);
            io.verdict_failure(pers, &st.store, &ds, &e, i, verified);
            io.keep_heap(st, ds, None);
            c
        }
    }
}

/// con-leche: ConLeche/Driver/CheckMain.lean:268-458 checkMainG
/// **The check of one lean4export file** — `bin/con-ron.rs`'s `check_main`
/// on `Input::Ndjson`, step for step: the reserved pins, the heartbeat's first
/// line, the prelude, the streaming parse over the file's reads, the
/// preparation and its receipt, the pin list, the pin walk, the check phase,
/// the verdict; the exit code.  The verdict path hands the heap to the
/// instance (`keep_heap`) rather than freeing it (con-leche task #336).
pub fn check_main<I: CheckerIo>(io: &mut I, a: &Args, file: &Vec<u32>) -> u8 {
    let verified = a.verified;
    let mode = if verified { CheckMode::Verified } else { CheckMode::Trusted };
    let mut st = AState::empty();
    let pers = PersTier::empty();
    // ConRon.Capstone: h1
    match pins::intern_reserved_pins(&pers, &mut st) {
        Err(e) => {
            io.note(&Note::ReservedPins(e, verified));
            return 3;
        }
        Ok(()) => (),
    }
    io.read_starts(&a.progress, file);
    // ConRon.Capstone: h2
    let prelude_ix = match prelude::builtin_prelude_e(&pers, &mut st) {
        Err((e, line)) => {
            io.note(&Note::Prelude(e, line, verified));
            return 3;
        }
        Ok(p) => p,
    };
    // ConRon.Capstone: hreads, h3
    let (read, err) = {
        let mut src = FileChunks { fs: &*io, path: file, off: 0, reads: 0, err: None };
        let read = export_c::parse_source(&pers, &mut st, &mut src);
        (read, src.err)
    };
    match err {
        Some(m) => {
            io.note(&Note::ReadFailed(str_copy(file), m));
            return 3;
        }
        None => (),
    }
    let parsed = match read {
        Err((e, line)) => {
            let c = exit_code(&e);
            io.note(&Note::Parse(e, line, str_copy(file), verified));
            return c;
        }
        Ok(p) => p,
    };
    let file_records = parsed.decls.len();
    // ConRon.Capstone: h4
    let prepared = match prepare::prepare_d(&pers, &mut st, prelude_ix, parsed.decls, &DeclUsedConsts) {
        Err(e) => {
            let c = exit_code(&e);
            io.note(&Note::Frontend(e, verified));
            return c;
        }
        Ok(p) => p,
    };
    if prepared.hoisted.len() > 0 {
        io.hoisted(&pers, &st.store, &prepared.hoisted);
    }
    // ConRon.Capstone: hpins (`--pins`/`--no-pins` are outside the theorems)
    let pins: Vec<NatOpPinSet> = match pins_for_run(io, a) {
        None => return 3,
        Some(ps) => ps,
    };
    // ConRon.Capstone: h5
    let ipins = match checker::intern_all_pins(&pers, &mut st, &pins, &a.max_nat_size) {
        Err(e) => {
            let c = exit_code(&e);
            io.note(&Note::Frontend(e, verified));
            return c;
        }
        Ok(p) => p,
    };
    let jobs: u64 = jobs_for_run(io, a);
    // ConRon.Capstone: h6, h7, h8
    let verdict = check_phase(io, &pers, &mut st, &mode, &ipins, None, &prepared.decls, jobs, file_records, prepared.synthesised);
    verdict_of(io, &pers, st, prepared.decls, verdict, file_records, verified)
}

/// con-leche: ConLeche/Driver/CheckMain.lean:268-458 checkMainG
/// The failure of an `.olean` read: its line, and its exit code.
pub fn oleans_failed<I: CheckerIo>(io: &mut I, e: CheckError, line: u64, roots: &Vec<Name>, verified: bool) -> u8 {
    let c = exit_code(&e);
    io.note(&Note::OleanRead(e, line, name_vec_dup(roots), verified));
    c
}

/// con-leche: none — a list of names, copied
pub fn name_vec_dup(ns: &Vec<Name>) -> Vec<Name> {
    let mut out: Vec<Name> = Vec::new();
    let mut i = 0usize;
    while i < ns.len() {
        out.push(name::dup(&ns[i]));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/CheckMain.lean:268-458 checkMainG
/// con-leche: ConLeche/Driver/CheckMain.lean:87-98 readInputG
/// **The check of the closure of root modules** (`--olean`): `check_main` with
/// the stream's parse replaced by the roots interned and the `.olean` reader
/// over the lookup `sp` (`records::read_oleans`, the constants `cs` or the whole
/// closure), the preparation reading what a theorem mentions off the read
/// (`prepare_d` at the `OleanRead`), and every theorem's job reading its value
/// from its file (`check_phase_olean`).  The read's records leave it before the
/// preparation, and its merged constants after it, before the pool.
pub fn check_oleans<I: CheckerIo>(io: &mut I, a: &Args, roots: &Vec<Name>, cs: &Vec<Name>, sp: &Roots) -> u8 {
    let verified = a.verified;
    let mode = if verified { CheckMode::Verified } else { CheckMode::Trusted };
    let mut st = AState::empty();
    let pers = PersTier::empty();
    // ConRon.Capstone: h1
    match pins::intern_reserved_pins(&pers, &mut st) {
        Err(e) => {
            io.note(&Note::ReservedPins(e, verified));
            return 3;
        }
        Ok(()) => (),
    }
    io.oleans_read_starts(&a.progress, roots);
    // ConRon.Capstone: h2
    let prelude_ix = match prelude::builtin_prelude_e(&pers, &mut st) {
        Err((e, line)) => {
            io.note(&Note::Prelude(e, line, verified));
            return 3;
        }
        Ok(p) => p,
    };
    // ConRon.Capstone: hroots
    let rs = match intern_names(&pers, &mut st, roots) {
        Err(e) => return oleans_failed(io, e, 0, roots, verified),
        Ok(rs) => rs,
    };
    let consts: Option<Vec<NIdx>> = match intern_consts(&pers, &mut st, cs) {
        Err(e) => return oleans_failed(io, e, 0, roots, verified),
        Ok(c) => c,
    };
    // ConRon.Capstone: h3
    io.read_notes_begin(&a.progress);
    let read = records::read_oleans(&*io, &pers, &mut st.store, sp, &rs, &consts, false, false);
    io.read_notes_end();
    let mut rd = match read {
        Err((e, line)) => return oleans_failed(io, e, line, roots, verified),
        Ok(rd) => rd,
    };
    let file_records = rd.decls.len();
    let decls = core::mem::replace(&mut rd.decls, Vec::new());
    // ConRon.Capstone: h4 (what a theorem mentions, off the read)
    let prepared = match prepare::prepare_d(&pers, &mut st, prelude_ix, decls, &rd) {
        Err(e) => {
            let c = exit_code(&e);
            io.note(&Note::Frontend(e, verified));
            return c;
        }
        Ok(p) => p,
    };
    // what the check keeps of the read: the reader's pins and the values' modules
    let OleanRead { decls: _, values, merged: _, homes: _, pins: pk } = rd;
    if prepared.hoisted.len() > 0 {
        io.hoisted(&pers, &st.store, &prepared.hoisted);
    }
    // ConRon.Capstone: hpins
    let pins: Vec<NatOpPinSet> = match pins_for_run(io, a) {
        None => return 3,
        Some(ps) => ps,
    };
    // ConRon.Capstone: h5
    let ipins = match checker::intern_all_pins(&pers, &mut st, &pins, &a.max_nat_size) {
        Err(e) => {
            let c = exit_code(&e);
            io.note(&Note::Frontend(e, verified));
            return c;
        }
        Ok(p) => p,
    };
    let jobs: u64 = jobs_for_run(io, a);
    // ConRon.Capstone: h6, h7, h8
    let verdict = check_phase_olean(io, &pers, &mut st, &mode, &ipins, &prepared.decls, &pk, &values, sp, jobs, file_records, prepared.synthesised);
    verdict_of(io, &pers, st, prepared.decls, verdict, file_records, verified)
}
