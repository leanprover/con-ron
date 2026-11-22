//! `driver::worker` — con-leche's `Driver/Worker.lean` driver: a module's
//! worker, `--olean --module` (the run's one check) or one module of
//! `--olean --modular` (DESIGN.md §3.9, task #171).
//!
//! ```text
//! intern_reserved_pins → intern_name (the module) → the pins → intern_all_pins
//!   → worker_read (phases 1-4) → worker_decls
//!   → build_index → freeze_tier → infer_flags → the jobs from `start`
//! ```
//!
//! — one call per premise of the capstone's worker (`ConRon.Capstone`'s
//! `rust_worker_of`), on one `AState::empty()` and one `PersTier::empty()`.
//! The run's one check puts its jobs on the instance's worker map; a module of
//! `--modular` runs them in order on its own thread (its worker count is 1),
//! with the instance's file operations and its worker lines (`WorkerNotes`)
//! alone.

use crate::arena::checker;
use crate::arena::env::IDeclaration;
use crate::arena::monad;
use crate::arena::monad::AState;
use crate::arena::nat_op_pin_set::INatOpPinSet;
use crate::arena::pins;
use crate::arena::store::PersTier;
use crate::arena::stream_index;
use crate::arena::stream_index::IStreamIndex;
use crate::driver::check_main;
use crate::driver::check_main::OleanJobStep;
use crate::driver::cli::Args;
use crate::frontend::checker_io::CheckerFs;
use crate::frontend::checker_io::CheckerIo;
use crate::frontend::checker_io::WorkerNote;
use crate::frontend::checker_io::WorkerNotes;
use crate::frontend::modular::graph as mgraph;
use crate::frontend::modular::reach;
use crate::frontend::modular::worker;
use crate::frontend::modular::worker::WorkerRead;
use crate::frontend::olean::files::Roots;
use crate::frontend::olean::records;
use crate::frontend::olean::records::ModRef;
use crate::frontend::olean::spec::OleanPins;
use crate::frontend::olean::spec::ImportRec;
use crate::kernel::core_types::CheckError;
use crate::kernel::env::CheckMode;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::nat_op_pins::NatOpPinSet;
use crate::ron::nat::Nat;

/// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
/// A step of the worker failed: its line, naming the module, and its exit code.
pub fn worker_failed<F: WorkerNotes>(fs: &F, m: &Name, e: CheckError, verified: bool) -> u8 {
    let c = check_main::exit_code(&e);
    fs.worker_note(&WorkerNote::Failed(name::dup(m), e, verified));
    c
}

/// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
/// **What the worker checks**: the pins interned (before the reads: the pin
/// ground reads the interned variants), phases 1-4 (`worker::worker_read`, every
/// read through `sp`, the imports `x` added to the header), the heartbeat's lines about it at the
/// run's one check, the ground hoist's receipt, and the jobs' records (the
/// context, then the own records); a failure's exit code.
pub fn module_read<F: CheckerFs + WorkerNotes>(
    fs: &F,
    pers: &PersTier,
    st: &mut AState,
    sp: &Roots,
    m: &crate::arena::handle::NIdx,
    m_name: &Name,
    x: &Vec<ImportRec>,
    pins: &Vec<NatOpPinSet>,
    max_nat_size: &Nat,
    verified: bool,
    who: &Option<Name>,
    pace: &crate::frontend::pace::Pace,
) -> Result<(WorkerRead, Vec<INatOpPinSet>, Vec<IDeclaration>), u8> {
    // ConRon.Capstone: h5
    let ipins = match checker::intern_all_pins(pers, st, pins, max_nat_size) {
        Err(e) => return Err(worker_failed(fs, m_name, e, verified)),
        Ok(p) => p,
    };
    // ConRon.Capstone: hwork
    let w: WorkerRead = match worker::worker_read(fs, pers, st, sp, &ipins, m, x) {
        Err((e, _)) => return Err(worker_failed(fs, m_name, e, verified)),
        Ok(w) => w,
    };
    match who {
        None => fs.worker_read_done(pace, m_name, &w),
        Some(_) => (),
    }
    if w.hoisted.len() > 0 {
        fs.worker_hoisted(who, pers, &st.store, &w.hoisted);
    }
    // ConRon.Capstone: hds
    let ds: Vec<IDeclaration> = worker::worker_decls(&w);
    Ok((w, ipins, ds))
}

/// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
/// **The imports a run adds to the module's header**: none, or at a compared
/// challenge `import all` of its solution (`graph::solution_import`), the
/// solution's name interned after the module's; a failure's exit code.
pub fn added_imports<F: WorkerNotes>(
    fs: &F,
    pers: &PersTier,
    st: &mut AState,
    m_name: &Name,
    sol: Option<&Name>,
    verified: bool,
) -> Result<Vec<ImportRec>, u8> {
    match sol {
        None => Ok(Vec::new()),
        Some(s) => match monad::intern_name(pers, st, s) {
            Err(e) => Err(worker_failed(fs, m_name, e, verified)),
            Ok(sh) => {
                let mut x: Vec<ImportRec> = Vec::new();
                x.push(mgraph::solution_import(&sh));
                Ok(x)
            }
        },
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
/// **After an accept, a compared challenge's copies** (`copyRecs`, `copyLine`,
/// the instance's lines): none where no import was added; the exit code, a
/// failure's if the copies' lines could not be made.
pub fn module_copies<F: WorkerNotes>(
    fs: &F,
    who: &Option<Name>,
    m_name: &Name,
    pers: &PersTier,
    st: &mut AState,
    x: &Vec<ImportRec>,
    w: &WorkerRead,
    c: u8,
    verified: bool,
) -> u8 {
    if c != 0 {
        return c;
    }
    if x.len() == 0 {
        return 0;
    }
    match fs.worker_copies(who, m_name, pers, st, x, w) {
        Some(e) => worker_failed(fs, m_name, e, verified),
        None => 0,
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
/// **The worker's verdict**: the failure line and its exit code, or the accept
/// line (the own records' count) and 0; the module named unless it is the run's
/// one check.
pub fn module_verdict<F: WorkerNotes>(
    fs: &F,
    who: &Option<Name>,
    pers: &PersTier,
    st: &AState,
    ds: &Vec<IDeclaration>,
    own: usize,
    verdict: Result<IStreamIndex, (CheckError, u64)>,
    verified: bool,
) -> u8 {
    match verdict {
        Err((e, i)) => {
            let c = check_main::exit_code(&e);
            fs.worker_verdict_failure(who, pers, &st.store, ds, &e, i, verified);
            c
        }
        Ok(_) => {
            let w = match who {
                None => None,
                Some(n) => Some(name::dup(n)),
            };
            fs.worker_note(&WorkerNote::Accepted(w, own as u64, verified));
            0
        }
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
/// The jobs of a module's check phase: those from `start`, `n` of them.
pub fn module_jobs(ds: &Vec<IDeclaration>, start: usize) -> usize {
    let m = ds.len();
    if start <= m {
        m - start
    } else {
        0
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
/// con-leche: ConLeche/Driver/CheckMain.lean:154-177 checkOleansG
/// **The check phase of the run's one module**: the index over every record from
/// 0 (the context's records visible to every job), the frozen tier, the reach's
/// inferred flags on a worker's state over it, then the jobs from `start` on the
/// instance's worker map; the tier thawed.
pub fn module_phase<I: CheckerIo>(
    io: &mut I,
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    ipins: &Vec<INatOpPinSet>,
    w: &WorkerRead,
    ds: &Vec<IDeclaration>,
    sp: &Roots,
    jobs: u64,
) -> Result<IStreamIndex, (CheckError, u64)> {
    io.index_starts();
    // ConRon.Capstone: h6
    let ix = match stream_index::build_index(pers, st, stream_index::stream_index_empty(), ds, 0) {
        Err(e) => return Err(e),
        Ok(ix) => ix,
    };
    io.parse_done(pers, &st.store, ds.len(), 0, 0);
    let start = w.start;
    let n = module_jobs(ds, start);
    let workers = check_main::workers_for(jobs, n);
    io.check_starts(n, workers);
    // ConRon.Capstone: h7
    let tier: PersTier = checker::freeze_tier(&mut st.store, ix);
    // ConRon.Capstone: hws, hinfer
    let mut fws: AState = checker::worker_state(&st.pins);
    match reach::infer_flags(&tier, &mut fws, &w.reach.ctx, &w.reach.pending) {
        Err(e) => {
            let _ = checker::thaw_tier(&mut st.store, tier);
            return Err((e, start as u64));
        }
        Ok(()) => (),
    }
    // ConRon.Capstone: h8
    let r = {
        let step = OleanJobStep { tier: &tier, mode, pins: ipins, apins: &st.pins, ds, pk: &w.pins, values: &w.values, sp, sol: None, start };
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

/// con-leche: ConLeche/Driver/CheckPool.lean:128-135 runAt
/// The jobs at `start + k` for `k` from `k` below `n`, in order, on one worker
/// state (`olean_job`): the first failure, or `Ok` (the worker map at one
/// worker).
pub fn jobs_in_order<F: CheckerFs>(
    fs: &F,
    tier: &PersTier,
    w: &mut AState,
    cache: &mut records::ValueCache,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
    pk: &OleanPins,
    values: &Vec<ModRef>,
    sp: &Roots,
    start: usize,
    k: usize,
    n: usize,
) -> Result<(), (CheckError, u64)> {
    let mut k = k;
    while k < n {
        match check_main::olean_job(fs, tier, w, cache, mode, pins, ds, pk, values, sp, None, start + k) {
            Err(e) => return Err(e),
            Ok(()) => (),
        }
        k += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
/// **The check phase of a module of `--modular`**: `module_phase` with the jobs
/// in order on the module's own thread, and no heartbeat.
pub fn module_phase_in<F: CheckerFs>(
    fs: &F,
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    ipins: &Vec<INatOpPinSet>,
    w: &WorkerRead,
    ds: &Vec<IDeclaration>,
    sp: &Roots,
) -> Result<IStreamIndex, (CheckError, u64)> {
    // ConRon.Capstone: h6
    let ix = match stream_index::build_index(pers, st, stream_index::stream_index_empty(), ds, 0) {
        Err(e) => return Err(e),
        Ok(ix) => ix,
    };
    let start = w.start;
    let n = module_jobs(ds, start);
    // ConRon.Capstone: h7
    let tier: PersTier = checker::freeze_tier(&mut st.store, ix);
    // ConRon.Capstone: hws, hinfer
    let mut fws: AState = checker::worker_state(&st.pins);
    match reach::infer_flags(&tier, &mut fws, &w.reach.ctx, &w.reach.pending) {
        Err(e) => {
            let _ = checker::thaw_tier(&mut st.store, tier);
            return Err((e, start as u64));
        }
        Ok(()) => (),
    }
    // ConRon.Capstone: h8 (one worker: `oleanWorkerInit`, the jobs in order)
    let mut ws: AState = checker::worker_state(&st.pins);
    let mut cache = records::value_cache_empty();
    let r = jobs_in_order(fs, &tier, &mut ws, &mut cache, mode, ipins, ds, &w.pins, &w.values, sp, start, 0, n);
    let ix: IStreamIndex = checker::thaw_tier(&mut st.store, tier);
    match r {
        Ok(()) => Ok(ix),
        Err(e) => Err(e),
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
/// con-leche: ConLeche/Driver/Dispatch.lean:63-87 runReq
/// **`--olean --module`**: the worker of `m_name` as the run's one check, every
/// module read through `sp` (the trusted path, then the search path), from
/// fresh start values; with `sol` (`--compare`) the compare worker, `import all`
/// of the solution added to the header and the copies listed after the accept;
/// the verdict.
pub fn check_module<I: CheckerIo>(io: &mut I, a: &Args, sp: &Roots, m_name: &Name, sol: Option<&Name>) -> u8 {
    let verified = a.verified;
    let mode = if verified { CheckMode::Verified } else { CheckMode::Trusted };
    let mut st = AState::empty();
    let pers = PersTier::empty();
    // ConRon.Capstone: h1
    match pins::intern_reserved_pins(&pers, &mut st) {
        Err(e) => return worker_failed(&*io, m_name, e, verified),
        Ok(()) => (),
    }
    io.module_starts(&a.progress, m_name);
    // ConRon.Capstone: hroot
    let m = match monad::intern_name(&pers, &mut st, m_name) {
        Err(e) => return worker_failed(&*io, m_name, e, verified),
        Ok(m) => m,
    };
    // ConRon.Capstone: hsol
    let x: Vec<ImportRec> = match added_imports(&*io, &pers, &mut st, m_name, sol, verified) {
        Err(c) => return c,
        Ok(x) => x,
    };
    // ConRon.Capstone: hpins
    let pins: Vec<NatOpPinSet> = match check_main::embedded_pins(&*io) {
        None => return 3,
        Some(ps) => ps,
    };
    let (w, ipins, ds) = match module_read(&*io, &pers, &mut st, sp, &m, m_name, &x, &pins, &a.max_nat_size, verified, &None, &a.progress) {
        Err(c) => return c,
        Ok(r) => r,
    };
    let jobs: u64 = check_main::jobs_for_run(io, a);
    let verdict = module_phase(io, &pers, &mut st, &mode, &ipins, &w, &ds, sp, jobs);
    let c = module_verdict(&*io, &None, &pers, &st, &ds, w.own.len(), verdict, verified);
    module_copies(&*io, &None, m_name, &pers, &mut st, &x, &w, c, verified)
}

/// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
/// **One module of `--olean --modular`**: its worker from fresh start values,
/// every line naming it, the embedded pins, its jobs in order on this thread;
/// with `sol`, the compare worker; the exit code.
pub fn check_module_in<F: CheckerFs + WorkerNotes>(
    fs: &F,
    sp: &Roots,
    m_name: &Name,
    sol: Option<&Name>,
    verified: bool,
    max_nat_size: &Nat,
) -> u8 {
    let mode = if verified { CheckMode::Verified } else { CheckMode::Trusted };
    let mut st = AState::empty();
    let pers = PersTier::empty();
    // ConRon.Capstone: h1
    match pins::intern_reserved_pins(&pers, &mut st) {
        Err(e) => return worker_failed(fs, m_name, e, verified),
        Ok(()) => (),
    }
    // ConRon.Capstone: hroot
    let m = match monad::intern_name(&pers, &mut st, m_name) {
        Err(e) => return worker_failed(fs, m_name, e, verified),
        Ok(m) => m,
    };
    // ConRon.Capstone: hsol
    let x: Vec<ImportRec> = match added_imports(fs, &pers, &mut st, m_name, sol, verified) {
        Err(c) => return c,
        Ok(x) => x,
    };
    // ConRon.Capstone: hpins
    let pins: Vec<NatOpPinSet> = match check_main::embedded_pins(fs) {
        None => return 3,
        Some(ps) => ps,
    };
    let who = Some(name::dup(m_name));
    let (w, ipins, ds) = match module_read(fs, &pers, &mut st, sp, &m, m_name, &x, &pins, max_nat_size, verified, &who, &crate::frontend::pace::Pace::Off) {
        Err(c) => return c,
        Ok(r) => r,
    };
    let verdict = module_phase_in(fs, &pers, &mut st, &mode, &ipins, &w, &ds, sp);
    let c = module_verdict(fs, &who, &pers, &st, &ds, w.own.len(), verdict, verified);
    module_copies(fs, &who, m_name, &pers, &mut st, &x, &w, c, verified)
}
