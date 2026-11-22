//! `std_io` — the binary's instance of the core's `CheckerIo` (DESIGN.md §3.9,
//! task #171): the file reads, the worker map, the escapes, and the rendering
//! of every event the verified driver (`con_ron_core::driver`) hands it, in the
//! binary's words.  All of it is outside the theorems; what they assume of it
//! is OVERVIEW §8.2's driver row: its reads answer as one snapshot of the files
//! (`AnswersAs`), its worker map keeps `ParallelAll` (`PoolSound`), its escapes
//! write no file and do not end the process.
//!
//! The text of a usage error, of a help or a synopsis, and the legacy driver
//! are the binary's (`bin/con-ron.rs`), handed in as `StdIoHooks`.

use std::io::Write;
use std::sync::Mutex;
use std::time::Instant;

use con_ron_core::arena::env::IDeclaration;
use con_ron_core::arena::handle::NIdx;
use con_ron_core::arena::justify::Solution;
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::store::EStore;
use con_ron_core::arena::store::PersTier;
use con_ron_core::arena::stream_index::IStreamIndex;
use con_ron_core::driver::check_main::Note;
use con_ron_core::driver::cli::Bad;
use con_ron_core::frontend::checker_io::{CheckerFs, CheckerIo, CodeStep, Step, WorkerNote, WorkerNotes};
use con_ron_core::frontend::modular::worker::WorkerRead;
use con_ron_core::frontend::olean::progress;
use con_ron_core::frontend::olean::spec::ImportRec;
use con_ron_core::frontend::pace::{pace_dup, pace_on, Pace};
use con_ron_core::kernel::name::Name;
use con_ron_core::ron::hashmap::Dup;
use con_ron_core::ron::hashmap2::HashMap2;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;

use crate::driver;
use crate::driver::{Heartbeat, PhaseObserver};
use crate::olean_fs;
use crate::olean_fs::path_of;
use crate::olean_fs::{NotesFs, StdFs};
use crate::pool::parallel_all;
use crate::render;

/// con-leche: none — the binary's own text and its legacy driver, which the
/// instance renders with and hands requests to.
pub struct StdIoHooks {
    /// `--help`: print the help, the exit code
    pub help: fn() -> u8,
    /// no arguments: print the invocation forms and the pointer to `--help`
    pub synopsis: fn(),
    /// a usage error's two lines, for its message
    pub usage: fn(&str) -> u8,
    /// a request the verified driver does not run: the legacy driver
    pub legacy: fn(Vec<String>) -> u8,
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:515-531 instCheckerIOIO
/// **The binary's instance.**
pub struct StdIo {
    hooks: StdIoHooks,
    /// the start of the run, which the verdict's `t=` is measured from
    t0: Instant,
    /// the `.olean` read's heartbeat while a read is on (`read_notes_begin`)
    notes: Mutex<Option<NotesFs>>,
    /// the heartbeat, and the jobs done in the current check phase
    hb: Mutex<(Heartbeat, usize)>,
    /// what the run built, kept to the process's exit (con-leche task #336)
    kept: Mutex<Vec<(AState, Vec<IDeclaration>, Option<IStreamIndex>)>>,
    /// what a compared run built besides its store, kept the same way
    kept_solutions: Mutex<Vec<(Vec<IDeclaration>, Vec<IDeclaration>, Solution)>>,
}

/// con-leche: ConLeche/Driver/CheckMain.lean:64-67 Input.label
/// The roots of an `.olean` run, as its lines name them.
fn roots_label(roots: &Vec<Name>) -> String {
    let shown: Vec<String> = roots.iter().map(render::name_str).collect();
    shown.join(" ")
}

/// con-leche: none — a mode's tag on a line
fn mode_tag(verified: bool) -> &'static str {
    if verified {
        "--verified"
    } else {
        "--trusted"
    }
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:515-531 instCheckerIOIO
impl StdIo {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:515-531 instCheckerIOIO
    /// The instance, its clock started now.
    pub fn new(hooks: StdIoHooks) -> StdIo {
        let t0 = Instant::now();
        StdIo {
            hooks,
            t0,
            notes: Mutex::new(None),
            hb: Mutex::new((Heartbeat::new(Pace::Off, t0), 0)),
            kept: Mutex::new(Vec::new()),
            kept_solutions: Mutex::new(Vec::new()),
        }
    }

    /// con-leche: none — the heartbeat, locked; a poisoned lock is a panicked
    /// worker's, and its line is dropped
    fn with_hb<R>(&self, f: impl FnOnce(&mut Heartbeat) -> R) -> Option<R> {
        match self.hb.lock() {
            Ok(mut g) => Some(f(&mut g.0)),
            Err(_) => None,
        }
    }
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:515-531 instCheckerIOIO
impl CheckerFs for StdIo {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:141-200 CheckerIO
    fn path_exists(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>> {
        StdFs.path_exists(p)
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:141-200 CheckerIO
    fn is_dir(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>> {
        StdFs.is_dir(p)
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:141-200 CheckerIO
    fn real_path(&self, p: &Vec<u32>) -> Result<Vec<u32>, Vec<u32>> {
        StdFs.real_path(p)
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:141-200 CheckerIO
    fn read_bin_file(&self, p: &Vec<u32>) -> Result<Vec<u8>, Vec<u32>> {
        StdFs.read_bin_file(p)
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:403-409 openReadIO
    /// **A positional read** (`olean_fs::StdFs`'s): the path must name a regular
    /// file, decided before it is opened (opening a FIFO with no writer would
    /// block), then a seek and forward reads on a handle of this call's own.  A
    /// failure's message names the path.
    fn read_range(&self, p: &Vec<u32>, off: u64, len: u64) -> Result<Vec<u8>, Vec<u32>> {
        StdFs.read_range(p, off, len)
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:141-200 CheckerIO
    fn file_size(&self, p: &Vec<u32>) -> Result<u64, Vec<u32>> {
        StdFs.file_size(p)
    }

    /// con-leche: ConLeche/Frontend/Olean/Progress.lean:42-48 ReadNotes.say
    /// A line of the `.olean` read's heartbeat while a read is on; silent
    /// otherwise (a worker's reads, a job's).
    fn read_notes_say(&self, line: &Vec<u32>) {
        if let Ok(g) = self.notes.lock() {
            if let Some(n) = &*g {
                n.read_notes_say(line);
            }
        }
    }

    /// con-leche: ConLeche/Frontend/Olean/Progress.lean:50-60 ReadNotes.moduleLoaded
    /// As `read_notes_say`.
    fn read_notes_module_loaded(&self, total: u64, size: u64) {
        if let Ok(g) = self.notes.lock() {
            if let Some(n) = &*g {
                n.read_notes_module_loaded(total, size);
            }
        }
    }
}

/// con-leche: none — a worker's `who`: the module it names, or none
fn who_text(who: &Option<Name>) -> String {
    match who {
        None => String::new(),
        Some(m) => format!("module {}: ", render::name_str(m)),
    }
}

/// con-leche: none — a code-point message as a Rust `String`
fn text(s: &[u32]) -> String {
    s.iter().filter_map(|c| char::from_u32(*c)).collect()
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:515-531 instCheckerIOIO
impl WorkerNotes for StdIo {
    /// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
    fn worker_note(&self, n: &WorkerNote) {
        match n {
            WorkerNote::Failed(m, e, v) => eprintln!(
                "con-ron: module {}: {} ({})",
                render::name_str(m),
                driver::error_text(e),
                mode_tag(*v)
            ),
            WorkerNote::EmbeddedPins(e) => eprintln!("con-ron: embedded pin text: {}", driver::message(e)),
            WorkerNote::Accepted(who, n, v) => {
                println!("con-ron: {}accepted {} declarations ({})", who_text(who), n, mode_tag(*v))
            }
        }
    }

    /// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
    fn module_starts(&self, pace: &Pace, m: &Name) {
        let label = format!("module {}", render::name_str(m));
        self.with_hb(|hb| {
            hb.pace = pace_dup(pace);
            hb.read_starts(&label)
        });
    }

    /// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
    /// The heartbeat's three lines about what the worker read, at a pace that is
    /// on: the home, the loads, the reach.
    fn worker_read_done(&self, pace: &Pace, m: &Name, w: &WorkerRead) {
        if !pace_on(pace) {
            return;
        }
        let say = |line: String| {
            let ms = self.t0.elapsed().as_millis() as u64;
            let t = progress::read_line_text(&render::cps(&line), ms, &olean_fs::resident_set());
            eprintln!("con-ron: {}", text(&t));
        };
        let m_text = render::name_str(m);
        say(format!("the home of {}: {} constants, views checked", m_text, w.home.constants.len()));
        say(format!(
            "loads {} modules, {} names; {} names held twice, merged",
            w.reads.loads.order.len(),
            w.reads.index.first.len(),
            w.reads.clashes.len()
        ));
        let mut homes: HashMap2<NIdx, bool> = HashMap2::new();
        for h in &w.reach.homes {
            homes.insert(h.dup2(), true);
        }
        say(format!(
            "reach: {} records from {} modules, {} completed, {} flags inferred",
            w.reach.ctx.len(),
            homes.len(),
            w.reach.completed.len(),
            w.reach.inferred
        ));
    }

    /// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
    fn worker_hoisted(&self, who: &Option<Name>, pers: &PersTier, ar: &EStore, names: &Vec<NIdx>) {
        let ns: Vec<String> = names.iter().map(|n| driver::name_of(pers, ar, n)).collect();
        eprintln!(
            "con-ron: {}{} declarations hoisted ahead of the pinned Nat operations they ground: {}",
            who_text(who),
            names.len(),
            ns.join(", ")
        );
    }

    /// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
    fn worker_verdict_failure(&self, who: &Option<Name>, pers: &PersTier, ar: &EStore, ds: &Vec<IDeclaration>, e: &CheckError, i: u64, verified: bool) {
        let _ = driver::verdict_failure(pers, ar, ds, e, i, mode_tag(verified), self.t0, &who_text(who));
    }
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:515-531 instCheckerIOIO
impl CheckerIo for StdIo {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:491-513 parMapWorkersIO
    /// `pool::parallel_all` over `st`, the heartbeat's check line after each job
    /// (`jobEnd`: the count and its line under one lock, so the lines leave in
    /// count order), the pool's own failures internal errors
    /// (`driver::pool_verdict`).
    fn par_map_workers<S: Send, St: Step<Self, S> + Sync>(
        &mut self,
        st: &St,
        n: usize,
        workers: usize,
    ) -> Result<(), (CheckError, u64)> {
        let me: &StdIo = &*self;
        let heartbeat = match me.hb.lock() {
            Ok(mut g) => {
                g.1 = 0;
                g.0.wants_check_lines()
            }
            Err(_) => false,
        };
        let r = parallel_all(
            n,
            workers,
            || st.init(),
            |w: &mut S, k| st.step(me, w, k),
            |w: &S, k| {
                if heartbeat {
                    if let Ok(mut g) = me.hb.lock() {
                        g.1 += 1;
                        let done = g.1;
                        let (tier, ar, ds, off) = st.view(w);
                        g.0.check_after(tier, ar, done, n, ds, off + k);
                    }
                }
            },
        );
        driver::pool_verdict(r)
    }

    /// con-leche: ConLeche/Driver/Modular.lean:90-137 checkModularG
    /// The modules on up to `threads` threads of `driver::stack_bytes` each,
    /// each claiming the next until none is left (fewer threads where no more
    /// can be started); every module run.  None started, or one died: the
    /// message.
    fn par_map_codes<St: CodeStep<Self> + Sync>(&mut self, st: &St, n: usize, threads: usize) -> Result<Vec<u8>, Vec<u32>> {
        let me: &StdIo = &*self;
        let next = std::sync::atomic::AtomicUsize::new(0);
        let codes: Vec<Mutex<Option<u8>>> = (0..n).map(|_| Mutex::new(None)).collect();
        let spawned = std::thread::scope(|sc| -> Result<(), String> {
            let mut hs = Vec::with_capacity(threads);
            for _ in 0..threads {
                let h = std::thread::Builder::new().stack_size(driver::stack_bytes()).spawn_scoped(sc, || loop {
                    let k = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    if k >= n {
                        break;
                    }
                    let c = st.code(me, k);
                    if let Ok(mut g) = codes[k].lock() {
                        *g = Some(c);
                    }
                });
                // a thread that cannot be started (the 1 GiB stacks against `ulimit -v`)
                // leaves the modules to the threads that did start
                match h {
                    Ok(h) => hs.push(h),
                    Err(e) => {
                        if hs.is_empty() {
                            return Err(e.to_string());
                        }
                        break;
                    }
                }
            }
            for h in hs {
                if h.join().is_err() {
                    return Err("a module's thread died".to_string());
                }
            }
            Ok(())
        });
        if let Err(e) = spawned {
            return Err(render::cps(&e));
        }
        let mut out: Vec<u8> = Vec::with_capacity(n);
        for c in codes.iter() {
            out.push(match c.lock() {
                Ok(g) => g.unwrap_or(3),
                Err(_) => 3,
            });
        }
        Ok(out)
    }

    /// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
    fn print_help(&mut self) -> u8 {
        (self.hooks.help)()
    }

    /// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
    fn run_legacy(&mut self, argv: &Vec<Vec<u32>>) -> u8 {
        (self.hooks.legacy)(argv.iter().map(|a| path_of(a)).collect())
    }

    /// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
    fn hardware_jobs(&mut self) -> u64 {
        driver::default_jobs()
    }

    /// con-leche: none — `driver::pins_for_run`'s `--pins FILE`
    fn read_pins_file(&mut self, p: &Vec<u32>) -> Result<Vec<NatOpPinSet>, Vec<u32>> {
        driver::pins_for_run(&Some(path_of(p)), false).map_err(|m| render::cps(&m))
    }

    /// con-leche: none — con-leche task #336
    fn keep_heap(&mut self, st: AState, ds: Vec<IDeclaration>, ix: Option<IStreamIndex>) {
        if let Ok(mut g) = self.kept.lock() {
            g.push((st, ds, ix));
        }
    }

    /// con-leche: none — con-leche task #336
    fn keep_solution(&mut self, ds_s: Vec<IDeclaration>, ds_c: Vec<IDeclaration>, sol: Solution) {
        if let Ok(mut g) = self.kept_solutions.lock() {
            g.push((ds_s, ds_c, sol));
        }
    }

    /// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
    /// A usage error in the binary's words: the flag values' messages are
    /// `driver`'s own functions', so the two parses cannot drift apart.
    fn usage(&self, b: &Bad) {
        let msg: String = match b {
            Bad::PinsNoFile => "--pins takes a file: --pins FILE".to_string(),
            Bad::JobsBare => "--jobs takes a worker count: --jobs=<n>; omit the flag for one worker \
                 per hardware thread"
                .to_string(),
            Bad::ProgressValue(v) => match driver::progress_pace(&path_of(v)) {
                Err(m) => m,
                Ok(_) => String::new(),
            },
            Bad::JobsZero => match driver::jobs_count("0") {
                Err(m) => m,
                Ok(_) => String::new(),
            },
            Bad::JobsValue(v) => match driver::jobs_count(&path_of(v)) {
                Err(m) => m,
                Ok(_) => String::new(),
            },
            Bad::MaxNatValue(v) => match driver::max_nat_size_arg(&path_of(v)) {
                Err(m) => m,
                Ok(_) => String::new(),
            },
            Bad::WorkerStackValue(v) => format!(
                "--worker-stack-size takes a size with a unit, K, M, G or T (e.g. 8G), got {}",
                render::display_str(&path_of(v))
            ),
            Bad::UnknownOption(s) => format!("unknown option {}", render::display_str(&path_of(s))),
            Bad::WorkerStackNoSchedule => "--worker-stack-size takes --schedule".to_string(),
            Bad::TakeOlean => "--search-path, --trusted-search-path, --constant, --module, --modular and \
                 --schedule take --olean"
                .to_string(),
            Bad::OneInputFile => "takes one input file".to_string(),
            Bad::CheckGraphFlags => "--check-graph takes none of --olean, --module and --constant, and \
                 --trusted-search-path only with --compare"
                .to_string(),
            Bad::CheckGraphArgs => "--check-graph takes one or more module names and a --search-path=DIRS".to_string(),
            Bad::NotModuleName(f) => format!("not a module name: {}", render::display_str(&path_of(f))),
            Bad::OleanArgs => "--olean takes one or more module names and a --search-path=DIRS".to_string(),
            Bad::NotConstName(c) => format!("not a constant's name: {}", render::display_str(&path_of(c))),
            Bad::TrustedTakes => "--trusted-search-path takes --compare or --module".to_string(),
            Bad::ModularArgs => "--modular takes one module name, and neither --constant nor --module".to_string(),
            Bad::ModuleArgs => "--module takes one module name and no --constant".to_string(),
            Bad::CompareTakeOlean => "--compare on two lean4export files takes none of --search-path, \
                 --trusted-search-path, --constant, --module, --modular and --schedule \
                 (they take --olean)"
                .to_string(),
            Bad::CompareTwoFiles => "--compare takes two files, a challenge and its solution".to_string(),
            Bad::CompareSameFile => "--compare takes two different files, a challenge and its solution".to_string(),
        };
        let _ = (self.hooks.usage)(&msg);
    }

    /// con-leche: ConLeche/Driver/CheckMain.lean:70-75 diagLine
    /// A line in the binary's words.
    fn note(&self, n: &Note) {
        match n {
            Note::Synopsis => (self.hooks.synopsis)(),
            Note::ReservedPins(e, v) => eprintln!(
                "con-ron: the reserved-name pins do not intern ({}) ({})",
                driver::message(e),
                mode_tag(*v)
            ),
            Note::Prelude(e, line, v) => {
                let m = driver::message(e);
                let what = match e {
                    CheckError::Internal(_) => format!("does not parse (line {}: {})", line, m),
                    CheckError::NotImplemented(_) | CheckError::Native(_) => format!("is unsupported ({})", m),
                    CheckError::Invalid(_) => format!("contradicts itself ({})", m),
                };
                eprintln!(
                    "con-ron: the built-in prelude {}; regenerate it with \
                     `lake exe natop-pins-export` ({})",
                    what,
                    mode_tag(*v)
                );
            }
            // the read's message names the file (`read_range`'s)
            Note::ReadFailed(_, m) => eprintln!("con-ron: {}", path_of(m)),
            Note::Parse(e, line, p, v) => {
                let m = driver::message(e);
                match e {
                    CheckError::NotImplemented(_) | CheckError::Native(_) => {
                        eprintln!("con-ron: declined: {} ({})", m, mode_tag(*v))
                    }
                    CheckError::Invalid(_) => eprintln!("con-ron: invalid: {} ({})", m, mode_tag(*v)),
                    CheckError::Internal(_) => {
                        eprintln!("con-ron: {}:{}: {}", render::display_path(&path_of(p)), line, m)
                    }
                }
            }
            Note::Frontend(e, v) => {
                let m = driver::message(e);
                match e {
                    CheckError::NotImplemented(_) | CheckError::Native(_) => {
                        eprintln!("con-ron: declined: {} ({})", m, mode_tag(*v))
                    }
                    CheckError::Invalid(_) => eprintln!("con-ron: invalid: {} ({})", m, mode_tag(*v)),
                    CheckError::Internal(_) => eprintln!("con-ron: {} ({})", m, mode_tag(*v)),
                }
            }
            Note::PinsFile(m) => eprintln!("con-ron: {}", path_of(m)),
            Note::EmbeddedPins(e) => eprintln!("con-ron: embedded pin text: {}", driver::message(e)),
            Note::Accepted(records, v) => {
                let _ = driver::verdict_accept(*records, mode_tag(*v));
            }
            Note::OleanRead(e, line, roots, v) => {
                let m = driver::message(e);
                match e {
                    CheckError::NotImplemented(_) | CheckError::Native(_) => {
                        eprintln!("con-ron: declined: {} ({})", m, mode_tag(*v))
                    }
                    CheckError::Invalid(_) => eprintln!("con-ron: invalid: {} ({})", m, mode_tag(*v)),
                    CheckError::Internal(_) => eprintln!("con-ron: {}:{}: {}", roots_label(roots), line, m),
                }
            }
            Note::GraphPins(e) => {
                eprintln!("con-ron: the reserved-name pins do not intern ({})", driver::message(e))
            }
            Note::GraphFailed(e) => eprintln!("con-ron: graph: {}", driver::error_text(e)),
            Note::ModularGraph(n) => eprintln!("con-ron: modular: graph: acyclic, {} modules", n),
            Note::ModularThreads(m) => eprintln!("con-ron: modular: {}", path_of(m)),
            Note::ModularDone => eprintln!("con-ron: modular: done"),
            Note::ModularAccepted(n, v) => println!("con-ron: accepted {} modules ({})", n, mode_tag(*v)),
            Note::ModularFailed(k, n, m, v) => eprintln!(
                "con-ron: {} of {} modules not accepted; the first in the graph's order: {} ({})",
                k,
                n,
                render::name_str(m),
                mode_tag(*v)
            ),
        }
    }

    /// con-leche: ConLeche/Driver/Run.lean:33-36 readStarts
    fn read_starts(&self, pace: &Pace, path: &Vec<u32>) {
        let label = render::display_path(&path_of(path));
        self.with_hb(|hb| {
            hb.pace = pace_dup(pace);
            hb.read_starts(&label)
        });
    }

    /// con-leche: ConLeche/Driver/Run.lean:33-36 readStarts
    fn oleans_read_starts(&self, pace: &Pace, roots: &Vec<Name>) {
        let label = roots_label(roots);
        self.with_hb(|hb| {
            hb.pace = pace_dup(pace);
            hb.read_starts(&label)
        });
    }

    /// con-leche: ConLeche/Frontend/Olean/Progress.lean:27-28 ReadNotes.new
    fn read_notes_begin(&self, pace: &Pace) {
        if let Ok(mut g) = self.notes.lock() {
            *g = Some(olean_fs::read_notes_new(pace));
        }
    }

    /// con-leche: ConLeche/Frontend/Olean/Records.lean:108-138 readOleansAt
    fn read_notes_end(&self) {
        if let Ok(mut g) = self.notes.lock() {
            *g = None;
        }
    }

    /// con-leche: ConLeche/Driver/Graph.lean:240-251 checkGraphG
    fn graph_accepted(&self, c: &Vec<(NIdx, Vec<ImportRec>)>) {
        let edges: usize = c.iter().map(|e| e.1.len()).sum();
        println!("con-ron: graph: acyclic: {} modules, {} import edges", c.len(), edges);
    }

    /// con-leche: ConLeche/Driver/CheckMain.lean:268-458 checkMainG
    fn hoisted(&self, pers: &PersTier, ar: &EStore, names: &Vec<NIdx>) {
        let ns: Vec<String> = names.iter().map(|n| driver::name_of(pers, ar, n)).collect();
        eprintln!(
            "con-ron: {} declarations hoisted ahead of the pinned Nat operations \
             they ground: {}",
            names.len(),
            ns.join(", ")
        );
    }

    /// con-leche: ConLeche/Driver/CheckMain.lean:268-458 checkMainG
    fn index_starts(&self) {
        self.with_hb(|hb| hb.index_starts());
    }

    /// con-leche: ConLeche/Driver/CheckMain.lean:268-458 checkMainG
    fn parse_done(&self, pers: &PersTier, ar: &EStore, fold: usize, file: usize, synthesised: u64) {
        self.with_hb(|hb| {
            hb.file_records = file;
            hb.synthesised = synthesised;
            hb.parse_done(pers, ar, fold)
        });
    }

    /// con-leche: ConLeche/Driver/Run.lean:49-55 checkStarts
    fn check_starts(&self, m: usize, workers: usize) {
        self.with_hb(|hb| hb.check_starts(m, workers));
    }

    /// con-leche: ConLeche/Driver/Run.lean:57-83 checkDone
    fn check_done(&self, m: usize, failure: &Option<u64>) {
        self.with_hb(|hb| hb.check_done(m, *failure));
    }

    /// con-leche: ConLeche/Driver/CheckMain.lean:180-266 verdictG
    fn verdict_failure(&self, pers: &PersTier, ar: &EStore, ds: &Vec<IDeclaration>, e: &CheckError, i: u64, verified: bool) {
        let _ = driver::verdict_failure(pers, ar, ds, e, i, mode_tag(verified), self.t0, "");
    }

    /// con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
    fn solution_failure(
        &self,
        pers: &PersTier,
        ar: &EStore,
        ds: &Vec<IDeclaration>,
        e: &CheckError,
        i: u64,
        verified: bool,
        solution: &Vec<u32>,
    ) {
        let who = format!("the solution {}: ", path_of(solution));
        let _ = driver::verdict_failure(pers, ar, ds, e, i, mode_tag(verified), self.t0, &who);
    }

    /// con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
    fn compare_accepted(
        &self,
        pers: &PersTier,
        ar: &EStore,
        ds: &Vec<IDeclaration>,
        holes: &Vec<usize>,
        records: usize,
        solution: &Vec<u32>,
        records_s: usize,
        verified: bool,
    ) {
        println!(
            "con-ron: accepted {} declarations, {} axioms justified by the solution {} ({} \
             declarations accepted) ({})",
            records,
            holes.len(),
            path_of(solution),
            records_s,
            mode_tag(verified)
        );
        for k in holes {
            println!("con-ron: {} justified by the solution", driver::decl_label(pers, ar, &ds[*k]));
        }
    }
}

/// con-leche: Main.lean:32-54 flushStdoutStderr
/// The flush before the exit: both streams; the code, or 3 if the flush fails
/// (con-leche task #490).
pub fn flush_stdout_stderr(code: u8) -> u8 {
    match std::io::stdout().flush().and_then(|()| std::io::stderr().flush()) {
        Ok(()) => code,
        Err(e) => {
            let _ = writeln!(std::io::stderr(), "con-ron: cannot write the output: {}", e);
            3
        }
    }
}
