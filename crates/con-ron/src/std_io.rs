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
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::store::EStore;
use con_ron_core::arena::store::PersTier;
use con_ron_core::arena::stream_index::IStreamIndex;
use con_ron_core::driver::check_main::Note;
use con_ron_core::driver::cli::Bad;
use con_ron_core::frontend::checker_io::{CheckerFs, CheckerIo, Step};
use con_ron_core::frontend::pace::{pace_dup, Pace};
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;

use crate::driver;
use crate::driver::{Heartbeat, PhaseObserver};
use crate::olean_fs::path_of;
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

/// con-leche: ConLeche/Frontend/CheckerIO.lean:403-409 openReadIO
/// The stream's open file: the path, the handle, where its next read starts.
struct Pipe {
    path: Vec<u32>,
    file: std::fs::File,
    pos: u64,
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:515-531 instCheckerIOIO
/// **The binary's instance.**
pub struct StdIo {
    hooks: StdIoHooks,
    /// the start of the run, which the verdict's `t=` is measured from
    t0: Instant,
    /// the stream's forward reader
    pipe: Mutex<Option<Pipe>>,
    /// the heartbeat, and the jobs done in the current check phase
    hb: Mutex<(Heartbeat, usize)>,
    /// what the run built, kept to the process's exit (con-leche task #336)
    kept: Mutex<Vec<(AState, Vec<IDeclaration>, Option<IStreamIndex>)>>,
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
            pipe: Mutex::new(None),
            hb: Mutex::new((Heartbeat::new(Pace::Off, t0), 0)),
            kept: Mutex::new(Vec::new()),
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
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:403-409 openReadIO
    /// **A pipe's read**: the file is opened at offset 0 (a regular file, decided
    /// before it is opened: opening a FIFO with no writer would block) and read
    /// forward, `driver::read_up_to` filling the buffer to `len` or the end; a
    /// read at any other offset than where the last ended fails.
    fn read_range(&self, p: &Vec<u32>, off: u64, len: u64) -> Result<Vec<u8>, Vec<u32>> {
        let mut g = match self.pipe.lock() {
            Ok(g) => g,
            Err(_) => return Err(render::cps("the reader failed")),
        };
        let fresh = match &*g {
            Some(pipe) => !(pipe.path == *p && pipe.pos == off),
            None => true,
        };
        if fresh {
            if off != 0 {
                return Err(render::cps(&format!("a read at offset {} is not where the last one ended", off)));
            }
            let s = path_of(p);
            let md = std::fs::metadata(&s).map_err(|e| render::cps(&e.to_string()))?;
            if !md.is_file() {
                return Err(render::cps("not a regular file"));
            }
            let file = std::fs::File::open(&s).map_err(|e| render::cps(&e.to_string()))?;
            *g = Some(Pipe { path: p.clone(), file, pos: 0 });
        }
        let pipe = match &mut *g {
            Some(pipe) => pipe,
            None => return Err(render::cps("the reader failed")),
        };
        let mut buf: Vec<u8> = vec![0u8; len as usize];
        match driver::read_up_to(&mut pipe.file, &mut buf) {
            Ok(n) => {
                buf.truncate(n);
                pipe.pos += n as u64;
                Ok(buf)
            }
            Err(e) => {
                *g = None;
                Err(render::cps(&e.to_string()))
            }
        }
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
                        let (tier, ar, ds) = st.view(w);
                        g.0.check_after(tier, ar, done, n, ds, k);
                    }
                }
            },
        );
        driver::pool_verdict(r)
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
            Note::ReadFailed(p, m) => {
                eprintln!("con-ron: {}: {}", render::display_path(&path_of(p)), path_of(m))
            }
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
