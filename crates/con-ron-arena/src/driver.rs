//! `driver` — con-leche's `Main.lean` over the ARENA (task #97 P4f), the
//! Lean twin's `proof/ConRon/Arena/Main.lean` one representation down.
//!
//! It is `con_ron::driver` with the handles in place of the trees, and it is
//! deliberately the same module in the same order: the reads, the two phases
//! with the boundary visible, the `--progress` heartbeat behind one observer
//! trait, the verdict lines, the exit-code mapping.  What is *not* copied is
//! copied: everything that does not mention a term —
//! [`con_ron::driver::exit_code`], `verdict_word`, `message`, `ms_secs`,
//! `progress_stride`, `jobs_count`, `default_jobs`, `workers_for`,
//! `mark_persistent_note`, `read_up_to` — is called across the crate line, so
//! the two binaries' flags and exit codes cannot drift.
//!
//! ## What differs from `con_ron::driver`, and why
//!
//! 1. **The state is one `AState`** (`arena_core::arena::monad::AState`: the
//!    store, the per-call memos, the per-declaration caches), threaded as a
//!    `&mut` through the parse, the preparation, the pin walk and both phases.
//!    con-ron's driver threads a `CState` and the declarations carry their own
//!    terms; here the terms are in the state and the records are handles into
//!    it, so nothing may be run against a state that is not the one they were
//!    interned into.
//! 2. **`intern_all_pins` runs once, before the fold, with the scratch tier
//!    off** (DESIGN.md §8.6 P2d, task #97-P4d's "for P4f"): every pinned datum
//!    is in the PERSISTENT cons table before any declaration's check can
//!    intern one into a tier that is about to vanish.  Its result — the
//!    interned pin list — is the fold's parameter.
//! 3. **Phase B's bracket is `check_pending`'s**, which turns the scratch tier
//!    on and drops it.  A driver that checked records itself without it would
//!    grow the scratch tier without bound; the loop below calls it once per
//!    record and nothing else opens a tier.
//! 4. **`--jobs=<n>` is accepted, validated and today single-lane.**  con-ron's
//!    pool (`con_ron::pool`) is phase B at every count above 1; the arena's is
//!    P6's, and DESIGN.md §8.3 already says what it will be — the persistent
//!    tier is immutable in phase B and each worker owns a scratch tier and its
//!    own caches, so there are no atomics to add.  The loop below is shaped
//!    for it: phase B reads `fe` and the pending list and writes only the
//!    per-record state, so a pool slots in where the `while` is, exactly as
//!    `check_decls_driver`'s does.  A run that asks for more than one worker
//!    says on stderr that it got one.
//! 5. **No `--no-mark-persistent` note about `Arc`.**  The arena has no
//!    reference counts at all (DESIGN.md §8.5: no `Arc`, no `ron::ptr`), so
//!    the flag is accepted and ignored for a *stronger* reason than con-ron's,
//!    and [`mark_persistent_note`] says which.
//!
//! ## The read loop
//!
//! [`parse_export_handle_d`] is `ConLeche/Frontend/ExportC.lean:903-931`'s
//! `parseExportHandleD` over the arena's `chunk_step`: the handle read
//! strictly forward 4 MiB at a time, each buffer fed to the step and dropped,
//! the first empty read its end of file and `chunk_finish` the close.  Never
//! seeked, never re-opened, never asked for its size — so the source may be a
//! pipe and no scratch file exists (con-leche task #180).  It is the same fold
//! as `export_c::parse_chunks` with the reads interleaved, which is the Lean
//! twin's `readFold` and its argument for why the two are one computation.

use std::io::Read;
use std::time::Instant;

use arena_core::arena::checker;
use arena_core::arena::checker::PendingCheck;
use arena_core::arena::checker_split::ValueKind;
use arena_core::arena::env as ienv;
use arena_core::arena::env::{IDeclaration, IFEnv};
use arena_core::arena::monad::AState;
use arena_core::arena::nat_op_pin_set::INatOpPinSet;
use arena_core::arena::store::EStore;
use arena_core::frontend::export_c;
use arena_core::frontend::export_c::ParseResultD;
use arena_core::frontend::types::Modeller;

use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::CheckMode;

use con_ron::driver::{message, ms_secs};

/// con-leche: none — the Lean runtime's per-thread stack reservation, which
/// `Main.lean`'s `--jobs` note measures at 1 GiB per worker.
/// **The stack**, and the arena needs it MORE than con-ron does (task
/// #97-P4b/P4c/P4d's finding): a `check_decl` on a deep term is tens of
/// thousands of Rust frames through the knot's six mutually recursive
/// functions *and* the declaration checker's splits, and the readback of
/// `in_model` and `pins_decode::decode_embedded` recurse once per node and
/// once per record.  So the whole run is on one such thread, as `con-ron`'s
/// checker threads are.
pub const STACK_BYTES: usize = con_ron::driver::STACK_BYTES;

// ---------------------------------------------------------------------------
// Rendering: the labels the arena has to read back
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:44-48 ValueKind.word
/// The kind's word, for the check phase's heartbeat line.  `con_ron::driver`
/// has the same three words against `con_ron_core`'s `ValueKind`; the arena
/// has its own enum, so the three arms are spelled once more here rather than
/// converted.
pub fn value_kind_word(k: &ValueKind) -> &'static str {
    match k {
        ValueKind::Defn => "definition",
        ValueKind::Thm => "theorem",
        ValueKind::Opaque => "opaque",
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:267-276 declCLabel
/// con-leche: Main.lean:61-65 declCName
/// A record's display label, `con_ron::driver::decl_label`'s seven arms with
/// the names READ BACK out of the store: a handle is not a name until the
/// store is asked, which is the one thing every rendering in this crate has to
/// do that con-ron's does not.  A dangling handle renders as `?` rather than
/// failing — this is a log line, never a verdict.
pub fn decl_label(ar: &EStore, d: &IDeclaration) -> String {
    let (kind, n) = match d {
        IDeclaration::AxiomDecl(cv) => ("axiom", Some(name_of(ar, &cv.name))),
        IDeclaration::DefnDecl(cv, _, _) => ("def", Some(name_of(ar, &cv.name))),
        IDeclaration::ThmDecl(cv, _) => ("theorem", Some(name_of(ar, &cv.name))),
        IDeclaration::OpaqueDecl(cv, _) => ("opaque", Some(name_of(ar, &cv.name))),
        IDeclaration::BasisDecl(_) => ("basis", None),
        IDeclaration::IndDecl(block, _) => (
            "inductive",
            block
                .first()
                .map(|ci| name_of(ar, &ienv::i_constant_info_name(ci))),
        ),
        IDeclaration::QuotDecl(_, cv) => ("quot", Some(name_of(ar, &cv.name))),
    };
    match n {
        Some(n) => format!("{} {}", kind, n),
        None => kind.to_string(),
    }
}

/// con-leche: none — `Name.toString` of a handle, for a log line
/// A name handle, rendered.  `arena_core::arena::env::read_name` is the
/// readback and `con_ron::render::name_str` the rendering; a handle the store
/// does not know renders as `?`.
pub fn name_of(ar: &EStore, h: &arena_core::arena::handle::NIdx) -> String {
    match ienv::read_name(ar, h) {
        Ok(n) => con_ron::render::name_str(&n),
        Err(_) => "?".to_string(),
    }
}

/// con-leche: Main.lean:318-421 checkDeclsIO
/// **`--no-mark-persistent`: accepted, and a no-op** — and here for a stronger
/// reason than `con_ron::driver::mark_persistent_note`'s.  con-leche's mark
/// turns off the Lean runtime's reference counting on the installed
/// environment; con-ron's counts are `std::sync::Arc`'s, atomic by type with
/// no runtime mark to clear.  **The arena has no reference counts at all**
/// (DESIGN.md §8.5: no `Arc`, no `ron::ptr`, no `ron::tagged`): a term is a
/// `u32` handle into a `Vec`, and the persistent tier is immutable in phase B
/// by construction.  So there is nothing the flag could turn off, and a run
/// that passes it says so rather than letting a log read as an A/B lane that
/// was never run.
pub fn mark_persistent_note() -> &'static str {
    "--no-mark-persistent accepted and ignored: the persistent mark is a Lean-runtime \
     reference-counting device (Runtime.markPersistent), and the arena has no reference \
     counts to mark — a term is a u32 handle into a Vec and the persistent tier is \
     immutable in phase B (DESIGN.md section 8.5)"
}

/// con-leche: Main.lean:318-421 checkDeclsIO
/// The worker count a run reports: `max 1 (min jobs pend.size)` as con-leche
/// computes it, clamped again to ONE because phase B is single-lane here (the
/// module note's item 4).  The requested count is kept so that the summary can
/// say what was asked for and what was run.
pub fn workers_for(jobs: u64, m: usize) -> usize {
    let _ = con_ron::driver::workers_for(jobs, m);
    1
}

// ---------------------------------------------------------------------------
// The two phases (`Main.lean:67-141 installLoop`, `:160-191 checkLoop`)
// ---------------------------------------------------------------------------

/// con-leche: Main.lean:143-158 checkHeartbeat
/// con-leche: Main.lean:318-421 checkDeclsIO
/// What a caller wants to know between the steps of the fold —
/// `con_ron::driver::PhaseObserver` over the arena's records, with the store
/// passed to every method because a handle is not a label until the store is
/// asked.  Every method defaults to nothing, so a caller implements the lines
/// it prints and no more.
pub trait PhaseObserver {
    /// con-leche: Main.lean:67-141 installLoop
    /// Before record `pos` of `total` is installed.
    fn install_before(&mut self, _ar: &EStore, _pos: u64, _total: usize, _d: &IDeclaration) {}

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// Phase A failed at fold position `pos`.
    fn install_failed(&mut self, _pos: u64, _total: usize) {}

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// The phase boundary: every record installed, `pend` checks pending, and
    /// the store as phase A left it — the node counts are the one number P6
    /// asked this line for, because they are what the install ADDED to the
    /// persistent tier on top of the parse's.  Since task #97-P6-2 phase A
    /// runs in the SCRATCH tier and promotes what the environment keeps, so
    /// the figure to compare with the Lean twin's (`Init`: **6 508 719**, the
    /// parse's 6 137 973 plus 370 746) is the PERSISTENT one, printed beside
    /// the total; phase B promotes nothing, so it is also the count at the
    /// end of the run.
    fn install_done(&mut self, _ar: &EStore, _total: usize, _pend: usize) {}

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// The worker count phase B is about to run on, so that the summary
    /// reports the lane the run actually took.
    fn phase_b_workers(&mut self, _workers: usize) {}

    /// con-leche: Main.lean:143-158 checkHeartbeat
    /// After the `done`-th of `m` recorded checks completed.
    fn check_after(&mut self, _ar: &EStore, _done: usize, _m: usize, _pc: &PendingCheck) {}

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// Phase B failed at fold position `pos`.
    fn check_failed(&mut self, _pos: u64) {}

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// Every recorded check passed.
    fn check_done(&mut self, _m: usize) {}
}

/// con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls
/// **The driver**: `checker::install_then_check`'s body with the phase
/// boundary visible — phase A installs every record with
/// `checker::annot_decl_step`, phase B checks every recorded declaration with
/// `checker::check_pending` from the installed index.  It is step for step
/// the fold (the twin's `installThenCheck`), which is why an observer printing
/// between the steps changes no verdict and why ONE loop serves the plain run
/// and the `--progress` heartbeat alike.  A run with no observer calls
/// `install_then_check` itself and never comes through here.
///
/// **The two-phase shape is the pool's seam** (DESIGN.md §8.3, the module
/// note's item 4): after the boundary the persistent tier is immutable, the
/// installed index is read-only, and each pending record is checked inside its
/// own scratch tier from its own caches — so `n` workers claiming records off
/// a counter is a change to this `while` and to nothing else.
pub fn check_decls_driver<O: PhaseObserver>(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
    jobs: u64,
    obs: &mut O,
) -> Result<IFEnv, (CheckError, u64)> {
    let total = ds.len();
    let mut p: (u64, IFEnv, Vec<PendingCheck>) = (0, ienv::mk_ifenv(ienv::i_env_empty()), Vec::new());
    let mut i = 0usize;
    while i < total {
        obs.install_before(&st.store, p.0, total, &ds[i]);
        match checker::annot_decl_step(st, mode, pins, p, &ds[i]) {
            Err(e) => {
                obs.install_failed(e.1, total);
                return Err(e);
            }
            Ok(q) => p = q,
        }
        i += 1;
    }
    let pend: Vec<PendingCheck> = p.2;
    let m = pend.len();
    let mut fe: IFEnv = p.1;
    obs.install_done(&st.store, total, m);
    let workers = workers_for(jobs, m);
    obs.phase_b_workers(workers);
    // Phase B, `checker::check_pending_list`'s walk with the observer between
    // the records: every record checked at its own prefix view, inside its own
    // scratch tier (`check_pending` is the bracket, task #97-P4d), with the
    // installed index threaded through.
    let mut j = 0usize;
    while j < m {
        match checker::check_pending(st, mode, fe, &pend[j]) {
            Err(e) => {
                obs.check_failed(pend[j].pos);
                return Err((e, pend[j].pos));
            }
            Ok(fe2) => fe = fe2,
        }
        j += 1;
        obs.check_after(&st.store, j, m, &pend[j - 1]);
    }
    obs.check_done(m);
    Ok(fe)
}

// ---------------------------------------------------------------------------
// The progress heartbeat (`--progress[=<stride>]`)
// ---------------------------------------------------------------------------

/// con-leche: Main.lean:318-421 checkDeclsIO
/// con-leche: Main.lean:143-158 checkHeartbeat
/// **The heartbeat**, `con_ron::driver::Heartbeat`'s line shapes with
/// `con-ron-arena: ` for the prefix:
///
/// ```text
/// con-ron-arena: parse done: <N> fold records — … t=<s>s (parse <s>s)
/// con-ron-arena: install <i>/<N> <decl> t=<s>s
/// con-ron-arena: install done: <N>/<N> declarations installed, <M> checks pending t=<s>s (install <s>s)
/// con-ron-arena: check <done>/<M> <kind> <name> t=<s>s
/// con-ron-arena: check done: <M>/<M> t=<s>s (check <s>s)
/// con-ron-arena: done: parse <p>s, install <i>s, check <c>s, <n> worker t=<s>s
/// ```
///
/// An install line is printed BEFORE the record it names, so a run that dies
/// in phase A names on its last line the declaration it died in; a check line
/// is printed AFTER the check, so "a check that is running is not on any line,
/// the gap between two lines is where it sits".
pub struct Heartbeat {
    /// The stride; `0` is no flag and no heartbeat.
    pub stride: u64,
    /// The start of the run, which every `t=` is measured from.
    pub t0: Instant,
    /// When the parse finished, in ms since `t0` — `Main.lean`'s `tParse`.
    pub t_parse: u128,
    /// When phase A finished, in ms since `t0` — `Main.lean`'s `tCheck`.
    pub t_install: u128,
    /// The worker count phase B ran on, for the summary.
    pub workers: usize,
}

/// con-leche: Main.lean:318-421 checkDeclsIO
/// The heartbeat's own lines: the parse's, and the closing summary the failure
/// and success arms share.
impl Heartbeat {
    /// con-leche: Main.lean:461-711 checkMain
    /// A heartbeat at `stride` (0 for none), starting now.
    pub fn new(stride: u64, t0: Instant) -> Heartbeat {
        Heartbeat {
            stride,
            t0,
            t_parse: 0,
            t_install: 0,
            workers: 1,
        }
    }

    /// con-leche: none — `IO.monoMsNow`, in milliseconds since `t0`.
    fn now(&self) -> u128 {
        self.t0.elapsed().as_millis()
    }

    /// con-leche: Main.lean:461-711 checkMain
    /// `con-ron-arena: parse done: …`, the heartbeat's first line.  Records
    /// `t_parse`, so the summary can price the parse whatever happens next.
    pub fn parse_done(
        &mut self,
        fold_records: usize,
        file_records: usize,
        gen_records: u64,
        synthesised: u64,
        nodes: (usize, usize, usize),
    ) {
        self.t_parse = self.now();
        if self.stride == 0 {
            return;
        }
        eprintln!(
            "con-ron-arena: parse done: {} fold records — the file's {} ({} of them \
             generated in-process), {} built-in prelude records synthesised; store \
             {} expression, {} level, {} name nodes t={}s (parse {}s)",
            fold_records,
            file_records,
            gen_records,
            synthesised,
            nodes.0,
            nodes.1,
            nodes.2,
            ms_secs(self.t_parse),
            ms_secs(self.t_parse)
        );
    }

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// The `done:` summary — the three phase durations and the worker count.
    fn summary(&self, check_ms: Option<u128>) {
        if self.stride == 0 {
            return;
        }
        let now = self.now();
        match check_ms {
            None => eprintln!(
                "con-ron-arena: done: parse {}s, install {}s, check not reached t={}s",
                ms_secs(self.t_parse),
                ms_secs(now - self.t_parse),
                ms_secs(now)
            ),
            Some(c) => eprintln!(
                "con-ron-arena: done: parse {}s, install {}s, check {}s, {} worker{} t={}s",
                ms_secs(self.t_parse),
                ms_secs(self.t_install - self.t_parse),
                ms_secs(c),
                self.workers,
                if self.workers == 1 { "" } else { "s" },
                ms_secs(now)
            ),
        }
    }
}

/// con-leche: Main.lean:143-158 checkHeartbeat
/// con-leche: Main.lean:318-421 checkDeclsIO
/// The heartbeat as an observer of the two phases.
impl PhaseObserver for Heartbeat {
    /// con-leche: Main.lean:67-141 installLoop
    /// `con-ron-arena: install <i>/<N> <decl> t=<s>s`, before the install.
    fn install_before(&mut self, ar: &EStore, pos: u64, total: usize, d: &IDeclaration) {
        if self.stride > 0 && pos % self.stride == 0 {
            eprintln!(
                "con-ron-arena: install {}/{} {} t={}s",
                pos,
                total,
                decl_label(ar, d),
                ms_secs(self.now())
            );
        }
    }

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// `con-ron-arena: install failed at <i>/<N> …`, then the summary.
    fn install_failed(&mut self, pos: u64, total: usize) {
        if self.stride > 0 {
            let now = self.now();
            eprintln!(
                "con-ron-arena: install failed at {}/{} t={}s (install {}s)",
                pos,
                total,
                ms_secs(now),
                ms_secs(now - self.t_parse)
            );
        }
        self.summary(None);
    }

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// `con-ron-arena: install done: <N>/<N> …, <M> checks pending …`.
    fn install_done(&mut self, ar: &EStore, total: usize, pend: usize) {
        self.t_install = self.now();
        if self.stride > 0 {
            eprintln!(
                "con-ron-arena: install done: {}/{} declarations installed, {} checks \
                 pending; store {} expression ({} persistent), {} level, {} name nodes \
                 t={}s (install {}s)",
                total,
                total,
                pend,
                ar.node_count(),
                ar.pers_count(),
                ar.ls().node_count(),
                ar.ns().node_count(),
                ms_secs(self.t_install),
                ms_secs(self.t_install - self.t_parse)
            );
        }
    }

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// The cited `workers`, for the summary's last field.
    fn phase_b_workers(&mut self, workers: usize) {
        self.workers = workers;
    }

    /// con-leche: Main.lean:143-158 checkHeartbeat
    /// `con-ron-arena: check <done>/<M> <kind> <name> t=<s>s`, after the check.
    fn check_after(&mut self, ar: &EStore, done: usize, m: usize, pc: &PendingCheck) {
        if self.stride > 0 && (done as u64) % self.stride == 0 {
            eprintln!(
                "con-ron-arena: check {}/{} {} {} t={}s",
                done,
                m,
                value_kind_word(&pc.vg.kind),
                name_of(ar, &pc.vg.cv_a.name),
                ms_secs(self.now())
            );
        }
    }

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// `con-ron-arena: check failed at fold position <i> …`, then the summary.
    fn check_failed(&mut self, pos: u64) {
        let now = self.now();
        if self.stride > 0 {
            eprintln!(
                "con-ron-arena: check failed at fold position {} t={}s (check {}s)",
                pos,
                ms_secs(now),
                ms_secs(now - self.t_install)
            );
        }
        self.summary(Some(now - self.t_install));
    }

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// `con-ron-arena: check done: <M>/<M> …`, then the summary.
    fn check_done(&mut self, m: usize) {
        let now = self.now();
        if self.stride > 0 {
            eprintln!(
                "con-ron-arena: check done: {}/{} t={}s (check {}s)",
                m,
                m,
                ms_secs(now),
                ms_secs(now - self.t_install)
            );
        }
        self.summary(Some(now - self.t_install));
    }
}

// ---------------------------------------------------------------------------
// The verdict lines
// ---------------------------------------------------------------------------

/// con-leche: Main.lean:461-711 checkMain
/// **The accept line**, `con_ron::driver::verdict_accept`'s with this
/// binary's name: `records` is the FILE's declaration-record count — what the
/// parse produced, less the records the in-process modeller generated — and
/// nothing the preparation does moves it.  It is not the environment's
/// constant count, which is a property of the representation and not of the
/// input.  Printed on STDOUT, where a caller greps for a verdict.
pub fn verdict_accept(records: u64, mode_tag: &str) -> u8 {
    println!(
        "con-ron-arena: accepted {} declarations ({})",
        records, mode_tag
    );
    0
}

/// con-leche: Main.lean:461-711 checkMain
/// The failure line: the error, the declaration it names and its FOLD
/// position, the mode, the elapsed time.  There is no second pass — the fold's
/// error carries the position, so the label is read off the record array the
/// driver already holds.
///
/// `i` is the fold position and is NOT the file's record index (the prepared
/// list starts with the prelude's records and carries the ones the in-process
/// modeller generated); the declaration NAME on the line is the portable
/// handle.  `owner` is the inductive block a generated `_model` record belongs
/// to, where the caller can say.
pub fn verdict_failure(
    ar: &EStore,
    ds: &Vec<IDeclaration>,
    e: &CheckError,
    i: u64,
    owner: Option<String>,
    mode_tag: &str,
    t0: Instant,
) -> u8 {
    let code = con_ron::driver::exit_code(e);
    let loc = match ds.get(i as usize) {
        None => format!(" [at fold position {}]", i),
        Some(d) => match owner {
            Some(t) => format!(
                " [at {}, a generated model record of inductive {}, fold position {}]",
                decl_label(ar, d),
                t,
                i
            ),
            None => format!(" [at {}, fold position {}]", decl_label(ar, d), i),
        },
    };
    eprintln!(
        "con-ron-arena: {}: {}{} ({}) t={}s",
        con_ron::driver::verdict_word(code),
        message(e),
        loc,
        mode_tag,
        ms_secs(t0.elapsed().as_millis())
    );
    code
}

// ---------------------------------------------------------------------------
// The streaming reader
//
// `ConLeche/Frontend/ExportC.lean`'s `parseExportHandleD` and
// `parseExportStreamD` over the ARENA's `chunk_step`/`chunk_finish` — the loop
// with the reads interleaved, whose pure counterpart `parse_chunks` is
// `arena_core::frontend::export_c`'s.  It is here and not there for
// `con_ron::driver`'s reason: `IO.FS.Handle.read` has no model, and a theorem
// about the file is a theorem about its bytes.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:903-931 parseExportHandleD
/// Streaming direct parse off an open reader, into the persistent tier of
/// `ar`.  The unconsumed tail of a chunk — at most one incomplete line — is
/// carried into the next one.  Each step is the core's `chunk_step`, the end
/// its `chunk_finish`; the loop is `parse_chunks`' with the reads interleaved,
/// stopping at the first empty read.  The chunk count comes back for the
/// heartbeat, as the Lean twin's `readFold` returns it.
pub fn parse_export_handle_d<R: Read, M: Modeller>(
    m: &M,
    ar: &mut AState,
    h: &mut R,
    in_model: bool,
    census: bool,
    chunk: usize,
) -> std::io::Result<(Result<ParseResultD, (CheckError, u64)>, u64)> {
    let mut st = match export_c::state_d_init(&mut ar.store, in_model, census) {
        Ok(s) => s,
        Err(e) => return Ok((Err((e, 0)), 0)),
    };
    let mut carry: Vec<u8> = Vec::new();
    let mut line_no: u64 = 0;
    let mut total: u64 = 0;
    let mut chunks: u64 = 0;
    let mut buf0: Vec<u8> = vec![0u8; chunk];
    loop {
        let n = con_ron::driver::read_up_to(h, &mut buf0)?;
        if n == 0 {
            return Ok((export_c::chunk_finish(m, ar, st, &carry[..], line_no), chunks));
        }
        chunks += 1;
        match export_c::chunk_step(m, ar, &mut st, carry, line_no, total, &buf0[..n]) {
            Err(e) => return Ok((Err(e), chunks)),
            Ok((c, l, t)) => {
                carry = c;
                line_no = l;
                total = t;
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:933-938 parseExportStreamD
/// Streaming direct parse of a file.
pub fn parse_export_stream_d<M: Modeller>(
    m: &M,
    ar: &mut AState,
    path: &str,
    in_model: bool,
    census: bool,
    chunk: usize,
) -> std::io::Result<(Result<ParseResultD, (CheckError, u64)>, u64)> {
    let mut f = std::fs::File::open(path)?;
    parse_export_handle_d(m, ar, &mut f, in_model, census, chunk)
}

#[cfg(test)]
mod tests {
    use super::*;
    use arena_core::frontend::types::DeclineModeller;

    /// **The reader loop is `parse_chunks` with the reads interleaved.**  The
    /// core proves nothing about the reader — it cannot, `IO.FS.Handle.read`
    /// has no model — so the agreement is a test: at every chunk size,
    /// including sizes that cut inside a line and one byte at a time, the
    /// streaming parse and the pure fold over the same chunks produce the same
    /// records.  `con_ron::driver`'s own test, over the arena's parser.
    #[test]
    fn the_reader_is_parse_chunks_with_the_reads() {
        let s = concat!(
            "{\"meta\":{\"exporter\":{\"name\":\"lean4export\"}}}\n",
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n"
        );
        let b = s.as_bytes();
        for chunk in [1usize, 2, 7, 8, 13, 64, 4096] {
            let mut ar = AState::init(EStore::empty());
            let mut r = std::io::Cursor::new(b.to_vec());
            let (streamed, _) =
                parse_export_handle_d(&DeclineModeller {}, &mut ar, &mut r, true, false, chunk)
                    .expect("no io error");
            let streamed = streamed
                .unwrap_or_else(|(e, l)| panic!("chunk {} line {}: {}", chunk, l, message(&e)));
            let mut ar2 = AState::init(EStore::empty());
            let cs: Vec<Vec<u8>> = b.chunks(chunk).map(|c| c.to_vec()).collect();
            let pure = export_c::parse_chunks(&DeclineModeller {}, &mut ar2, &cs, true, false)
                .unwrap_or_else(|(e, l)| {
                    panic!("pure chunk {} line {}: {}", chunk, l, message(&e))
                });
            assert_eq!(streamed.decls.len(), pure.decls.len(), "chunk {}", chunk);
            assert_eq!(streamed.decls.len(), 1, "chunk {}", chunk);
            assert_eq!(ar.store.node_count(), ar2.store.node_count(), "chunk {}", chunk);
        }
    }

    /// The three words of the arena's own `ValueKind`, and the flag values,
    /// which are `con_ron::driver`'s and are called across the crate line so
    /// that the two binaries cannot drift.
    #[test]
    fn rendering_and_flag_values() {
        assert_eq!(value_kind_word(&ValueKind::Defn), "definition");
        assert_eq!(value_kind_word(&ValueKind::Thm), "theorem");
        assert_eq!(value_kind_word(&ValueKind::Opaque), "opaque");
        assert_eq!(con_ron::driver::progress_stride("1"), Ok(1));
        assert!(con_ron::driver::progress_stride("0").is_err());
        assert_eq!(con_ron::driver::jobs_count("8"), Ok(8));
        assert!(con_ron::driver::jobs_count("0").is_err());
        // phase B is single-lane here, whatever `--jobs` asked for
        assert_eq!(workers_for(8, 100), 1);
        assert_eq!(workers_for(1, 0), 1);
    }
}
