//! `checker_io` — con-leche's `CheckerIO` class as two traits (DESIGN.md §3.9,
//! task #171).
//!
//! con-leche writes its driver once over the class `CheckerIO m`
//! (`ConLeche/Frontend/CheckerIO.lean`) and runs it at `IO` (the binary) and at
//! `ModelIO` (the model the main theorems are stated in).  The port writes its
//! driver (`crate::driver`) once over these traits: `crates/con-ron`'s `StdIo`
//! is the binary's instance, and the main theorems (`proof/ConRon/MainTheorem.lean`)
//! hold at every instance whose file operations answer as one snapshot of the
//! files (`AnswersAs`) and whose worker map keeps its contract (`PoolSound`).
//!
//! * `CheckerFs` — the file operations, `&self`: in the Aeneas model a pure
//!   function of the instance, and the premise on them holds at every state, so
//!   no escape can change what they see.  Slice 1 needs the positional read
//!   alone; its name and signature are `files::OleanFs`'s, which slice 2 folds
//!   in.
//! * `Step` — a job of the worker map: a worker's first state and one step,
//!   which may read files through the instance.
//! * `CheckerIo` — the worker map and the escapes.  An escape that ANSWERS a
//!   value the run goes on with (the help's exit code, the hardware thread
//!   count, a legacy mode's exit code, a pin file) is `&mut self`, so that the
//!   model claims nothing about its answer (`liftIO`'s "any outcome"); a
//!   notification (answer `()`) is `&self`.  Two traits and not one: Aeneas
//!   rejects mutually recursive trait declarations (`Step` bounded by
//!   `CheckerIo`, whose method is bounded by `Step`).
//!
//! `FileChunks` is the stream's reader over the file operations: the core's
//! `export_c::ChunkSource` over `(&F, path, offset)`, so the stream parse
//! (`export_c::parse_source`) and its Theorem 2 stay as they are.

use crate::arena::env::IDeclaration;
use crate::arena::handle::NIdx;
use crate::arena::monad::AState;
use crate::arena::store::EStore;
use crate::arena::store::PersTier;
use crate::arena::stream_index::IStreamIndex;
use crate::driver::cli::Bad;
use crate::driver::check_main::Note;
use crate::frontend::export_c::ChunkSource;
use crate::frontend::export_c::CHUNK_SIZE;
use crate::frontend::pace::Pace;
use crate::kernel::core_types::CheckError;
use crate::kernel::nat_op_pins::NatOpPinSet;

/// con-leche: ConLeche/Frontend/CheckerIO.lean:141-200 CheckerIO
/// **The checker's file operations**: the class's operations a run reads files
/// with.  A failure is the operation's message, rendered by the instance.
pub trait CheckerFs {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:141-200 CheckerIO
    /// A positional read: the bytes of the file at `p` from `off` up to
    /// `off + len` or the end of the file, whichever comes first.  Deviation:
    /// the class opens a handle (`openRead`) and reads it forward (`read`); the
    /// reads a run makes here are at `0, n₁, n₁ + n₂, …`, each where the last
    /// ended, so an instance may serve them from one forward handle (a pipe)
    /// and fail any other offset.
    fn read_range(&self, p: &Vec<u32>, off: u64, len: u64) -> Result<Vec<u8>, Vec<u32>>;
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:141-200 CheckerIO
/// **A job of the worker map** (`parMapWorkers`'s `init` and `f`): a worker's
/// first state, and one step at a position, from the worker's state, which it
/// may read files through.  `view` is for the instance's per-job heartbeat
/// line and is in no contract.
pub trait Step<F: CheckerFs, S> {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:141-200 CheckerIO
    /// A worker's state before its first job.
    fn init(&self) -> S;
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:141-200 CheckerIO
    /// The job at position `k`, on the worker's state.
    fn step(&self, fs: &F, s: &mut S, k: usize) -> Result<(), (CheckError, u64)>;
    /// con-leche: ConLeche/Driver/CheckPool.lean:101-111 jobLabel
    /// What the heartbeat reads a job's label off: the tier, the worker's
    /// store and the records.
    fn view<'a>(&'a self, s: &'a S) -> (&'a PersTier, &'a EStore, &'a Vec<IDeclaration>);
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:141-200 CheckerIO
/// **The checker's IO**: the file operations, the worker map and the escapes.
/// What a run prints goes through the notifications as structured events, and
/// the instance renders them.
pub trait CheckerIo: CheckerFs + Sized + Sync {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:141-200 CheckerIO
    /// **The worker map** (`parMapWorkers`): `st`'s jobs at `0..n` on `workers`
    /// workers, each from `st.init()` and stepping through the jobs it claims in
    /// increasing order; the first failure in position order, or `Ok`.  Its
    /// contract is `PoolSound` (`Refine2/Checker/Jobs.lean`'s `ParallelAll`, for
    /// every `Step`); the per-job heartbeat is the instance's, around each step.
    fn par_map_workers<S: Send, St: Step<Self, S> + Sync>(
        &mut self,
        st: &St,
        n: usize,
        workers: usize,
    ) -> Result<(), (CheckError, u64)>;
    /// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
    /// `--help`: the help text on stdout; the exit code (3 when the write fails).
    fn print_help(&mut self) -> u8;
    /// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
    /// A request the verified driver does not run yet: the unverified driver's
    /// run of the whole argument list, and its exit code.
    fn run_legacy(&mut self, argv: &Vec<Vec<u32>>) -> u8;
    /// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
    /// The `--jobs` default: one worker per hardware thread, capped
    /// (`System.Platform.Internal.getHardwareConcurrency`).
    fn hardware_jobs(&mut self) -> u64;
    /// con-leche: none — `--pins FILE`, the port's testing override, read by the
    /// unverified `con-ron-pins/2` reader; the message names the file.
    fn read_pins_file(&mut self, p: &Vec<u32>) -> Result<Vec<NatOpPinSet>, Vec<u32>>;
    /// con-leche: none — con-leche task #336's exit without freeing the heap: the
    /// instance keeps what the run built until the process exits.
    fn keep_heap(&mut self, st: AState, ds: Vec<IDeclaration>, ix: Option<IStreamIndex>);
    /// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
    /// A usage error's two lines.
    fn usage(&self, b: &Bad);
    /// con-leche: ConLeche/Driver/CheckMain.lean:70-75 diagLine
    /// A diagnostic or a verdict line that reads no store.
    fn note(&self, n: &Note);
    /// con-leche: ConLeche/Driver/Run.lean:33-36 readStarts
    /// The heartbeat at `pace` starts, with what the run reads.
    fn read_starts(&self, pace: &Pace, path: &Vec<u32>);
    /// con-leche: ConLeche/Driver/CheckMain.lean:268-458 checkMainG
    /// The ground hoist's receipt: the records moved ahead of the pinned `Nat`
    /// operations they ground.
    fn hoisted(&self, pers: &PersTier, ar: &EStore, names: &Vec<NIdx>);
    /// con-leche: ConLeche/Driver/CheckMain.lean:268-458 checkMainG
    /// The index build is about to start (`tIndex`).
    fn index_starts(&self);
    /// con-leche: ConLeche/Driver/CheckMain.lean:268-458 checkMainG
    /// The parse and the index are done: `fold` records, `file` of them the
    /// file's, `synthesised` the prelude's.
    fn parse_done(&self, pers: &PersTier, ar: &EStore, fold: usize, file: usize, synthesised: u64);
    /// con-leche: ConLeche/Driver/Run.lean:49-55 checkStarts
    /// The check phase starts: `m` jobs on `workers` workers.
    fn check_starts(&self, m: usize, workers: usize);
    /// con-leche: ConLeche/Driver/Run.lean:57-83 checkDone
    /// The check phase ended, at the first failure's position or with every
    /// job passed.
    fn check_done(&self, m: usize, failure: &Option<u64>);
    /// con-leche: ConLeche/Driver/CheckMain.lean:180-266 verdictG
    /// The failure line: the error, the record at its fold position, the mode.
    fn verdict_failure(&self, pers: &PersTier, ar: &EStore, ds: &Vec<IDeclaration>, e: &CheckError, i: u64, verified: bool);
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:210-218 foldChunks
/// **The stream's reads over the file operations**: positional reads of the
/// file at `path`, `CHUNK_SIZE` bytes each, each at the offset the last one
/// ended, to the first empty one.  A failed read ends the input the same way
/// and is KEPT here: the driver reports it in place of whatever the parse of
/// the truncated input said, so a read error is exit 3, never a verdict.
pub struct FileChunks<'a, F: CheckerFs> {
    /// the file operations
    pub fs: &'a F,
    /// the file
    pub path: &'a Vec<u32>,
    /// where the next read starts: the bytes handed out so far
    pub off: u64,
    /// the reads that answered so far: a `usize`, so that the chunks they
    /// handed out are a list a `usize` indexes (`Vec<Vec<u8>>`, the form the
    /// capstone's `parse_chunks` is stated over) on every platform
    pub reads: usize,
    /// the first read failure, if any
    pub err: Option<Vec<u32>>,
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:210-218 foldChunks
impl<'a, F: CheckerFs> ChunkSource for FileChunks<'a, F> {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:210-218 foldChunks
    /// One read of up to `CHUNK_SIZE` bytes at the offset; empty at the end or
    /// on a failure, and empty for good after a failure.
    fn next_chunk(&mut self) -> Vec<u8> {
        match &self.err {
            Some(_) => return Vec::new(),
            None => (),
        }
        match self.fs.read_range(self.path, self.off, CHUNK_SIZE as u64) {
            Ok(b) => {
                self.off = self.off + (b.len() as u64);
                self.reads = self.reads + 1;
                b
            }
            Err(e) => {
                self.err = Some(e);
                Vec::new()
            }
        }
    }
}
