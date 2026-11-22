//! The `.olean` reader, inside the verified core (task #142): con-leche's
//! `ConLeche/Frontend/Olean/*`, one Rust module per Lean file, every public entry
//! point of `ConLeche/Frontend/Olean.lean`'s tables, used or not.
//!
//! | Rust | Lean twin | con-leche |
//! |---|---|---|
//! | `region` | imported, not twinned | `Olean/Region.lean` (bytes only) |
//! | `spec` | `Arena/Frontend/Olean/Spec.lean` | `Olean/Spec.lean`, what executes of it |
//! | `header` | `Arena/Frontend/Olean/Header.lean` | `Olean/Header.lean` |
//! | `fast` | `Arena/Frontend/Olean/Fast.lean` | `Olean/Fast.lean` |
//! | `sparse` | `Arena/Frontend/Olean/Sparse.lean` | `Olean/Sparse.lean` |
//! | `reads` | `Arena/Frontend/Olean/Reads.lean` | `Olean/Reads.lean` |
//! | `view` | `Arena/Frontend/Olean/View.lean` | `Olean/View.lean` |
//! | `module` | `Arena/Frontend/Olean/Module.lean` | `Olean/Module.lean` |
//! | `files` | `Arena/Frontend/Olean/Files.lean` | `Olean/Files.lean` |
//! | `lazy` | none yet | `Olean/Lazy.lean` (task #481) |
//! | `progress` | none yet | `Olean/Progress.lean`, the pure part (task #484) |
//! | `closure` | `Arena/Frontend/Olean/Closure.lean` | `Olean/Closure.lean` |
//! | `merge` | `Arena/Frontend/Olean/Merge.lean` | `Olean/Merge.lean` |
//! | `emit` | `Arena/Frontend/Olean/Emit.lean` | `Olean/Emit.lean` |
//! | `records` | `Arena/Frontend/Olean/Records.lean` | `Olean/Records.lean` |
//! | `levels` | `Arena/Frontend/Olean/Levels.lean` | `Olean/Levels.lean` (task #166) |
//! | `index` | `Arena/Frontend/Olean/Index.lean` | `Olean/Index.lean` (task #166) |
//! | `group` | `Arena/Frontend/Olean/Group.lean` | `Olean/Group.lean` (task #166) |
//! | `present` | `Arena/Frontend/Olean/Present.lean` | `Olean/Present.lean` (task #166) |
//!
//! **Terms are read straight into the store**, as the stream parser's are, so the
//! reader's outcome is `IDeclaration`s over handles and everything after the parse
//! is the stream path's.  DESIGN.md's `### Task #142` has the design; the seam is
//! `checker_io::CheckerFs`.

pub mod region;
pub mod spec;
pub mod header;
pub mod fast;
pub mod sparse;
pub mod reads;
pub mod view;
pub mod module;
pub mod files;
pub mod lazy;
pub mod progress;
pub mod closure;
pub mod merge;
pub mod emit;
pub mod records;
pub mod levels;
pub mod index;
pub mod group;
pub mod present;
