//! `ConLeche/Kernel/Inductives/*` — the **two install routes for inductive
//! blocks**: the *direct* (fixpoint) route, which checks a block against the
//! reference kernels' own inductive-declaration checks and **generates** its
//! recursor, and the *modeled* route, which checks every member against the
//! in-process modeller's `_model` artifacts.
//!
//! | Rust | Lean |
//! |---|---|
//! | `struct_parts` | `Inductives/StructParts.lean` |
//! | `sum_parts` | `Inductives/SumParts.lean` |
//! | `native_parts` | `Inductives/NativeParts.lean` |
//! | `struct_install` | `Inductives/StructInstall.lean` + `Inductives/StructInstallF.lean` |
//! | `sum_install` | `Inductives/SumInstall.lean` + `Inductives/SumInstallF.lean` |
//! | `native_install` | `Inductives/NativeInstall.lean` + `Inductives/NativeInstallF.lean` |
//! | `modeled` | `Inductives/Modeled.lean` + the `*F` twins of `Kernel/DeclCheck.lean` |
//! | `inductives_c` | the two routes' drivers in `Cached/CheckerC.lean` |
//!
//! ## Three deviations that apply to the whole directory
//!
//! 1. **One spelling of the environment: `fe: &FEnv`** (task #18's deviation
//!    3).  con-leche writes each install stage twice — over `Env`
//!    (`*Install.lean`, the pure fueled checker the verification tier reasons
//!    about) and over the index (`*InstallF.lean`, what the executable runs);
//!    the two differ *only* in `env.find?` versus `fe.find?` and in
//!    `⟨ci :: env.consts⟩` versus `fe.push ci`.  The port has one function
//!    per pair, carrying **both** citations, so `Inductives/StructInstallF`,
//!    `Inductives/SumInstallF` and `Inductives/NativeInstallF` have no Rust
//!    module of their own and the merged functions live in the module of the
//!    non-`F` file.  For the same reason `Modeled.lean`'s stages carry their
//!    `Kernel/DeclCheck.lean` `*F` twin as a second citation.
//!
//! 2. **`CheckerOps` is dissolved into direct wrapper calls** (§3.1's knot
//!    ruling).  The whole declaration checker is written once against a record
//!    of five closures plus an `orElse` combinator; §3.4 forbids closures and
//!    the knot rule forbids a trait in the recursion, so an `ops.whnf env d e`
//!    becomes `core_c::whnf(mode, check_fuel(), st, fe, d, &e)` — the
//!    *wrapper*, by name, at `core_k::check_fuel()`, which is what
//!    `sharedOpsC` passes (`coreKnotI mode fe checkFuel`).  `ops.ensureSort`
//!    is `core_k::ensure_sort`, `ops.annotate`/`inferType`/`isDefEq` the
//!    `core_c` wrappers of those names.  `orElse` is not reached from these
//!    routes (its one caller is the Nat-op pin gate).
//!
//! 3. **`StructWalkers` is dissolved too.**  `StructInstallF.lean:63-72`
//!    passes the two whole-tree traversals of the direct install as a record
//!    of two closures, so that the cached driver can supply its memoised
//!    twins (`Cached/CheckerC.lean:56` `structWalkersC`).  Both walkers the
//!    port has *are* memoised — `core_k::consts_resolve` is the one spelling
//!    of `Expr.constsResolve`/`constsResolveF`/`constsResolveFC` and
//!    `struct_parts::struct_proj_bodies` of
//!    `structProjBodies`/`structProjBodiesC` — and con-leche's own
//!    `structWalkersC_eq_plain` is the equation that says the record is the
//!    specification.  So the record is gone and the two walkers are called by
//!    name; the memos are per-call and local, so no memo *policy*
//!    (DESIGN.md §3.1) is touched.
//!
//! ## What these routes take from the declaration checker
//!
//! The install routes sit *on top of* `Kernel/CheckerBase.lean` and
//! `Kernel/DeclCheck.lean`, which are `kernel/checker_base.rs` and
//! `kernel/decl_check.rs`.  Task #25 landed the pieces it needed in a
//! temporary `checker_local` module; **task #27 unified it away** — there is
//! no second spelling of any of them any more:
//!
//! | what a route needs | where it is |
//! |---|---|
//! | `checkConstantVal`, `checkTypedList`/`checkAnnotList`/`checkDefEqList`, `openPisAtFvars`(`F`), `domsMatchAux` and its `DomView`, `isEqHead`/`eqHeadLevel`, `Env.findCV?`, `checkProjShape`/`checkProjRule`, `unwrapOr`, `fvs.map Expr.fvarTypeD` | `kernel::checker_base` |
//! | `Expr.allLevelParamsDefined` (spec, memoised `*Go`, executed `*Fast`) | `kernel::expr_ops` (task #13's leftover, closed by task #24) |
//! | the `deriving DecidableEq`s of the stored-constant records, and `blockRecSuffixDec` | `kernel::env` |
//! | `eqA` and the guard `env.find? eqName = some eqA` | `kernel::basis_pins`, over task #22's generated `kernel::basis_tables` |
//!
//! The one non-identity binder view the directory needs — `checkProjIotaF`'s
//! forward projection rename — is `modeled::DomProjFwd`, an implementation of
//! `checker_base::DomView`; the other three sites pass
//! `checker_base::DomIdent`.

pub mod inductives_c;
pub mod modeled;
pub mod native_install;
pub mod native_parts;
pub mod struct_install;
pub mod struct_parts;
pub mod sum_install;
pub mod sum_parts;
