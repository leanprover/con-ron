//! `ConLeche/Frontend/InModel.lean` — the entry point of the in-process
//! construction of `_model` families for the inductive blocks the direct
//! routes do not install and the modeled install expects a model for:
//! **mutual** and **nested** blocks.
//!
//! The frontend calls `generate` at the block's record, before the block is
//! pushed, when the stream carries no model for it; the records it returns are
//! pushed ahead of the block and checked by the fold like any stream
//! declaration (the "certification tax"), and the block itself installs
//! through the modeled route.
//!
//! Soundness needs nothing from this module: a wrong record is rejected or
//! declined by the fold, never accepted.  Its correctness decides only
//! *coverage* — which blocks accept — and every decline names its class, so
//! the residual is exact and positive.  Nothing here is verified, and nothing
//! here is in §3.4's Aeneas subset.
//!
//! | Rust | con-leche |
//! |---|---|
//! | `in_model` (this file) | `ConLeche/Frontend/InModel.lean` |
//! | `in_model::kit` | `ConLeche/Frontend/InModel/Kit.lean` |
//! | `in_model::mutual` | `ConLeche/Frontend/InModel/Mutual.lean` |
//! | `in_model::nested` | `ConLeche/Frontend/InModel/Nested.lean` |
//!
//! **`ConLeche/Frontend/InModelDump.lean` is not ported.**  It is the
//! `CON_LECHE_INMODEL_DUMP=OUT` debug path: a copy of the raw input with the
//! generated records spliced in ahead of their block, written through
//! `Frontend/ExportWrite.lean`'s `ExportWriter`.  It is not on the checking
//! path (its own header says so), and the writer it is built on is the one
//! source file task #37 deliberately left out — an output format, not
//! something a checker reads.  So con-ron has no `--inmodel-dump`, and
//! `StateD.inModelGen`, the array that feeds it, stays unported too.
//!
//! `InModel.wants` is ported in `frontend::export_c` (`in_model_wants`),
//! where the call site is: its two fields are the scan record's own, so the
//! test needs neither `BlockRec` nor `blockRecOf`.

pub mod kit;
pub mod mutual;
pub mod nested;

use con_ron_core::frontend::in_model_rec;
use con_ron_core::frontend::in_model_rec::{ModelCtx, Modeller};
use con_ron_core::kernel::env::Declaration;
use con_ron_core::kernel::expr::Expr;
use con_ron_core::kernel::name::Name;

use crate::in_model::mutual::{BlockRec, Ctx};

/// con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
/// Generate the model records of a block, in stream order, or the reason the
/// block is declined.
pub fn generate(ctx: &Ctx, b: &BlockRec) -> Result<Vec<Declaration>, String> {
    if b.types.iter().any(|t| t.num_nested > 0) {
        nested::gen_nested(ctx, b)
    } else {
        mutual::gen_mutual(ctx, b)
    }
}

/// con-leche: none — the seam between the verified parse and this crate
/// (task #84)
/// The modeller, as the core's parse sees it.  `parse_chunks` and everything
/// above it are generic in a `Modeller`, which Charon renders as a typeclass
/// field — an opaque function — so the extracted parse is quantified over an
/// arbitrary modeller and its refinement carries one hypothesis about this
/// crate's output rather than a port of it.  This unit struct is the
/// implementation the binary passes.
pub struct InProcess;

/// con-leche: none — the seam's one method (task #84)
/// The core hands over `ModelCtx`, which borrows the parse state's three
/// tables; con-leche's `InModel.Ctx` is three *functions*, because the
/// generators build **overlays** over them (`tbl'` adds the block's own
/// generated types, `hOf` the heights of the definitions emitted so far).
/// So the borrows are wrapped back into closures here, at the boundary,
/// and nothing below this file changed.
impl Modeller for InProcess {
    /// con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
    /// `InModel.generate` at the seam: the borrows rewrapped as the three
    /// closures the generators overlay, and the decline's message as code
    /// points (the core's `String`, DESIGN.md §3.3).
    fn generate(&self, ctx: &ModelCtx, b: &BlockRec) -> Result<Vec<Declaration>, Vec<u32>> {
        let tbl = |n: &Name| -> Option<(Vec<Name>, Expr)> { in_model_rec::ctx_tbl(ctx, n) };
        let hs = |n: &Name| -> u64 { in_model_rec::ctx_height(ctx, n) };
        let bl = |n: &Name| -> Option<&BlockRec> { in_model_rec::ctx_block(ctx, n) };
        let c = Ctx {
            tbl: &tbl,
            heights: &hs,
            blocks: &bl,
        };
        match generate(&c, b) {
            Ok(ds) => Ok(ds),
            Err(why) => Err(why.chars().map(|ch| ch as u32).collect()),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::driver::message;
    use crate::in_model::InProcess;
    use crate::render::name_str;
    use con_ron_core::frontend::export_c::{parse_bytes, ParseResultD};
    use con_ron_core::kernel::env::declaration_names;

    /// con-leche's own lake package directory (task #91: a plain lake
    /// dependency, not vendored, so the path is resolved through
    /// `scripts/provenance.py dir` rather than a fixed repository-relative
    /// one).
    fn con_leche_dir() -> std::path::PathBuf {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let out = std::process::Command::new("python3")
            .arg("scripts/provenance.py")
            .arg("dir")
            .current_dir(&root)
            .output()
            .expect("running scripts/provenance.py dir");
        assert!(
            out.status.success(),
            "scripts/provenance.py dir failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        std::path::PathBuf::from(String::from_utf8(out.stdout).unwrap().trim().to_string())
    }

    /// The fixture's bytes, read at test time from con-leche's own tree (the
    /// crate already hard-requires it: `frontend::prelude` embeds a file from
    /// it at build time).
    fn fixture_bytes(name: &str) -> Vec<u8> {
        let p = con_leche_dir().join("tests/e2e").join(name);
        std::fs::read(&p).unwrap_or_else(|e| panic!("{}: {}", p.display(), e))
    }

    /// con-leche's own `tests/e2e` streams for the three rungs.  The parse
    /// takes no prelude since con-leche task #293: it decodes the file's
    /// records, and `frontend::prepare` is what puts the prelude in front.
    fn parse_fixture(name: &str) -> ParseResultD {
        parse_bytes(&InProcess, &fixture_bytes(name), true, false)
            .unwrap_or_else(|(e, l)| panic!("{}:{}: {}", name, l, message(&e)))
    }

    /// **The modeller runs, and every record it emits belongs to the block it
    /// models.**  `gen_owner` maps each generated record's names to the
    /// block's type former, so the assertion is that the families are named
    /// under `T._model` / `T._model._impl` and nothing else was booked.
    fn assert_models(name: &str, blocks: &[&str], min_records: u64) {
        let r = parse_fixture(name);
        let got: Vec<String> = r.in_modelled.iter().map(name_str).collect();
        for b in blocks {
            assert!(got.contains(&b.to_string()), "{}: {:?}", name, got);
        }
        assert_eq!(got.len(), blocks.len(), "{}: {:?}", name, got);
        assert!(
            r.gen_records >= min_records,
            "{}: {} generated records",
            name,
            r.gen_records
        );
        // Every booked name is under its block's `_model` prefix, and the
        // fold's list carries them: the generated records are declarations
        // like any other.  Since task #84 `gen_owner` is the core's
        // `ron::HashMap`, which has no iterator, so the walk is over the
        // records and the map is only probed.
        let mut seen = 0u64;
        for d in r.decls.iter() {
            let mut booked = false;
            for n in declaration_names(d) {
                if let Some(owner) = r.gen_owner.get(&n) {
                    let nm = name_str(&n);
                    let ow = name_str(owner);
                    assert!(
                        nm.starts_with(&format!("{}._model", ow))
                            || nm.starts_with(&format!("{}.", ow))
                            || nm.contains("._model"),
                        "{}: {} booked under {}",
                        name,
                        nm,
                        ow
                    );
                    booked = true;
                }
            }
            if booked {
                seen += 1;
            }
        }
        assert_eq!(seen, r.gen_records, "{}: generated records in the list", name);
    }

    /// The MUTUAL rung (B1/B2) on con-leche's own fixture: `Even`/`Odd`.
    #[test]
    fn the_mutual_rung_models_its_fixture() {
        assert_models(
            "inmodel_mutual.ndjson",
            &["InModelMutual.Even", "InModelMutual.Node", "InModelMutual.A"],
            // per block: tag + aux + member models + ctor models + rec models
            // + iotas
            24,
        );
    }

    /// The NESTED rung (B3) on con-leche's own fixture: `Tree` through `List`.
    #[test]
    fn the_nested_rung_models_its_fixture() {
        assert_models(
            "inmodel_nested.ndjson",
            &[
                "InModelNested.Tree",
                "InModelNested.TV",
                "InModelNested.Op",
                "InModelNested.W",
                "InModelNested.PT",
                "InModelNested.NTree",
                "InModelNested.A",
            ],
            60,
        );
    }

    /// The CONTAINER-GROUP rung (B4): a container that is itself mutual, so
    /// the group has more than one member.
    #[test]
    fn the_group_rung_models_its_fixture() {
        assert_models(
            "inmodel_groups.ndjson",
            &[
                "InModelGroups.TT",
                "InModelGroups.M",
                "InModelGroups.F",
                "InModelGroups.N",
                "InModelGroups.H",
                "InModelGroups.P",
            ],
            60,
        );
    }

    /// `CON_LECHE_INMODEL=0`'s effect, as the parse sees it: the block is
    /// pushed bare, nothing is generated, and the decline is left to the fold.
    #[test]
    fn the_modeller_can_be_turned_off() {
        let r = parse_bytes(&InProcess, &fixture_bytes("inmodel_mutual.ndjson"), false, false)
            .unwrap_or_else(|(e, l)| panic!("{}: {}", l, message(&e)));
        assert!(r.in_modelled.is_empty());
        assert_eq!(r.gen_records, 0);
        assert!(r.gen_owner.is_empty());
    }

    /// The prelude is not the modeller's business at all — the parse never
    /// sees one since con-leche task #293 — and the nested fixture, which
    /// declares its own `Nat`/`List`, models every one of its seven blocks.
    #[test]
    fn the_modeller_needs_no_prelude() {
        let r = parse_fixture("inmodel_nested.ndjson");
        assert_eq!(r.in_modelled.len(), 7);
        assert!(r.gen_records > 0);
    }
}
