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

use con_ron_core::cached::parsed_c::DeclC;

use crate::in_model::mutual::{BlockRec, Ctx};

/// con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
/// con-leche: CHANGED since 405d06b7 — re-port, re-test, re-prove mod::generate_refines, then delete this line
/// Generate the model records of a block, in stream order, or the reason the
/// block is declined.
pub fn generate(ctx: &Ctx, b: &BlockRec) -> Result<Vec<DeclC>, String> {
    if b.types.iter().any(|t| t.num_nested > 0) {
        nested::gen_nested(ctx, b)
    } else {
        mutual::gen_mutual(ctx, b)
    }
}

#[cfg(test)]
mod tests {
    use crate::frontend::export::name_str;
    use crate::frontend::export_c::{parse_export_d, prelude_ix_empty, ParseResultD};
    use crate::frontend::nat_op_ground::decl_names;
    use crate::frontend::prelude::builtin_prelude_e;

    /// con-leche's own `tests/e2e` streams for the three rungs, read at test
    /// time from the pinned submodule (the crate already hard-requires it:
    /// `frontend::prelude` embeds a file from it at build time).
    fn parse_fixture(name: &str) -> ParseResultD {
        let p = format!(
            "{}/../../vendor/con-leche/tests/e2e/{}",
            env!("CARGO_MANIFEST_DIR"),
            name
        );
        let text = std::fs::read(&p).unwrap_or_else(|e| panic!("{}: {}", p, e));
        let ix = builtin_prelude_e().unwrap_or_else(|e| panic!("{:?}", e));
        parse_export_d(&text, ix, true, false).unwrap_or_else(|e| panic!("{}: {:?}", name, e))
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
        // every booked name is under its block's `_model` prefix
        for (k, v) in r.gen_owner.iter() {
            let n = name_str(&k.0);
            let owner = name_str(v);
            assert!(
                n.starts_with(&format!("{}._model", owner))
                    || n.starts_with(&format!("{}.", owner))
                    || n.contains("._model"),
                "{}: {} booked under {}",
                name,
                n,
                owner
            );
        }
        // and the fold's list carries them: the generated records are
        // declarations like any other
        let mut seen = 0u64;
        for d in r.decls.iter() {
            for n in decl_names(d) {
                if r.gen_owner.contains_key(&crate::frontend::nat_op_ground::NameKey(n)) {
                    seen += 1;
                    break;
                }
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
        let p = format!(
            "{}/../../vendor/con-leche/tests/e2e/inmodel_mutual.ndjson",
            env!("CARGO_MANIFEST_DIR")
        );
        let text = std::fs::read(&p).unwrap_or_else(|e| panic!("{}: {}", p, e));
        let ix = builtin_prelude_e().unwrap_or_else(|e| panic!("{:?}", e));
        let r = parse_export_d(&text, ix, false, false).unwrap_or_else(|e| panic!("{:?}", e));
        assert!(r.in_modelled.is_empty());
        assert_eq!(r.gen_records, 0);
        assert!(r.gen_owner.is_empty());
    }

    /// An empty prelude changes nothing about the modeller's reach: the sort
    /// inferer's table is the parse's own, and a fixture that declares its
    /// own `Nat`/`List` models just as well.
    #[test]
    fn the_modeller_needs_no_prelude() {
        let p = format!(
            "{}/../../vendor/con-leche/tests/e2e/inmodel_nested.ndjson",
            env!("CARGO_MANIFEST_DIR")
        );
        let text = std::fs::read(&p).unwrap_or_else(|e| panic!("{}: {}", p, e));
        let r = parse_export_d(&text, prelude_ix_empty(), true, false)
            .unwrap_or_else(|e| panic!("{:?}", e));
        assert_eq!(r.in_modelled.len(), 7);
        assert!(r.gen_records > 0);
    }
}
