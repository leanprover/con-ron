# con-ron – con-leche in Rust

This is the external Lean checker [con-leche](https://github.com/leanprover/con-leche), ported to Rust very closely.

So closely, in fact, that we can use [Aeneas](https://github.com/AeneasVerif/aeneas) to [prove the Rust implementation of the checker's core to be equivalent to the one in Lean](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Installed.lean#L3241-L3252) (partial correctness, the Rust code has [additional failure conditions](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/core_types.rs#L87-L92)), and thus [inherits the consistency properties of `con-leche`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L238-L259).

This was written by AI under supervision from Joachim Breitner at the [Lean FRO](https://lean-fro.org/). This README is genuinely human written; the rest of the repository is not. The file [`OVERVIEW.md`](./OVERVIEW.md) contains a much more detailed, AI written exposition of the project. 

This is not a high assurance verification effort, given the reliance on Aeneas as a Rust-to-Lean translator. The goal is to make it very plausible that the Rust implementation follows the Lean implementation very closely.

The point is that with `con-leche` having a [formal consistency proof](https://github.com/leanprover/con-ron/blob/master/vendor/con-leche/ConLeche/MainTheorem.lean#L63-L80), any remaining unsoundness bugs are most likely found in Lean’s compiler or runtime (including the bignum library used). Such a bug will very unlikely exist in the Rust compiler or runtime at the same time, so by checking a proof with both `con-leche` and `con-ron`, you gain a high level of protection against that class of bugs.

[Performance](./OVERVIEW.md#63-performance) of `con-ron` is currently not particularly impressive (about 2× wall time and space over `con-leche`, oddly at roughtly the same instruction count), likely because by following the Lean code and data structure design closely it implements idioms that are not particularly well suited for Rust.

Unsolicited PRs against this repo are unlikely to be useful; well-written issues with bug reports or feature requests are welcome.
