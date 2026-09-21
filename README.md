# con-ron – con-leche in Rust

This is the external Lean checker [con-leche](https://github.com/leanprover/con-leche), ported to Rust very closely.

This was written by AI under supervision from Joachim Breitner at the [Lean FRO](https://lean-fro.org/). This README is genuinely human written; the rest of the repository is not. The file [`OVERVIEW.md`](./OVERVIEW.md) contains a much more detailed, AI written exposition of the project. 

## Goal

The point of this exercise is that with `con-leche` having a [formal consistency proof](https://github.com/leanprover/con-leche/blob/78ded4b6fc9a4d9ab809e8ca2c75c56537c41bff/ConLeche/MainTheorem.lean#L90-L117), any remaining unsoundness bugs are most likely found in Lean’s compiler or runtime (including the bignum library used). Such a bug will very unlikely exist in the Rust compiler or runtime at the same time, so by checking a proof with both `con-leche` and `con-ron`, you gain a high level of protection against that class of bugs.

## Method

This translation sticks to the lean code so closely that we can use [Aeneas](https://github.com/AeneasVerif/aeneas) to [prove the Rust implementation of the checker's core to be equivalent to the one in Lean](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Installed.lean#L3289-L3305) (partial correctness, the Rust code has [additional failure conditions](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/kernel/core_types.rs#L87-L92)), and thus [inherits the consistency properties of `con-leche`](https://github.com/leanprover/con-ron/blob/master/proof/ConRon/Refine/Main.lean#L730-L746).

This is not a high assurance verification effort, given the reliance on Aeneas as a Rust-to-Lean translator. The goal is to make it very plausible that the Rust implementation follows the Lean implementation very closely.

## Unsafe code

The con-leche code and data structures are tailored for a reference-counting runtime, and for efficient representation of inductives/enum, so a direct translation incurs a sizable memory usage penalty.

So for now we include our own pointer abstraction that takes care of reference counting and pointer tagging ([`ron::tagged`](https://github.com/leanprover/con-ron/blob/master/crates/con-ron-core/src/ron/tagged.rs#L1-L20)), replacing the use of `std::Arc` here. This is unsafe code outside the proof, and should be considered part of the “run-time”. More details in the OVERVIEW.

This is not a satisfying state of affairs, and future work will involve refactoring the code to use a nanoda-style explicit expression DAG; then this module can be dropped.

## Performance

[Performance](./OVERVIEW.md#72-performance) of `con-ron` is currently not particularly impressive (up to 1.6× wall time, more with more threads), likely because by following the Lean code and data structure design closely it implements idioms that are not particularly well suited for Rust.

## Contributions

Unsolicited PRs against this repo are unlikely to be useful; well-written issues with bug reports or feature requests are welcome.
