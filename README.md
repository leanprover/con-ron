# con-ron – con-leche in Rust

This is the external Lean checker [con-leche](https://github.com/leanprover/con-leche), ported to Rust very closely.

So closely, in fact, hat we can use aeneas to prove the rust implementation to be equivalent to the Lean implementation (partial correctness, the Rust code has additional failure conditions), and thus inherits the consistency properties of `con-leche`.

This was written by AI under supervision from Joachim Breitner at the Lean FRO. This README is genuienly human written; the rest of the repository is not. The file [`OVERVIEW.md`](./OVERVIEW.md) contains more much more detailed, AI written exposition of the project. 

This is not a high assurance verification effort, given the reliance on aeneas as a Rust-to-Lean translator. The goal is make it very plausible that the rust implementation follows the lean implementation very closely.

The point is that with `con-leche` having a formal consistency proof, any remaining unsoundness bugs are most likely found in Lean’s compiler or runtime (including the bignum library used). Such a bug will very unlikely exist in the Rust compiler or runtime at the same time, so by checking a proof with both `con-leche` and `con-ron`, you gain a high level of protection against that class of bugs.

Performance of `con-ron` is currently not particularly impressive (about 2× time and space over `con-leche`), likely becaue by following the Lean code and data structure design closely it implements idioms that are not particularly well suited for Rust.

Unsolicited PRs against this repo are unlikely to be useful; well-written issues with bug reports or feature requests are welcome.
