# con-ron – con-leche in Rust

This is the external Lean checker [con-leche](https://github.com/leanprover/con-leche), ported to Rust very closely.

This was written by AI under supervision from Joachim Breitner at the [Lean FRO](https://lean-fro.org/). This README is genuinely human written; the rest of the repository is not. The file [`OVERVIEW.md`](./OVERVIEW.md) contains a much more detailed, AI written exposition of the project. 

## Goal

The point of this exercise is that with `con-leche` having a [formal consistency proof](https://github.com/leanprover/con-leche/blob/78ded4b6fc9a4d9ab809e8ca2c75c56537c41bff/ConLeche/MainTheorem.lean#L90-L117), any remaining unsoundness bugs are most likely found in Lean’s compiler or runtime (including the bignum library used). Such a bug will very unlikely exist in the Rust compiler or runtime at the same time, so by checking a proof with both `con-leche` and `con-ron`, you gain a high level of protection against that class of bugs.

It is also a goal of con-ron to have good performance; verified code should not be slower than unverified.

## Method

A previous version of con-ron translated the Lean code of con-leche very closely. This worked, but led to unsatisfying performance, because con-leche uses data structures that worked well on Lean but poorly in Rust.

Therefore, con-ron now deviates from con-leche in term representation and its approach to caching and memoization, while still sticking close to con-leche's algorithm.

To that end, con-ron implements a twin of con-leche's *pure* checking algorithm, still in Lean, but using data structures that closely match what we want to use in the Rust implementation. This twin is proven to be (partially) correct wrt the pure implementation by a simulation (Theorem 1). The Rust implementation is then proven (partially) correct to the twin by Theorem 2, via the Aeneas-generated model. Theorem 1 has a sibling in con-leche, where the pure checker is related to the actual caching implementation. Theorem 2 is kept as mechanical as possible (and our bespoke `lockstep` tactic automates much of it).

In the end we can compose all these to the end-to-end main consistency theorem TODO and main corollary TODO, matching what was proven about con-leche.

Not covered by these theorems is the main driver (i.e. reading the input file, scheduling threads), just as in con-leche.

This is not a high assurance verification effort, given the reliance on Aeneas as a Rust-to-Lean translator. The goal is to make it very plausible that the Rust implementation follows the Lean implementation very closely.

## Implementation ideas

Like nanoda, we cons-hash expressions and put them into one big data structure (the DAG), with two tiers (a persistent one and a scratch tier for the per-declaration intermediates) and an `EIdx` (a `u32`) pointing into that data structure, with one bit indicating which tier to use.

To further refine this approach, our DAG does not store an `enum ExprView`. Rust sizes enums by the largest member, which is wasteful when most nodes are `Expr.app`. Instead, we have one array per constructor, with just the fields stored there, and the `EIdx` reserves four bits to indicate which constructor this is. This leads to very compact, uniform arrays and some operations (e.g. `is_app`) can be resolved without dereferencing. Names, levels, level lists and binder data (the `PropWhen` field) are also hash-consed.

## Performance

After the rewrite to use better data structures, [performance](./OVERVIEW.md#9-performance) of `con-ron` is rather good, often better than with con-leche or nanoda.

## Contributions

Unsolicited PRs against this repo are unlikely to be useful; well-written issues with bug reports or feature requests are welcome.
