# con-ron

A Rust port of [con-leche](https://github.com/leanprover/con-leche), the
consistency-proven Lean checker, together with a Lean proof (via
[Aeneas](https://github.com/AeneasVerif/aeneas)) that the Rust checker refines
the Lean one — so con-leche's main theorem covers the Rust binary, with the
Lean runtime out of the trusted base.

See `DESIGN.md` for the design, plan, and work log.

## Setup

Dependencies not on the machine (the Rust nightly Charon needs, Charon,
Aeneas) come from `flake.nix`; `direnv allow` loads them.  Lean toolchains
come from the system `elan`.  Submodules: `git submodule update --init`.
