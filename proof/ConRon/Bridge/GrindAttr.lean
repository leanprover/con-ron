/-
# `ConRon.Bridge.GrindAttr` — the bridge's `grind` lemma set

`register_grind_attr` declares the attribute with an
`initialize`, so it is usable only in modules that import this one; the
lemmas themselves are in `Bridge/Grind.lean` and next to the walks.
-/
import Lean

/-- The bridge's `grind` vocabulary: the store order, the
transports, the answer atoms' equations and the walks' arm lemmas.  A
Theorem 1 proof uses it as `sym only [bridge_grind] => vcgen [...] <;> finish`. -/
register_grind_attr bridge_grind
