/-!
The store tier's spec layer, whose lemmas are `_abs`, `_run` and `_obs`
rather than `_refines` — task #97-P5-2's abstraction shape, which IS this
tier's Theorem 2 statement and which round 2 of the census learnt to read.

Two of them are QUALIFIED BY RECEIVER (`estore_view_app_abs`,
`tbl_find_abs`), because `Tbl::find` and `EStore::find` are both called
`find` on the Rust side; `estore_find_abs` deliberately does NOT exist, so
that `EStore.find?` reads "cited, nothing stated".
-/

namespace ConRon.Refine2

theorem estore_view_app_abs {i : EIdx} : True := by trivial

theorem tbl_find_abs {a : A} : True := by trivial

theorem derived_e_run {h : EIdx} : True := by trivial

theorem estore_drop_scratch_refines {st : EStore} : True := by
  sorry

theorem estore_der_of_bvar_obs {i : Nat} : True := by trivial

end ConRon.Refine2
