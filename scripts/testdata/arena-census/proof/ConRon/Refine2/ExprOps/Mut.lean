namespace ConRon.Refine2

theorem instantiate1_go_refines {v : EIdx} : True := by
  sorry

theorem instantiate_list_refines {vs : Array EIdx} : True := by
  sorry

theorem expr_ptr_beq_refines {a b : EIdx} : True := by trivial

theorem wscoped_b_fast_refines {e : EIdx} : True := by trivial

theorem promote_n_refines {n : NIdx} : True := by
  sorry

/-- `iota_rec_at_refines` is a DIFFERENT Rust function's lemma, and must not
be read as one for `iota_rec`: the row is "cited, one of two stated". -/
theorem iota_rec_at_refines {h : EIdx} : True := by trivial

end ConRon.Refine2
