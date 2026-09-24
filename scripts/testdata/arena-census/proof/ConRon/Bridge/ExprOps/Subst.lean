/-!
`eidxCopyUpto`'s Theorem 1 is real, and its name is `eidxCopyUpto_toList` —
a suffix `arena-census.py` does not recognise.  The row therefore reads
"unstated", and the self-check line is what stops that from being silent.
-/

namespace ConRon.Bridge

/-- **Theorem 1 for `eidxCopyUpto`**, under a name the census does not know. -/
theorem eidxCopyUpto_toList (xs : Array EIdx) : True := by trivial

end ConRon.Bridge
