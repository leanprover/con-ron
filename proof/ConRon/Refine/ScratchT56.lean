import ConLeche.Kernel.StdAxioms

open ConLeche

theorem matchesPin_congr {p q : ConstantVal} (hn : p.name = q.name)
    (hl : p.levelParams = q.levelParams) (ht : p.type.erasePw = q.type.erasePw)
    (cv : ConstantVal) :
    ConstantVal.matchesPin cv p = ConstantVal.matchesPin cv q := by
  simp [ConstantVal.matchesPin, hn, hl, ht]

example (cv) : ConstantVal.matchesPin cv iffA.toConstantVal
    = ConstantVal.matchesPin cv iffRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv
example (cv) : ConstantVal.matchesPin cv iffIntroA.toConstantVal
    = ConstantVal.matchesPin cv iffIntroRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv
example (cv) : ConstantVal.matchesPin cv iffRecA.toConstantVal
    = ConstantVal.matchesPin cv iffRecRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv
example (cv) : ConstantVal.matchesPin cv nonemptyA.toConstantVal
    = ConstantVal.matchesPin cv nonemptyRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv
example (cv) : ConstantVal.matchesPin cv nonemptyIntroA.toConstantVal
    = ConstantVal.matchesPin cv nonemptyIntroRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv
example (cv) : ConstantVal.matchesPin cv nonemptyRecA.toConstantVal
    = ConstantVal.matchesPin cv nonemptyRecRaw.toConstantVal :=
  matchesPin_congr rfl rfl rfl cv
example (cv) : ConstantVal.matchesPin cv propextA
    = ConstantVal.matchesPin cv propextRaw :=
  matchesPin_congr rfl rfl rfl cv
example (cv) : ConstantVal.matchesPin cv choiceA
    = ConstantVal.matchesPin cv choiceRaw :=
  matchesPin_congr rfl rfl rfl cv
