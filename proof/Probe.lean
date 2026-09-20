import Std.Data.HashMap
import ConLeche.Kernel.Expr

open ConLeche

structure Foo where
  a : Nat
  m : ConLeche.BinderMeta
  deriving DecidableEq, Repr, Inhabited, Hashable

instance : BEq Foo := instBEqOfDecidableEq
example : LawfulBEq Foo := inferInstance

-- HashMap lemma names
example (m : Std.HashMap Foo Nat) (k a : Foo) (v : Nat) :
    (m.insert a v)[k]? = if k == a then some v else m[k]? := by
  simp [Std.HashMap.getElem?_insert]

example (k : Foo) : (∅ : Std.HashMap Foo Nat)[k]? = none := by simp

#check @ConLeche.packData
#check @ConLeche.hash32
#check @ConLeche.hashOfData
#check @ConLeche.bvarOfData
#check @ConLeche.fvarOfData
#check @ConLeche.lpOfData
#check @ConLeche.satSucc
#check @ConLeche.satPred
#check @ConLeche.levelHash
#check @ConLeche.levelsHash
#check @ConLeche.levelHasParam
#check @ConLeche.levelsHaveParam
#check @ConLeche.Name.hashData
#check @ConLeche.Level.hashData
#check @ConLeche.Expr.data
#check (inferInstance : Hashable ConLeche.PropWhen)
#check (inferInstance : Hashable ConLeche.Literal)
#check (inferInstance : DecidableEq ConLeche.Literal)

structure Empt where
  deriving DecidableEq, Repr, Inhabited, Hashable
instance : BEq Empt := instBEqOfDecidableEq
example : LawfulBEq Empt := inferInstance

-- generic table with instance binders in the structure signature
structure Tbl (α : Type) [BEq α] [Hashable α] (ι : Type) (δ : Type) where
  nodes : Array α
  der : Array δ
  cons : Std.HashMap α ι

def Tbl.empty [BEq α] [Hashable α] : Tbl α ι δ := ⟨#[], #[], ∅⟩

#check (Tbl.empty : Tbl Foo Nat UInt64)
