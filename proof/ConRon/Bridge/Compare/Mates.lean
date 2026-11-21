/-
# `ConRon.Bridge.Compare.Mates` — the challenge's record mates

`Arena/Justify.lean`'s `recordMatesGo` against con-leche's `recordMates`: each name an inductive
block declares, mapped to the names of every block that declares it.  The twin's map is keyed
by handles; `MatesRel` relates it to con-leche's at every key, with every handle in it
persistent, so the relation survives the scratch tiers of the jobs that read it (`pmono`), and
gives `Compare/Needs.lean`'s `MatesDen` at any well-formed store (`toDen`).
-/
module

public import ConRon.Bridge.Compare.Needs
public import ConRon.Bridge.Checker.Inv
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Canon

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-- con-leche: ConLeche/Cached/Justify.lean:135-142 recordMates — **the twin's mates denote
con-leche's**: every key and every listed handle persistent, every key denoting a name whose
con-leche mates its list covers, and every name con-leche maps to some mates the denotation of a
key. -/
structure MatesRel (st : EStore) (mates : Std.HashMap NIdx (List NIdx))
    (matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)) : Prop where
  pers : ∀ n ms, mates[n]? = some ms → PersN n ∧ ∀ h ∈ ms, PersN h
  cover : ∀ n ms, mates[n]? = some ms → ∃ nm, denoteN st.ns n = some nm ∧
    NamesCover st ms (matesU.getD nm #[]).toList
  keys : ∀ nm m, m ∈ (matesU.getD nm #[]).toList → ∃ n, (mates[n]?).isSome = true ∧
    denoteN st.ns n = some nm

/-- con-leche: none — `MatesRel` across a persistent extension. -/
theorem MatesRel.pmono {st st' : EStore} {mates : Std.HashMap NIdx (List NIdx)}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)} (h : MatesRel st mates matesU)
    (hx : PExt st st') : MatesRel st' mates matesU where
  pers := h.pers
  cover := fun n ms hn => by
    obtain ⟨nm, hd, hc⟩ := h.cover n ms hn
    refine ⟨nm, denoteN_pext hx (h.pers n ms hn).1 hd, fun m hm => ?_⟩
    obtain ⟨k, hk, hkd⟩ := hc m hm
    exact ⟨k, hk, denoteN_pext hx ((h.pers n ms hn).2 k hk) hkd⟩
  keys := fun nm m hm => by
    obtain ⟨n, hs, hd⟩ := h.keys nm m hm
    obtain ⟨ms, hms⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨n, hs, denoteN_pext hx (h.pers n ms hms).1 hd⟩

/-- con-leche: none — `MatesRel` across a store extension. -/
theorem MatesRel.mono {st st' : EStore} {mates : Std.HashMap NIdx (List NIdx)}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)} (h : MatesRel st mates matesU)
    (hx : Ext st st') : MatesRel st' mates matesU where
  pers := h.pers
  cover := fun n ms hn => by
    obtain ⟨nm, hd, hc⟩ := h.cover n ms hn
    exact ⟨nm, denoteN_ext hd hx, hc.mono hx⟩
  keys := fun nm m hm => by
    obtain ⟨n, hs, hd⟩ := h.keys nm m hm
    exact ⟨n, hs, denoteN_ext hd hx⟩

/-- con-leche: none — **`MatesRel` is `MatesDen`** at a well-formed store: a key's list covers
its name's mates, and a handle that is no key denotes a name with none (`denoteN_injS`). -/
theorem MatesRel.toDen {st : EStore} (hwf : StoreWF st) {mates : Std.HashMap NIdx (List NIdx)}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)} (h : MatesRel st mates matesU) :
    MatesDen st mates matesU := by
  refine ⟨fun n nm hn => ?_, fun nm m hm => ?_⟩
  · cases hms : mates[n]? with
    | some ms =>
      obtain ⟨nm', hd, hc⟩ := h.cover n ms hms
      rw [hn] at hd
      obtain rfl := Option.some.inj hd
      simpa using hc
    | none =>
      intro m hm
      obtain ⟨n', hs, hd⟩ := h.keys nm m hm
      rw [denoteN_injS hwf hd hn, hms] at hs
      exact nomatch hs
  · obtain ⟨n, -, hd⟩ := h.keys nm m hm
    exact ⟨n, hd⟩

/-- con-leche: none — a denoting name list covers what it denotes. -/
theorem NamesCover.of_denoteNList {st : EStore} :
    ∀ {hs : List NIdx} {L : List ConLeche.Name}, Frontend.denoteNList st.ns hs = some L →
      NamesCover st hs L
  | [], L, h => by
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; exact NamesCover.nil _ _
  | h :: hs, L, hd => by
    obtain ⟨y, ys, hy, hys, rfl⟩ := denoteNList_cons_inv hd
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨h, List.mem_cons_self, hy⟩
    · obtain ⟨k, hk, hkd⟩ := NamesCover.of_denoteNList hys m hm
      exact ⟨k, List.mem_cons_of_mem _ hk, hkd⟩

/-- con-leche: ConLeche/Cached/Justify.lean:135-142 recordMates — one block's members inserted,
each mapped to what it had and the block's names. -/
theorem matesInsert_rel {st : EStore} (hwf : StoreWF st) {ns : List NIdx}
    {nsU : List ConLeche.Name} (hns : Frontend.denoteNList st.ns ns = some nsU)
    (hpns : ∀ h ∈ ns, PersN h) :
    ∀ (block : List IConstantInfo) (blockU : List ConstantInfo)
      (m : Std.HashMap NIdx (List NIdx)) (mU : Std.HashMap ConLeche.Name (Array ConLeche.Name)),
      Frontend.denoteCIList st block = some blockU → (∀ b ∈ block, PersN b.name) →
      MatesRel st m mU →
      MatesRel st (matesInsert m ns block)
        (blockU.foldl (fun m b => m.insert b.name (m.getD b.name #[] ++ nsU.toArray)) mU) := by
  intro block
  induction block with
  | nil =>
    intro blockU m mU hb _ hm
    simp only [Frontend.denoteCIList, Option.some.injEq] at hb
    subst hb; exact hm
  | cons b bs ih =>
    intro blockU m mU hb hpb hm
    obtain ⟨x, xs, hx, hxs, rfl⟩ := denoteCIList_cons hb
    simp only [matesInsert, List.foldl_cons]
    refine ih xs _ _ hxs (fun c hc => hpb c (List.mem_cons_of_mem _ hc)) ?_
    have hbn : denoteN st.ns b.name = some x.name := denoteCI_name hx
    have hpbn : PersN b.name := hpb b List.mem_cons_self
    have happ : nidxAppend (m.getD b.name []) ns 0 ns.length = m.getD b.name [] ++ ns := by
      simp [nidxAppend]
    rw [happ]
    refine ⟨fun n ms hn => ?_, fun n ms hn => ?_, fun nm k hk => ?_⟩
    · rw [Std.HashMap.getElem?_insert] at hn
      split at hn
      · next hbeq =>
        obtain rfl := eq_of_beq hbeq
        obtain rfl := Option.some.inj hn
        refine ⟨hpbn, fun h hh => ?_⟩
        rcases List.mem_append.mp hh with hh | hh
        · cases hg : m[b.name]? with
          | none => rw [Std.HashMap.getD_eq_getD_getElem?, hg] at hh; exact nomatch hh
          | some ms₀ =>
            rw [Std.HashMap.getD_eq_getD_getElem?, hg] at hh
            exact (hm.pers _ ms₀ hg).2 h hh
        · exact hpns h hh
      · exact hm.pers n ms hn
    · rw [Std.HashMap.getElem?_insert] at hn
      split at hn
      · next hh =>
        obtain rfl := eq_of_beq hh
        obtain rfl := Option.some.inj hn
        refine ⟨x.name, hbn, ?_⟩
        rw [Std.HashMap.getD_insert]
        simp only [beq_self_eq_true, ↓reduceIte, Array.toList_append]
        refine NamesCover.append (fun m' hm' => ?_) ((NamesCover.of_denoteNList hns).sub
          (fun k hk => List.mem_append_right _ hk))
        cases hg : m[b.name]? with
        | none =>
          obtain ⟨n', hs, hd⟩ := hm.keys x.name m' hm'
          rw [denoteN_injS hwf hd hbn, hg] at hs
          exact nomatch hs
        | some ms₀ =>
          obtain ⟨nm₀, hd₀, hc₀⟩ := hm.cover _ ms₀ hg
          rw [hbn] at hd₀
          obtain rfl := Option.some.inj hd₀
          obtain ⟨k, hk, hkd⟩ := hc₀ m' hm'
          refine ⟨k, List.mem_append_left _ ?_, hkd⟩
          rw [Std.HashMap.getD_eq_getD_getElem?, hg]; exact hk
      · next hh =>
        obtain ⟨nm, hd, hc⟩ := hm.cover n ms hn
        refine ⟨nm, hd, ?_⟩
        rw [Std.HashMap.getD_insert]
        have hne : (x.name == nm) = false := by
          rw [← denoteN_beqS hwf hbn hd]; simpa using hh
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        exact hc
    · rw [Std.HashMap.getD_insert] at hk
      split at hk
      · next hh =>
        obtain rfl := eq_of_beq hh
        exact ⟨b.name, by rw [Std.HashMap.getElem?_insert]; simp, hbn⟩
      · obtain ⟨n, hs, hd⟩ := hm.keys nm k hk
        refine ⟨n, ?_, hd⟩
        rw [Std.HashMap.getElem?_insert]
        split <;> simp_all

/-- con-leche: none — a constant's name is persistent where the constant is. -/
theorem PersCI.name {c : IConstantInfo} (h : PersCI c) : PersN c.name := by
  cases c <;> simp only [PersCI] at h
  all_goals first | exact h.name | exact h.1.name

/-- con-leche: ConLeche/Cached/Justify.lean:135-142 recordMates — **THEOREM 1 for the record
mates**: the twin's map over persistent records, from one denoting con-leche's mates of a prefix
`pre`, denotes con-leche's mates of `pre` and the denoted records. -/
theorem recordMatesGo_rel {st : EStore} (hwf : StoreWF st) :
    ∀ (ds : List IDeclaration) (dsU pre : List Declaration) (m : Std.HashMap NIdx (List NIdx)),
      denoteDecls st ds = some dsU → (∀ x ∈ ds, PersDecl x) →
      MatesRel st m (ConLeche.Cached.recordMates pre.toArray) →
      MatesRel st (recordMatesGo m ds) (ConLeche.Cached.recordMates (pre ++ dsU).toArray) := by
  intro ds
  induction ds with
  | nil =>
    intro dsU pre m hd _ hm
    simp only [denoteDecls, Option.some.injEq] at hd
    subst hd; simp only [recordMatesGo]; simpa using hm
  | cons d ds ih =>
    intro dsU pre m hd hp hm
    simp only [denoteDecls] at hd
    split at hd
    · next x xs hx hxs =>
      obtain rfl := Option.some.inj hd
      have hpd := hp d List.mem_cons_self
      have hps : ∀ y ∈ ds, PersDecl y := fun y hy => hp y (List.mem_cons_of_mem _ hy)
      have hsplit : pre ++ x :: xs = (pre ++ [x]) ++ xs := by simp
      rw [hsplit]
      cases d with
      | indDecl block nP =>
        simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
        obtain ⟨bU, hbU, rfl⟩ := hx
        simp only [recordMatesGo]
        refine ih xs _ _ hxs hps ?_
        have hpb : ∀ b ∈ block, PersN b.name := fun b hb => PersCI.name (hpd b hb)
        have hns := denoteCIList_names block bU hbU
        have hstep := matesInsert_rel hwf hns
          (fun h hh => by
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hh
            exact hpb b hb) block bU m _ hbU hpb hm
        simpa [ConLeche.Cached.recordMates, List.foldl_append, blockNames] using hstep
      | axiomDecl v | defnDecl v e hh | thmDecl v e | opaqueDecl v e | quotDecl k v =>
        simp only [recordMatesGo]
        refine ih xs _ _ hxs hps ?_
        cases x with
        | indDecl b nP =>
          simp only [Frontend.denoteDecl] at hx
          first
            | (split at hx <;> simp_all)
            | simp_all
        | _ => simpa [ConLeche.Cached.recordMates, List.foldl_append] using hm
    · exact nomatch hd

/-- con-leche: ConLeche/Cached/Justify.lean:144-146 solutionOf — **the challenge's mates in the
solution the twin builds** denote con-leche's `recordMates` of the denoted records. -/
theorem solutionOf_mates {st : EStore} (hwf : StoreWF st) {I : IStreamIndex}
    {ds : List IDeclaration} {dsU : List Declaration} (hd : denoteDecls st ds = some dsU)
    (hp : ∀ x ∈ ds, PersDecl x) :
    MatesRel st (solutionOf I ds).mates (ConLeche.Cached.recordMates dsU.toArray) := by
  have h0 : MatesRel st (∅ : Std.HashMap NIdx (List NIdx))
      (ConLeche.Cached.recordMates ([] : List Declaration).toArray) := by
    refine ⟨fun n ms h => by simp at h, fun n ms h => by simp at h, fun nm m h => ?_⟩
    simp [ConLeche.Cached.recordMates] at h
  simpa [solutionOf] using recordMatesGo_rel hwf ds dsU [] ∅ hd hp h0

end ConRon.Bridge
