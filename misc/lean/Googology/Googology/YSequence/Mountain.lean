import Googology.YSequence.Index

namespace Ysequence

section Types

/-- 𝕊 -/
def ValueList : Type :=
  { s : List ℕ+ // if h : 0 < s.length then Index.get (⟨0, h⟩ : Index s) = 1 else True }

/-- ^𝕊 -/
def ParentList : Type :=
  { t : List (Option ℕ) // ∀ i : Index t, WithBot.lt.lt i.get i.val }

lemma ParentList.head_eq_none {t : ParentList} (h : 0 < t.val.length) :
    Index.get (⟨0, h⟩ : Index t.val) = none :=
  Nat.WithBot.lt_zero_iff.mp (t.property _)

/-- 𝕊⁽²⁾ -/
structure ValueParentListPair where
  values : ValueList
  parents : ParentList
  pairable : Pairable values.val parents.val

theorem toNoneOrLtId_parent_list_get (x : ValueParentListPair) :
    ToNoneOrLtId (inIndexElim (Index.get ∘ x.pairable.transfer) none) :=
  by
  apply toNoneOrLtId_inIndexElim_val_none_of_forall_index
  intro
  rw [← Pairable.val_transfer x.pairable _]
  exact x.parents.property _

/-- 𝕊⁽²⁾* = {x : 𝕊⁽²⁾ // x.is_orphanless} -/
def ValueParentListPair.IsOrphanless (x : ValueParentListPair) : Prop :=
  ∀ i : Index x.values.val, 1 < i.get.val → (x.pairable.transfer i).get.isSome

instance : DecidablePred ValueParentListPair.IsOrphanless := fun _ => Fintype.decidableForallFintype

example : { x : ValueParentListPair // ValueParentListPair.IsOrphanless x } :=
  let s : List ℕ+ := [1, 3, 4]
  let t := [none, some 0, some 1]
  ⟨⟨⟨s, by decide⟩, ⟨t, by decide⟩, by decide⟩, by decide⟩

def GenericMountain (α : Type) : Type :=
  { m : List (List α) // ∀ c ∈ m, c ≠ [] }

lemma GenericMountain.index_get_ne_nil {α : Type} {m : GenericMountain α} (i : Index m.val) : i.get ≠ [] :=
  m.property _ (Index.get_mem i)

/-- 𝕄ᵥ -/
def ValueMountain : Type :=
  GenericMountain ℕ+

/-- 𝕄ₚ⁻ -/
def ParentMountain : Type :=
  GenericMountain (Option ℕ)

/-- 𝕄ₚ = {P : 𝕄ₚ⁻ // P.IsCoherent} -/
def ParentMountain.IsCoherent (P : ParentMountain) : Prop :=
  ∀ q : Index₂ P.val,
    let i := q.val.fst
    let j := q.val.snd
    (q.get = none ↔ j = q.fst.get.length - 1) ∧ WithBot.lt.lt q.get i ∧
      ∀ p ∈ q.get, ∃ q' : Index₂ P.val, q'.val = (p, j)

lemma ParentMountain.IsCoherent.get_eq_none_iff {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : q.get = none ↔ q.val.snd = q.fst.get.length - 1 :=
  (hP q).left

lemma ParentMountain.IsCoherent.get_lt {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : WithBot.lt.lt q.get q.val.fst :=
  (hP q).right.left

lemma ParentMountain.IsCoherent.exists_index_eq_val {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : ∀ p ∈ q.get, ∃ q' : Index₂ P.val, q'.val = (p, q.val.snd) :=
  (hP q).right.right

instance : DecidablePred ParentMountain.IsCoherent := fun _ => Fintype.decidableForallFintype

theorem ParentMountain.IsCoherent.get_isSome_iff {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : q.get.isSome ↔ q.val.snd ≠ q.fst.get.length - 1 :=
  Option.ne_none_iff_isSome.symm.trans (Decidable.not_iff_not.mpr (hP.get_eq_none_iff _))

theorem ParentMountain.IsCoherent.exists_index_of_isSome {P : ParentMountain} (hP : P.IsCoherent)
    {q : Index₂ P.val} (hq : q.get.isSome) :
    ∃ q' : Index₂ P.val, q'.val = (q.get.get hq, q.val.snd) :=
  by simp [hP.exists_index_eq_val]

theorem ParentMountain.IsCoherent.head_eq_none {P : ParentMountain} (hP : P.IsCoherent)
    (h : 0 < P.val.length) (j : Index (Index.get (⟨0, h⟩ : Index P.val))) :
    Index₂.get (⟨⟨0, h⟩, j⟩ : Index₂ P.val) = none :=
  Nat.WithBot.lt_zero_iff.mp (hP.get_lt _)

theorem ParentMountain.IsCoherent.head_length {P : ParentMountain} (hP : P.IsCoherent)
    (h : 0 < P.val.length) : (Index.get (⟨0, h⟩ : Index P.val)).length = 1 :=
  by
  have head_length_pos := List.length_pos_of_ne_nil (P.index_get_ne_nil ⟨0, h⟩)
  rw [← Nat.sub_eq_iff_eq_add head_length_pos]
  exact ((hP.get_eq_none_iff ⟨⟨0, h⟩, ⟨0, head_length_pos⟩⟩).mp (hP.head_eq_none _ _)).symm

def ParentMountain.IsCoherent.indexParentOfIsSome {P : ParentMountain} (hP : P.IsCoherent)
    {q : Index₂ P.val} (hq : q.get.isSome) : Index₂ P.val :=
  by
  refine ⟨⟨q.get.get hq, ?_⟩, ⟨q.val.snd, ?_⟩⟩
  all_goals
    cases' hP.exists_index_of_isSome hq with q' hq'
    rw [Index₂.val, Prod.eq_iff_fst_eq_snd_eq] at hq'
    simp only [Index₂.fst_val, Index₂.snd_val] at hq'
  · exact lt_of_eq_of_lt hq'.left.symm q'.val_fst_lt
  · refine' lt_of_eq_of_lt hq'.right.symm (lt_of_lt_of_eq q'.val_snd_lt _)
    congr
    exact Fin.eq_of_val_eq hq'.left

@[simp]
lemma ParentMountain.IsCoherent.indexParentOfIsSome_val {P : ParentMountain} (hP : P.IsCoherent)
    {q : Index₂ P.val} (hq : q.get.isSome) :
    let j := q.val.snd
    (hP.indexParentOfIsSome hq).val = (q.get.get hq, j) :=
  rfl

def ParentMountain.IsCoherent.indexAboveOfIsSome {P : ParentMountain} (hP : P.IsCoherent)
    {q : Index₂ P.val} (hq : q.get.isSome) : Index₂ P.val :=
  by
  refine ⟨q.fst, ⟨q.val.snd + 1, ?_⟩⟩
  have h := mt (hP.get_eq_none_iff q).mpr (Option.ne_none_iff_isSome.mpr hq)
  rw [lt_iff_le_and_ne]
  constructor
  · exact Nat.succ_le_of_lt q.val_snd_lt
  · rw [← Ne, ← Nat.succ_ne_succ] at h
    apply ne_of_ne_of_eq h
    exact Nat.sub_add_cancel (List.length_pos_of_ne_nil (P.index_get_ne_nil _))

@[simp]
lemma ParentMountain.IsCoherent.indexAboveOfIsSome_val {P : ParentMountain} (hP : P.IsCoherent)
    {q : Index₂ P.val} (hq : q.get.isSome) :
    let i := q.val.fst
    let j := q.val.snd
    (hP.indexAboveOfIsSome hq).val = (i, j + 1) :=
  rfl

/-- 𝕄⁻ -/
structure Mountain where
  values : ValueMountain
  parents : ParentMountain
  pairable : Pairable₂ values.val parents.val

/-- 𝕄* = {x : Mountain // x.parents.IsCoherent ∧ x.is_orphanless} -/
def Mountain.IsOrphanless (x : Mountain) : Prop :=
  ∀ i : Index x.values.val,
    1 < (Index₂.get ⟨i, ⟨0, List.length_pos_of_ne_nil (x.values.index_get_ne_nil _)⟩⟩).val →
      (Index₂.get
        ⟨x.pairable.fst.transfer i,
          ⟨0, List.length_pos_of_ne_nil (x.parents.index_get_ne_nil _)⟩⟩).isSome

instance : DecidablePred Mountain.IsOrphanless := fun _ => Fintype.decidableForallFintype

theorem Mountain.base_value_eq_one_of_parents_isCoherent_of_isOrphanless_of_height_eq_one
    {x : Mountain} (h_coherent : x.parents.IsCoherent) (h_orphanless : x.IsOrphanless)
    {i : Index x.values.val} (h : i.get.length = 1) :
    Index₂.get ⟨i, ⟨0, List.length_pos_of_ne_nil (x.values.index_get_ne_nil _)⟩⟩ = 1 :=
  by
  by_contra H
  have := h_orphanless i (by apply lt_of_le_of_ne (PNat.one_le _) (Ne.symm H))
  rw [← Option.ne_none_iff_isSome] at this
  apply this
  rw [h_coherent.get_eq_none_iff]
  conv_rhs => rw [← (x.pairable.snd _).def, h]
  rfl

theorem Mountain.head_value_eq_one_of_parents_isCoherent_of_isOrphanless_of_length_pos
    {x : Mountain} (h_coherent : x.parents.IsCoherent) (h_orphanless : x.IsOrphanless)
    (len_pos : 0 < x.values.val.length) :
    Index₂.get ⟨⟨0, len_pos⟩, ⟨0, List.length_pos_of_ne_nil (x.values.index_get_ne_nil _)⟩⟩ = 1 :=
  by
  apply
    Mountain.base_value_eq_one_of_parents_isCoherent_of_isOrphanless_of_height_eq_one h_coherent
      h_orphanless
  rw [(x.pairable.snd _).def]
  exact h_coherent.head_length (lt_of_lt_of_eq len_pos x.pairable.fst)

def Mountain.IsCrossCoherent (x : Mountain) : Prop :=
  ∃ hP : x.parents.IsCoherent,
    ∀ {q : Index₂ x.parents.val} (hq : q.get.isSome),
      (x.pairable.symm.transfer (hP.indexAboveOfIsSome hq)).get.val =
        (x.pairable.symm.transfer q).get.val -
          (x.pairable.symm.transfer (hP.indexParentOfIsSome hq)).get.val

lemma Mountain.IsCrossCoherent.to_parent_isCoherent {x : Mountain} (h : x.IsCrossCoherent) :
    x.parents.IsCoherent :=
  h.fst

lemma Mountain.IsCrossCoherent.get_value_above_eq_of_parent_isSome {x : Mountain}
    (h : x.IsCrossCoherent) {q : Index₂ x.parents.val} (hq : q.get.isSome) :
    have hP : x.parents.IsCoherent := h.to_parent_isCoherent
    (x.pairable.symm.transfer (hP.indexAboveOfIsSome hq)).get.val =
      (x.pairable.symm.transfer q).get.val -
        (x.pairable.symm.transfer (hP.indexParentOfIsSome hq)).get.val :=
  h.snd hq

theorem Mountain.IsCrossCoherent.value_above_lt_value_of_parent_isSome {x : Mountain}
    (h : x.IsCrossCoherent) {q : Index₂ x.parents.val} (hq : q.get.isSome) :
    have hP : x.parents.IsCoherent := h.to_parent_isCoherent
    (x.pairable.symm.transfer (hP.indexAboveOfIsSome hq)).get <
      (x.pairable.symm.transfer q).get :=
  by
  have := (h.get_value_above_eq_of_parent_isSome hq).symm
  rw [Pnat.sub_val_eq_iff_eq_add] at this
  rw [this]
  exact PNat.lt_add_right _ _

theorem Mountain.IsCrossCoherent.value_decrease_upwards {x : Mountain} (h : x.IsCrossCoherent)
    {i : Index x.values.val} {j₁ j₂ : Index i.get} (hj : j₁.val < j₂.val) : j₂.get < j₁.get :=
  by
  cases' j₁ with j₁ hj₁
  cases' j₂ with j₂ hj₂
  dsimp at hj
  revert hj₁ hj₂
  revert j₂
  refine' Nat.le_induction _ _
  · intro hj₁ hj₁'
    have hj₁'' := Nat.pred_lt_pred (Nat.succ_ne_zero _) hj₁'
    rw [Nat.pred_succ, Nat.pred_eq_sub_one, ← Fin.val_mk hj₁,
        ← Index.val_ne_pred_length_iff] at hj₁''
    conv_rhs at hj₁'' => rw [(x.pairable.snd i).def]
    erw [← h.to_parent_isCoherent.get_isSome_iff (x.pairable.transfer ⟨i, ⟨j₁, hj₁⟩⟩)] at hj₁''
    exact h.value_above_lt_value_of_parent_isSome hj₁''
  · intro j₂ _ IH hj₁ hj₂'
    have hj₂ := Nat.lt_trans (Nat.lt_succ_self _) hj₂'
    refine' lt_trans _ (IH _ hj₂)
    have hj₂'' := hj₂'
    rw [← Nat.lt_pred_iff, Nat.pred_eq_sub_one, ← Fin.val_mk hj₂, ← Index.val_ne_pred_length_iff] at hj₂''
    conv_rhs at hj₂'' => rw [(x.pairable.snd i).def]
    erw [← h.to_parent_isCoherent.get_isSome_iff (x.pairable.transfer ⟨i, ⟨j₂, hj₂⟩⟩)] at hj₂''
    exact h.value_above_lt_value_of_parent_isSome hj₂''

theorem Mountain.IsCrossCoherent.eq_of_parents_eq_of_value_eq_where_parent_eq_none
    {x₁ x₂ : Mountain} (hx₁ : x₁.IsCrossCoherent) (hx₂ : x₂.IsCrossCoherent)
    (parents_eq : x₁.parents = x₂.parents)
    (value_eq_where_parent_eq_none :
      ∀ q : Index₂ x₁.parents.val,
        q.get = none →
          (x₁.pairable.symm.transfer q).get =
            (((parents_eq ▸ Pairable₂.refl x₁.parents.val :
                        Pairable₂ x₁.parents.val x₂.parents.val).trans
                    x₂.pairable.symm).transfer
                q).get) :
    x₁ = x₂ :=
  by
  cases' x₁ with V₁ P₁ hVP₁
  cases' x₂ with V₂ P₂ hVP₂
  dsimp at parents_eq value_eq_where_parent_eq_none
  subst parents_eq
  rename' P₁ => P
  simp only [mk.injEq, and_true]
  apply Subtype.ext
  apply (hVP₁.trans hVP₂.symm).list_ext
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  induction' i using Nat.strong_induction_on with i IH₁ generalizing j
  obtain ⟨l, hl⟩ :=
    Nat.exists_eq_succ_of_ne_zero
      (ne_of_lt (List.length_pos_of_ne_nil (V₁.index_get_ne_nil ⟨i, hi⟩))).symm
  have hjl : j ≤ l := Nat.le_of_lt_succ (hl ▸ hj)
  have hl' := Nat.pred_eq_of_eq_succ hl
  revert hj
  refine' Nat.decreasingInduction' _ hjl _
  · intro j' hj'l _ IH₂
    clear! j
    rename' j' => j, hj'l => hjl
    intro hj
    have hj' := lt_of_lt_of_eq hjl (hl'.symm.trans (congr_arg _ (hVP₁.snd _)))
    replace hj' := ne_of_lt hj'
    erw [← hx₁.to_parent_isCoherent.get_isSome_iff (hVP₁.transfer ⟨⟨i, hi⟩, ⟨j, hj⟩⟩)] at hj'
    have lhs_eq := (hx₁.get_value_above_eq_of_parent_isSome hj').symm
    have rhs_eq := (hx₂.get_value_above_eq_of_parent_isSome hj').symm
    rw [Pnat.sub_val_eq_iff_eq_add] at lhs_eq rhs_eq
    erw [lhs_eq, rhs_eq]
    congr 1
    · apply IH₂
    · apply IH₁
      have := hx₁.to_parent_isCoherent.get_lt (hVP₁.transfer ⟨⟨i, hi⟩, ⟨j, hj⟩⟩)
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hj'
      simp only [hp, Pairable₂.val_transfer, Index₂.val_mk_mk, Index₂.fst_val,
        ParentMountain.IsCoherent.indexParentOfIsSome_val, Option.get_some, gt_iff_lt] at this ⊢
      exact WithBot.coe_lt_coe.mp this
  · clear! j
    intro hj
    apply value_eq_where_parent_eq_none (hVP₁.transfer ⟨⟨i, hi⟩, ⟨l, hj⟩⟩)
    rw [hx₁.to_parent_isCoherent.get_eq_none_iff]
    simp only [← hl', Nat.pred_eq_sub_one, Pairable₂.val_transfer, Index₂.val_mk_mk]
    congr 1
    exact hVP₁.snd _

theorem Mountain.IsCrossCoherent.value_ne_one_where_parent_isSome {x : Mountain}
    (h : x.IsCrossCoherent) {q : Index₂ x.parents.val} (hq : q.get.isSome) :
    (x.pairable.symm.transfer q).get ≠ 1 :=
  by
  intro H
  have := h.value_above_lt_value_of_parent_isSome hq
  rw [H] at this
  exact PNat.not_lt_one _ this

theorem Mountain.IsCrossCoherent.parent_eq_none_where_value_eq_one {x : Mountain}
    (h : x.IsCrossCoherent) {q : Index₂ x.values.val} :
    q.get = 1 → (x.pairable.transfer q).get = none :=
  by
  rw [← Decidable.not_imp_not, ← Ne, Option.ne_none_iff_isSome]
  exact h.value_ne_one_where_parent_isSome

/-- 𝕄** = {x : Mountain // x.is_orphanless ∧ x.IsCoherent} -/
def Mountain.IsCoherent (x : Mountain) : Prop :=
  x.IsOrphanless ∧ x.IsCrossCoherent

lemma Mountain.IsCoherent.to_isOrphanless {x : Mountain} (h : x.IsCoherent) : x.IsOrphanless :=
  h.left

lemma Mountain.IsCoherent.to_isCrossCoherent {x : Mountain} (h : x.IsCoherent) :
    x.IsCrossCoherent :=
  h.right

end Types

section Build

structure RowBuilder (x : ValueParentListPair) : Type where
  value : Index x.values.val → Option ℕ+
  parent : Index x.values.val → Option ℕ
  toNoneOrLtId_parent : ToNoneOrLtId (inIndexElim parent none)
  parentAsIndex :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      { p : Index x.values.val // p.val = (parent i).get h }
  parent_spec :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      let p := (parentAsIndex h).val
      ∃ m ∈ value p, ∃ n ∈ value i, m < n
  value_isSome_of_parent_isSome : ∀ {i : Index x.values.val}, (parent i).isSome → (value i).isSome
  value_parent_isSome_of_parent_isSome :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      let p := (parentAsIndex h).val
      (value p).isSome

def buildRowBuilder (x : ValueParentListPair) (value : Index x.values.val → Option ℕ+)
    (parentCandidateNext : Index x.values.val → Option ℕ)
    (toNoneOrLtId_parentCandidateNext : ToNoneOrLtId (inIndexElim parentCandidateNext none)) :
    RowBuilder x :=
  let parent : Index x.values.val → Option ℕ := fun i =>
    findIterateOfToNoneOrLtId toNoneOrLtId_parentCandidateNext
      (fun p => Finset.decidableMem p <|
        (Finset.univ.filter fun p : Index x.values.val =>
          ∃ m ∈ value p, ∃ n ∈ value i, m < n).map ⟨Fin.val, Fin.val_injective⟩)
      i.val
  have toNoneOrLtId_parent : ToNoneOrLtId (inIndexElim parent none) :=
    by
    apply toNoneOrLtId_inIndexElim_val_none_of_forall_index
    intro
    apply toNoneOrLtId_findIterate_of_not_mem
    simp_all [Set.mem_def, Fin.val_inj]
  let parentAsIndex :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      { p : Index x.values.val // p.val = (parent i).get h } :=
    fun {i} h =>
    ⟨⟨(parent i).get h,
        by
        cases' i with i hi
        have parent_i := toNoneOrLtId_parent i
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
        rw [inIndexElim_of_lt _ _ hi] at parent_i
        simp_rw [hp] at parent_i ⊢
        exact lt_trans (WithBot.coe_lt_coe.mp parent_i) hi⟩,
      rfl⟩
  have parent_spec :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      let p := (parentAsIndex h).val
      ∃ m ∈ value p, ∃ n ∈ value i, m < n :=
    by
    intro i h
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
    rcases parentAsIndex h with ⟨⟨p, hp₁⟩, hp₂⟩
    simp only [hk, Option.get_some] at hp₂
    subst hp₂
    have spec : ∀ y ∈ parent i, _ := findIterate_spec _ _ _
    simp only [hk, Option.mem_def, Option.some.injEq, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and, Function.Embedding.coeFn_mk, forall_eq'] at spec
    rcases spec with ⟨⟨p', hp'₁⟩, hp'₂, hp'₃⟩
    subst hp'₃
    exact hp'₂
  have value_isSome_of_parent_isSome :
    ∀ {i : Index x.values.val}, (parent i).isSome → (value i).isSome :=
    by
    intro i h
    specialize parent_spec h
    rw [← Option.ne_none_iff_isSome]
    intro H
    simp [H] at parent_spec
  have value_parent_isSome_of_parent_isSome :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      let p := (parentAsIndex h).val
      (value p).isSome :=
    by
    intro _ h
    cases parent_spec h
    simp_all
  { value := value
    parent := parent
    toNoneOrLtId_parent := toNoneOrLtId_parent
    parentAsIndex := parentAsIndex
    parent_spec := parent_spec
    value_isSome_of_parent_isSome := value_isSome_of_parent_isSome
    value_parent_isSome_of_parent_isSome := value_parent_isSome_of_parent_isSome }

def mountainBuilder (x : ValueParentListPair) : ℕ → RowBuilder x
  | 0 =>
    buildRowBuilder x (some ∘ Index.get)
      (Index.get ∘ x.pairable.transfer) (toNoneOrLtId_parent_list_get x)
  | j + 1 =>
    let prev := mountainBuilder x j
    buildRowBuilder x
      (fun i =>
        if h : (prev.parent i).isSome then
          let p := prev.parentAsIndex h
          some <|
            (prev.value i).get (prev.value_isSome_of_parent_isSome (i := i) h) -
              (prev.value p).get (prev.value_parent_isSome_of_parent_isSome (i := i) h)
        else none)
      prev.parent prev.toNoneOrLtId_parent

def value (x : ValueParentListPair) (i : Index x.values.val) (j : ℕ) : Option ℕ+ :=
  (mountainBuilder x j).value i

def parent (x : ValueParentListPair) (i : Index x.values.val) (j : ℕ) : Option ℕ :=
  (mountainBuilder x j).parent i

theorem toNoneOrLtId_parent (x : ValueParentListPair) (j : ℕ) :
    ToNoneOrLtId (inIndexElim (parent x · j) none) :=
  (mountainBuilder x j).toNoneOrLtId_parent

def parentAsIndex {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ}
    (h : (parent x i j).isSome) :
    { p : Index x.values.val // p.val = (parent x i j).get h } :=
  (mountainBuilder x j).parentAsIndex h

theorem parent_spec {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ}
    (h : (parent x i j).isSome) :
    let p := (parentAsIndex h).val
    ∃ m ∈ value x p j, ∃ n ∈ value x i j, m < n :=
  (mountainBuilder x j).parent_spec h

theorem value_isSome_of_parent_isSome {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    (parent x i j).isSome → (value x i j).isSome :=
  (mountainBuilder x j).value_isSome_of_parent_isSome

theorem value_parent_isSome_of_parent_isSome {x : ValueParentListPair} {i : Index x.values.val}
    {j : ℕ} (h : (parent x i j).isSome) :
    let p := (parentAsIndex h).val
    (value x p j).isSome :=
  (mountainBuilder x j).value_parent_isSome_of_parent_isSome h

theorem value_parent_lt_value {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ}
    (h : (parent x i j).isSome) :
    let p := (parentAsIndex h).val
    (value x p j).get (value_parent_isSome_of_parent_isSome h) <
      (value x i j).get (value_isSome_of_parent_isSome h) :=
  by
  rcases parent_spec h with ⟨_, _, _, _⟩
  simp_all

theorem parent_of_value_eq_none {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    value x i j = none → parent x i j = none :=
  by
  iterate 2 rw [← Option.not_isSome_iff_eq_none]
  exact mt value_isSome_of_parent_isSome

@[simp]
theorem value_zero (x : ValueParentListPair) (i : Index x.values.val) : value x i 0 = some i.get :=
  rfl

@[simp]
theorem value_succ (x : ValueParentListPair) (i : Index x.values.val) (j : ℕ) :
    value x i (j + 1) =
      if h : (parent x i j).isSome then
        let p := (parentAsIndex h).val
        some <|
          (value x i j).get (value_isSome_of_parent_isSome h) -
            (value x p j).get (value_parent_isSome_of_parent_isSome h)
      else none :=
  rfl

@[simp]
theorem parent_zero (x : ValueParentListPair) (i : Index x.values.val) :
    parent x i 0 =
      findIterateOfToNoneOrLtId (f := inIndexElim (Index.get ∘ x.pairable.transfer) none)
        (by
          apply toNoneOrLtId_inIndexElim_val_none_of_forall_index
          intro
          rw [← Pairable.val_transfer x.pairable _]
          exact x.parents.property _)
        (fun p => Finset.decidableMem p <|
          (Finset.univ.filter fun p : Index x.values.val =>
            ∃ m ∈ value x p 0, ∃ n ∈ value x i 0, m < n).map ⟨Fin.val, Fin.val_injective⟩)
        i.val :=
  by
  rfl

@[simp]
theorem parent_succ (x : ValueParentListPair) (i : Index x.values.val) (j : ℕ) :
    haveI : DecidablePred fun m => ∃ n ∈ value x i (j + 1), m < n :=
      fun _ => Option.decidableExistsMem ..
    parent x i (j + 1) =
      findIterateOfToNoneOrLtId (f := inIndexElim (parent x · j) none)
        (toNoneOrLtId_parent x j)
        (fun p => Finset.decidableMem p <|
          (Finset.univ.filter fun p : Index x.values.val =>
              ∃ m ∈ value x p (j + 1), ∃ n ∈ value x i (j + 1), m < n)
            |>.map ⟨Fin.val, Fin.val_injective⟩)
        i.val :=
  rfl

theorem value_succ_isSome {x : ValueParentListPair} {i : Index x.values.val}
    {j : ℕ} : (value x i (j + 1)).isSome = (parent x i j).isSome :=
  by
  rw [value_succ]
  split_ifs <;> simp_all only [Option.isSome_some, Option.isSome_none]

theorem value_succ_eq_none_iff_parent_eq_none {x : ValueParentListPair} {i : Index x.values.val}
    {j : ℕ} : value x i (j + 1) = none ↔ parent x i j = none :=
  by
  rw [← Decidable.not_iff_not, ← Ne, Option.ne_none_iff_isSome, value_succ_isSome]
  exact Option.ne_none_iff_isSome.symm

theorem get_value_above_eq_of_parent_isSome {x : ValueParentListPair} {i : Index x.values.val}
    {j : ℕ} (h : (parent x i j).isSome) :
    ((value x i (j + 1)).get (value_succ_isSome.symm ▸ h)).val =
      let p := (parentAsIndex h).val
      ((value x i j).get (value_isSome_of_parent_isSome h)).val -
        ((value x p j).get (value_parent_isSome_of_parent_isSome h)).val :=
  by simp [h, value_parent_lt_value, PNat.sub_coe]

theorem value_above_lt_value_of_parent_isSome {x : ValueParentListPair} {i : Index x.values.val}
    {j : ℕ} (h : (parent x i j).isSome) :
    ((value x i (j + 1)).get (value_succ_isSome.symm ▸ h)).val <
      ((value x i j).get (value_isSome_of_parent_isSome h)).val :=
  by
  rw [get_value_above_eq_of_parent_isSome h]
  exact Nat.sub_lt (PNat.pos _) (PNat.pos _)

lemma exists_iterate_parent_list_get_eq_parent_zero {x : ValueParentListPair} (i : Index x.values.val) :
    ∃ (k : ℕ), ((flip bind (inIndexElim (Index.get ∘ x.pairable.transfer) none))^[k] <| some i.val) =
      parent x i 0 :=
  by exact ⟨_, rfl⟩

lemma exists_iterate_parent_eq_parent_succ {x : ValueParentListPair} (i : Index x.values.val)
    (j : ℕ) :
    ∃ (k : ℕ), ((flip bind (inIndexElim (parent x · j) none))^[k] <| some i.val) =
      parent x i (j + 1) :=
  by exact ⟨_, rfl⟩

theorem exists_iterate_parent_eq_parent_upwards {x : ValueParentListPair} (i : Index x.values.val)
    {j₁ j₂ : ℕ} (hj : j₁ ≤ j₂) :
    ∃ (k : ℕ), ((flip bind (inIndexElim (parent x · j₁) none))^[k] <| some i.val) =
      parent x i j₂ :=
  by
  induction j₂, hj using Nat.le_induction generalizing i with
  | base => exact ⟨1, inIndexElim_val ..⟩
  | succ j₂ _ IH =>
    refine exists_iterate_bind_inIndexElim_trans_of_iterateEventuallyNone rfl ?_ IH ?_
    · apply iterateEventuallyNone_of_toNoneOrLtId
      apply toNoneOrLtId_parent
    · apply exists_iterate_parent_eq_parent_succ

theorem exists_iterate_parent_list_get_eq_parent {x : ValueParentListPair} (i : Index x.values.val)
    (j : ℕ) :
    ∃ (k : ℕ), ((flip bind (inIndexElim (Index.get ∘ x.pairable.transfer) none))^[k] <| some i.val) =
      parent x i j :=
  by
  refine exists_iterate_bind_inIndexElim_trans_of_iterateEventuallyNone rfl ?_
    exists_iterate_parent_list_get_eq_parent_zero ?_
  · apply iterateEventuallyNone_of_toNoneOrLtId
    apply toNoneOrLtId_parent_list_get
  · exact exists_iterate_parent_eq_parent_upwards i (Nat.zero_le j)

def height_finite (x : ValueParentListPair) (i : Index x.values.val) :
    ∃ j : ℕ, value x i j = none :=
  by
  suffices ∀ r, (∃ j, WithBot.le.le (value x i j) r) → ∃ j, value x i j = none
    from this (value x i 0) ⟨0, le_rfl⟩
  refine'
    fun r => WithBot.instWellFoundedLT.induction
      (C := fun r => (∃ j, WithBot.le.le (value x i j) r) → ∃ j, value x i j = none) r _
  clear r
  intro r IH
  dsimp only [] at IH
  cases r with
  | bot => exact Exists.imp fun _ => WithBot.le_bot_iff.mp
  | coe r =>
    intro ⟨j, hj⟩
    refine IH (value x i (j + 1)) ?_ ⟨j + 1, le_rfl⟩
    have value_succ_eq := value_succ x i j
    split_ifs at value_succ_eq with h
    · have va_lt_vt := value_above_lt_value_of_parent_isSome h
      generalize_proofs hva₀ hvp₀ at va_lt_vt
      obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := Option.isSome_iff_exists.mp hvp₀
      obtain ⟨⟨va, va_pos⟩, hva⟩ := Option.isSome_iff_exists.mp hva₀
      simp only [WithBot.some_eq_coe, WithBot.coe_le_coe, value_succ, ↓reduceDIte, PNat.coe_lt_coe,
        WithBot.coe_lt_coe, gt_iff_lt, hvt, h] at hj va_lt_vt ⊢
      exact lt_of_lt_of_le ((PNat.mk_lt_mk ..).mpr va_lt_vt) hj
    · rw [value_succ_eq]
      apply WithBot.bot_lt_coe

def height (x : ValueParentListPair) (i : Index x.values.val) : ℕ :=
  Nat.find (height_finite x i)

theorem height_spec (x : ValueParentListPair) (i : Index x.values.val) :
    value x i (height x i) = none :=
  Nat.find_spec (height_finite x i)

theorem height_min {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    j < height x i → value x i j ≠ none :=
  Nat.find_min (height_finite x i)

theorem height_pos (x : ValueParentListPair) (i : Index x.values.val) : 0 < height x i :=
  by
  by_contra H
  rw [not_lt, nonpos_iff_eq_zero] at H
  have := height_spec x i
  rw [H] at this
  contradiction

theorem value_eq_none_of_height_le {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    height x i ≤ j → value x i j = none :=
  by
  revert j
  apply Nat.le_induction
  · apply height_spec
  · intro _ _ IH
    exact value_succ_eq_none_iff_parent_eq_none.mpr (parent_of_value_eq_none IH)

theorem value_isSome_of_lt_height {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    j < height x i → (value x i j).isSome :=
  Option.ne_none_iff_isSome.mp ∘ height_min

theorem value_isSome_iff_lt_height {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    (value x i j).isSome ↔ j < height x i :=
  ⟨by
    rw [← Decidable.not_imp_not, not_lt, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none]
    exact value_eq_none_of_height_le, value_isSome_of_lt_height⟩

theorem value_eq_none_iff_height_le {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    value x i j = none ↔ height x i ≤ j :=
  by
  rw [← Decidable.not_iff_not, ← Ne, Option.ne_none_iff_isSome, not_le]
  exact value_isSome_iff_lt_height

def buildMountain (x : ValueParentListPair) : Mountain :=
  by
  refine
    { values :=
      ⟨List.finRange x.values.val.length |>.map fun i =>
        List.finRange (height x i) |>.map fun j =>
          (value x i j.val).get (value_isSome_of_lt_height j.isLt), ?_⟩,
      parents :=
        ⟨List.finRange x.values.val.length |>.map fun i =>
          List.finRange (height x i) |>.map fun j => parent x i j.val, ?_⟩,
      pairable := by simp [Pairable₂, Pairable, Index.get, Pairable.transfer] }
  all_goals
    simp only [List.mem_map, List.mem_finRange, true_and, ne_eq, forall_exists_index,
      forall_apply_eq_imp_iff, List.map_eq_nil_iff, List.finRange_eq_nil]
    intro
    exact ne_of_gt (height_pos ..)

theorem mountain_length_eq (x : ValueParentListPair) :
    (buildMountain x).values.val.length = x.values.val.length :=
  by simp [buildMountain]

theorem mountain_height_eq (x : ValueParentListPair) (i : Index (buildMountain x).values.val) :
    i.get.length = height x (Pairable.transfer (mountain_length_eq x) i) :=
  by simp [Pairable.transfer, Index.get, buildMountain]

theorem mountain_height_eq' (x : ValueParentListPair) (i : Index x.values.val) :
    (Pairable.transfer (mountain_length_eq x).symm i).get.length = height x i :=
  by simp [mountain_height_eq, Pairable.transfer, buildMountain]

theorem mountain_value_at_index_eq_value (x : ValueParentListPair)
    (q : Index₂ (buildMountain x).values.val) :
    q.get = (value x (Pairable.transfer (mountain_length_eq x) q.fst) q.val.snd).get
      (by
        apply value_isSome_of_lt_height
        rw [← mountain_height_eq]
        exact q.val_snd_lt) :=
  by simp [Index₂.get, Index.get, buildMountain, Pairable.transfer]

theorem mountain_parent_at_index_eq_parent (x : ValueParentListPair)
    (q : Index₂ (buildMountain x).parents.val) :
    q.get =
      parent x
        (Pairable.transfer ((buildMountain x).pairable.fst.symm.trans (mountain_length_eq x)) q.fst)
        q.val.snd :=
  by simp [Index₂.get, Index.get, buildMountain, Pairable.transfer]

theorem mountain_parents_isCoherent (x : ValueParentListPair) :
    (buildMountain x).parents.IsCoherent :=
  by
  rintro ⟨i, j⟩
  dsimp
  refine' ⟨_, _, _⟩
  · rw [mountain_parent_at_index_eq_parent, ← value_succ_eq_none_iff_parent_eq_none,
      value_eq_none_iff_height_le]
    dsimp only [Pairable.transfer, Index₂.mk_val_snd]
    rw [Nat.le_add_one_iff]
    conv in height _ _ = j.val + 1 =>
      rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt (height_pos _ _))]
    have iheight :=
      Eq.trans ((buildMountain x).pairable.snd _).symm
        (mountain_height_eq _ ((buildMountain x).pairable.fst.symm.transfer i))
    dsimp only [Pairable.transfer, Fin.eta] at iheight
    rw [← iheight, eq_comm, add_left_inj, or_iff_right_iff_imp]
    intro h
    exact absurd j.isLt (not_lt_of_ge h)
  · refine' lt_of_eq_of_lt _ (toNoneOrLtId_parent x j.val i.val)
    symm
    rw [inIndexElim, dite_eq_iff', and_iff_left]
    · intro
      rw [mountain_parent_at_index_eq_parent]
      rfl
    · intro h
      refine' absurd (lt_of_lt_of_eq i.isLt _) h
      exact (buildMountain x).pairable.fst.symm.trans (mountain_length_eq x)
  · cases' h : Index₂.get _ with k
    · intros; simp_all
    · rw [mountain_parent_at_index_eq_parent] at h
      have parent_isSome := Option.isSome_iff_exists.mpr ⟨k, h⟩
      let q := parentAsIndex parent_isSome
      intro _ hp
      rw [Option.mem_def, Option.some_inj] at hp
      subst hp
      refine
        ⟨⟨Pairable.transfer ((mountain_length_eq x).symm.trans (buildMountain x).pairable.fst) q.val,
            ⟨j.val, ?_⟩⟩, ?_⟩
      · apply Eq.subst ((mountain_height_eq' x _).symm.trans ((buildMountain x).pairable.snd _))
        rw [← value_isSome_iff_lt_height]
        exact value_parent_isSome_of_parent_isSome parent_isSome
      · have hp := q.property
        simp only [h, Option.get_some] at hp
        exact Prod.ext hp rfl

theorem mountain_orphanless_isOrphanless {x : ValueParentListPair} (h : x.IsOrphanless) :
    (buildMountain x).IsOrphanless :=
  by
  rintro ⟨i, hi⟩
  simp only [mountain_value_at_index_eq_value, Pairable.transfer, Index₂.val_mk_mk, value_zero,
    Option.get_some, mountain_parent_at_index_eq_parent, parent_zero, findIterateOfToNoneOrLtId]
  intro value_gt_one
  rw [findIterate_isSome_iff]
  simp only [Option.mem_def, Option.some.injEq, exists_eq_left', Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.Embedding.coeFn_mk, Option.bind_eq_bind]
  let i_on_mv : Index _ := ⟨i, hi⟩
  let i_on_lv : Index _ := Pairable.transfer (mountain_length_eq x) i_on_mv
  change ∃ k hk p, _ < i_on_lv.get ∧ _ = Option.get _ hk
  change 1 < i_on_lv.get.val at value_gt_one
  have v_gt_one := value_gt_one
  generalize i_on_lv.get = v at v_gt_one ⊢
  induction i using Nat.strong_induction_on with | h i IH =>
  have i_has_parent_candidate := h _ value_gt_one
  let i_on_lp : Index _ := Pairable.transfer ((mountain_length_eq x).trans x.pairable) i_on_mv
  change i_on_lp.get.isSome at i_has_parent_candidate
  let p := i_on_lp.get.get i_has_parent_candidate
  have hp : some p = _ := Option.some_get i_has_parent_candidate
  have p_lt_i : p < i := WithBot.coe_lt_coe.mp <| lt_of_eq_of_lt hp <| x.parents.property i_on_lp
  have p_lt_length : p < x.values.val.length :=
    p_lt_i.trans (lt_of_lt_of_eq hi (mountain_length_eq x))
  let p_on_lv : Index _ := ⟨p, p_lt_length⟩
  by_cases h' : p_on_lv.get < v
  · use 1
    have :
        (flip Option.bind (inIndexElim (Index.get ∘ x.pairable.transfer) none))^[1] (some i) =
          i_on_lp.get :=
      by
      dsimp [flip]
      conv in i => change i_on_lv.val
      rw [inIndexElim_val]
      rfl
    simp_rw [this]
    exact ⟨h _ value_gt_one, p_on_lv, h', rfl⟩
  · specialize IH p p_lt_i (lt_of_lt_of_eq p_lt_length (mountain_length_eq x).symm)
    extract_lets p_on_mv p_on_lv at IH
    specialize IH <| lt_of_lt_of_le v_gt_one (not_lt.mp h')
    rcases IH with ⟨k, hk⟩
    use k + 1
    have :
        (flip Option.bind (inIndexElim (Index.get ∘ x.pairable.transfer) none))^[k + 1] (some i) =
          (flip Option.bind (inIndexElim (Index.get ∘ x.pairable.transfer) none))^[k] (some p) :=
      by
      dsimp [flip]
      congr
      conv in i => change i_on_lv.val
      rw [inIndexElim_val]
      exact hp.symm
    simp_rw [this]
    exact hk

theorem mountain_isCrossCoherent (x : ValueParentListPair) : (buildMountain x).IsCrossCoherent :=
  by
  use mountain_parents_isCoherent x
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ hq
  dsimp [Pairable₂.transfer, Pairable.transfer,
    ParentMountain.IsCoherent.indexAboveOfIsSome, ParentMountain.IsCoherent.indexParentOfIsSome]
  simp only [mountain_value_at_index_eq_value, mountain_parent_at_index_eq_parent,
    Pairable.transfer]
  dsimp
  generalize_proofs hi' _ _ _ _ hp₀ hj' _
  simp_rw [dite_cond_eq_true (eq_true hp₀)]
  rw [Option.get_some]
  conv in (⟨(parent x ⟨i, hi'⟩ j).get hp₀, hj'⟩ : Index _) =>
    rw [Fin.eq_of_val_eq (i := ⟨_, hj'⟩) (parentAsIndex hp₀).property.symm]
  rw [PNat.sub_coe]
  apply ite_cond_eq_true
  apply eq_true
  apply value_parent_lt_value

theorem mountain_orphanless_isCoherent {x : ValueParentListPair} (h : x.IsOrphanless) :
    (buildMountain x).IsCoherent :=
  ⟨mountain_orphanless_isOrphanless h, mountain_isCrossCoherent x⟩

theorem iterate_mountain_indexParentOfIsSome_map_val_snd_eq_of_isSome {x : ValueParentListPair}
    (q : Index₂ (buildMountain x).parents.val) (k : ℕ) h :
    (((flip bind (fun q =>
        if h : q.get.isSome then some ((mountain_parents_isCoherent x).indexParentOfIsSome h)
        else none))^[k] <| some q).map (·.val.snd)).get h =
      q.val.snd :=
  by
  rw [← Option.some_inj, Option.some_get]
  induction k with
  | zero => rfl
  | succ k IH =>
    rw [Option.isSome_map] at h
    have h' := iterate_bind_isSome_le (Nat.le_succ k) h
    specialize IH <| (Option.isSome_map ..).symm ▸ h'
    rw [Function.iterate_succ_apply'] at h ⊢
    set q' := _^[k] _
    rw [← Option.some_get h'] at h IH ⊢
    simp only [flip, Option.bind_eq_bind, Option.bind_some, Option.isSome_dite] at h
    simpa only [flip, Option.bind_eq_bind, Option.bind_some, Option.map_dif,
      (mountain_parents_isCoherent x).indexParentOfIsSome_val, dite_eq_ite,
      Option.ite_none_right_eq_some, h, true_and]

theorem iterate_mountain_indexParentOfIsSome_map_val_fst_eq_iterate_mountain_parent {x : ValueParentListPair}
    (q : Index₂ (buildMountain x).parents.val) (k : ℕ) :
    ((flip bind (fun q =>
        if h : q.get.isSome then some ((mountain_parents_isCoherent x).indexParentOfIsSome h)
        else none))^[k] <| some q).map (·.val.fst) =
      ((flip bind (inIndexElim (parent x · q.val.snd) none))^[k] <| some q.val.fst) :=
  by
  induction k with
  | zero => rfl
  | succ k IH =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← IH]
    set q' := _^[k] _
    by_cases h : q'.isSome
    · have := iterate_mountain_indexParentOfIsSome_map_val_snd_eq_of_isSome q k <|
        (Option.isSome_map ..).symm ▸ h
      rw [Option.get_map] at this
      change (q'.get h).val.snd = _ at this
      rw [← Option.some_get h]
      simp only [flip, Option.bind_eq_bind, Option.bind_some, Option.map_some]
      erw [inIndexElim_of_lt _ _ <| Nat.lt_of_lt_of_eq (q'.get h).val_fst_lt <|
          (buildMountain x).pairable.symm.fst.trans (mountain_length_eq x),
        ← this, ← mountain_parent_at_index_eq_parent x (q'.get h)]
      split_ifs with h'
      · rw [Option.map_some, (mountain_parents_isCoherent x).indexParentOfIsSome_val]
        exact Option.some_get _
      · symm
        exact Option.not_isSome_iff_eq_none.mp h'
    · rw [Option.not_isSome_iff_eq_none] at h
      rw [h]
      rfl

theorem exists_iterate_mountain_indexParentOfIsSome_map_val_fst_eq_mountain_parent_upwards
    {x : ValueParentListPair} (i : Index (buildMountain x).parents.val) {j₁ j₂ : Index i.get} :
    j₁ ≤ j₂ →
    ∃ (k : ℕ),
      ((flip bind (fun q : Index₂ (buildMountain x).parents.val =>
          if h : q.get.isSome then some ((mountain_parents_isCoherent x).indexParentOfIsSome h)
          else none))^[k] <| some ⟨i, j₁⟩).map (·.val.fst) =
        j₂.get :=
  by
  conv in _ = _ =>
    congr
    · rw [iterate_mountain_indexParentOfIsSome_map_val_fst_eq_iterate_mountain_parent]
    · change Index₂.get ⟨i, j₂⟩; rw [mountain_parent_at_index_eq_parent]
  exact exists_iterate_parent_eq_parent_upwards ⟨i.val,
    Nat.lt_of_lt_of_eq i.isLt <| (buildMountain x).pairable.symm.fst.trans (mountain_length_eq x)⟩

end Build

end Ysequence
