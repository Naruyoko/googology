import Googology.YSequence.Mountain

namespace Ysequence

section Diagonal

def surfaceAt {V : ValueMountain} (i : Index V.val) : ℕ+ :=
  Index₂.get ⟨i, Index.last (V.index_get_ne_nil i)⟩

theorem surfaceAt_lt_base_of_orphanless_of_ne_one {x : Mountain} (h_coherent : x.IsCoherent)
    {i : Index x.values.val} (h_surface : surfaceAt i ≠ 1) :
    surfaceAt i < Index₂.get ⟨i, ⟨0, List.length_pos_of_ne_nil (x.values.index_get_ne_nil _)⟩⟩ :=
  by
  have h_cross_coherent := h_coherent.to_isCrossCoherent
  apply h_cross_coherent.value_decrease_upwards
  simp only [Index.last]
  rw [(x.pairable.snd _).def, tsub_pos_iff_lt, ← Nat.succ_le_iff, Nat.two_le_iff]
  constructor
  · exact (ne_of_lt (List.length_pos_of_ne_nil (x.parents.index_get_ne_nil _))).symm
  · intro H
    have h :=
      h_cross_coherent.to_parent_isCoherent.get_eq_none_iff
        ⟨x.pairable.fst.transfer i, ⟨0, List.length_pos_of_ne_nil (x.parents.index_get_ne_nil _)⟩⟩
    conv at h in _ - 1 => simp only [H]
    simp at h
    have h' := h_coherent.to_isOrphanless i
    rw [← Decidable.not_imp_not, Option.not_isSome_iff_eq_none, not_lt] at h'
    specialize h' h
    erw [PNat.coe_le_coe _ 1, PNat.le_one_iff] at h'
    rw [surfaceAt] at h_surface
    conv at h_surface =>
      lhs
      congr
      congr
      rw [Index.last]
      congr
      rw [(x.pairable.snd _).def, H]
      simp
    contradiction

def descend {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) : Option (Index₂ P.val) :=
  if h : q.get.isSome then some (hP.indexParentOfIsSome h)
  else
    match q.snd with
    | ⟨0, _⟩ => none
    | ⟨j + 1, h⟩ => some ⟨q.fst, ⟨j, lt_trans (Nat.lt_succ_self j) h⟩⟩

theorem descend_eq_none_iff {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    descend hP q = none ↔ ¬q.get.isSome ∧ q.val.snd = 0 :=
  by
  rw [descend]
  split_ifs with h
  · simp [h]
  · rcases q with ⟨_, ⟨_ | _, _⟩⟩ <;> simp [h]

theorem descend_eq_none_iff' {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    descend hP q = none ↔ q.get = none ∧ q.val.snd = 0 := by
  rw [← Option.not_isSome_iff_eq_none (o := q.get)]; exact descend_eq_none_iff hP q

theorem descend_isSome_iff {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    (descend hP q).isSome ↔ q.get.isSome ∨ q.val.snd ≠ 0 :=
  by
  rw [descend]
  split_ifs with h
  · simp [h]
  · rcases q with ⟨_, ⟨_ | _, _⟩⟩ <;> simp [h]

theorem descend_lt_and_eq_or_eq_and_lt_of_it_isSome {P : ParentMountain} {hP : P.IsCoherent}
    {q : Index₂ P.val} (h : (descend hP q).isSome) :
    let i := q.val.fst
    let j := q.val.snd
    let q' := (descend hP q).get h
    let i' := q'.val.fst
    let j' := q'.val.snd
    i' < i ∧ j' = j ∨ i' = i ∧ j' < j :=
  by
  intro i j q' i' j'
  have q'_eq := Eq.refl q'
  conv_rhs at q'_eq => simp only [q', descend]
  split_ifs at q'_eq with hq
  · left
    rw [Option.get_some] at q'_eq
    have := (hP.indexParentOfIsSome hq).property
    simp only [← q'_eq, Prod.ext_iff, Index₂.fst_val, Index₂.snd_val] at this
    refine ⟨?_, this.right⟩
    unfold_let
    rw [this.left, ← WithBot.coe_lt_coe, ← WithBot.some_eq_coe, Option.some_get]
    exact hP.get_lt q
  · rcases q_eq : q with ⟨⟨i₁, hi⟩, ⟨j₁, hj⟩⟩
    obtain rfl : i = i₁ := congr_arg (·.val.fst) q_eq
    obtain rfl : j = j₁ := congr_arg (·.val.snd) q_eq
    conv_rhs at q'_eq =>
      congr
      rw [q_eq]
      dsimp
    cases hj : j <;> simp_rw [hj] at q'_eq
    case _ =>
      generalize_proofs at q'_eq
      contradiction
    case _ j =>
      right
      simp only [Option.get_some, Index₂.eq_iff_val_fst_eq_and_val_snd_eq] at q'_eq
      exact ⟨q'_eq.left, lt_of_eq_of_lt q'_eq.right (lt_add_one j)⟩

theorem descend_pairwise_le_of_it_isSome {P : ParentMountain} {hP : P.IsCoherent} {q : Index₂ P.val}
    (h : (descend hP q).isSome) :
    let i := q.val.fst
    let j := q.val.snd
    let q' := (descend hP q).get h
    let i' := q'.val.fst
    let j' := q'.val.snd
    i' ≤ i ∧ j' ≤ j :=
  by
  rcases descend_lt_and_eq_or_eq_and_lt_of_it_isSome h with (⟨h'₁, h'₂⟩ | ⟨h'₁, h'₂⟩)
  · exact ⟨le_of_lt h'₁, le_of_eq h'₂⟩
  · exact ⟨le_of_eq h'₁, le_of_lt h'₂⟩

theorem descend_pairwise_ne_of_it_isSome {P : ParentMountain} {hP : P.IsCoherent} {q : Index₂ P.val}
    (h : (descend hP q).isSome) : q ≠ (descend hP q).get h :=
  by
  intro H
  rcases descend_lt_and_eq_or_eq_and_lt_of_it_isSome h with (⟨h'₁, _h'₂⟩ | ⟨_h'₁, h'₂⟩)
  · exact absurd (congr_arg (·.val.fst) H.symm) (ne_of_lt h'₁)
  · exact absurd (congr_arg (·.val.snd) H.symm) (ne_of_lt h'₂)

theorem iterate_descend_pairwise_le_of_it_isSome {P : ParentMountain} {hP : P.IsCoherent}
    {q : Index₂ P.val} {k : ℕ} (h : ((flip bind (descend hP))^[k] <| some q).isSome) :
    let i := q.val.fst
    let j := q.val.snd
    let q' := Option.get _ h
    let i' := q'.val.fst
    let j' := q'.val.snd
    i' ≤ i ∧ j' ≤ j :=
  by
  induction' k with k IH
  · constructor <;> rfl
  · set p := (flip bind (descend hP))^[k] <| some q
    have : ((flip bind (descend hP))^[k + 1] <| some q) = p >>= descend hP :=
      by apply Function.iterate_succ_apply'
    conv in (_^[_] _) => rw [this]
    rw [this] at h
    have hp : p.isSome := by
      cases hp : p
      · rw [hp] at h; contradiction
      · trivial
    specialize IH hp
    have p_bind_eq : p >>= descend hP = descend hP (p.get hp) :=
      congrArg (· >>= _) <| Option.some_get hp |>.symm
    have hstep := descend_pairwise_le_of_it_isSome <| p_bind_eq ▸ h
    conv in (_ >>= _) => rw [p_bind_eq]
    exact ⟨le_trans hstep.left IH.left, le_trans hstep.right IH.right⟩

theorem iterate_descend_succ_ne_of_it_isSome {P : ParentMountain} {hP : P.IsCoherent}
    {q : Index₂ P.val} {k : ℕ} (h : ((flip bind (descend hP))^[k + 1] <| some q).isSome) :
    q ≠ Option.get _ h :=
  by
  set p := (flip bind (descend hP))^[k] <| some q
  have : ((flip bind (descend hP))^[k + 1] <| some q) = p >>= descend hP :=
    by apply Function.iterate_succ_apply'
  conv in (_^[_] _) => rw [this]
  rw [this] at h
  have hp : p.isSome := by
    cases hp : p
    · rw [hp] at h; contradiction
    · trivial
  have p_bind_eq : p >>= descend hP = descend hP (p.get hp) :=
    congrArg (· >>= _) <| Option.some_get hp |>.symm
  have hupto := iterate_descend_pairwise_le_of_it_isSome hp
  have hstep := descend_lt_and_eq_or_eq_and_lt_of_it_isSome <| p_bind_eq ▸ h
  rw [Index₂.ne_iff_val_fst_ne_or_val_snd_ne]
  cases hstep with
  | inl hstep => convert Or.inl <| ne_of_gt <| lt_of_lt_of_le hstep.left hupto.left
  | inr hstep => convert Or.inr <| ne_of_gt <| lt_of_lt_of_le hstep.right hupto.right

theorem descend_finite {P : ParentMountain} (hP : P.IsCoherent) :
    IterateEventuallyNone <| descend hP :=
  by
  let r := (WithBot.lt.lt on Option.map fun q : Index₂ P.val => q.val.fst + q.val.snd)
  have : IsWellFounded _ r := ⟨WellFounded.onFun wellFounded_lt⟩
  refine fun q => IsWellFounded.induction r q (fun q IH => ?_)
    (C := fun q => ∃ k, (flip bind (descend hP))^[k] q = none)
  cases' q with q
  · exact ⟨0, rfl⟩
  · cases' h : descend hP q with q'
    · exact ⟨1, h⟩
    · specialize IH (descend hP q) _
      · simp [r, h]
        have h' := descend_lt_and_eq_or_eq_and_lt_of_it_isSome (Option.isSome_iff_exists.mpr ⟨_, h⟩)
        simp_rw [← Index₂.snd_val] at h'
        simp [h] at h'
        rcases h' with h' | h'
        · exact Nat.add_lt_add_of_lt_of_le h'.left (le_of_eq h'.right)
        · exact Nat.add_lt_add_of_le_of_lt (le_of_eq h'.left) h'.right
      rcases IH with ⟨k, hk⟩
      exact ⟨k + 1, hk⟩

def descendToSurface {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    Option (Index P.val) :=
  Sigma.fst <$>
    findIterateOfIterateEventuallyNone
      (descend_finite hP)
      (fun p => Finset.decidableMem p <|
        Finset.univ.filter fun p : Index₂ P.val => p.get = none ∧ p.fst ≠ q.fst)
      q

theorem exists_iterate_descend_spec_of_descendToSurface_isSome {P : ParentMountain}
    (hP : P.IsCoherent) (q : Index₂ P.val) (h : (descendToSurface hP q).isSome) :
    ∃ (k : ℕ) (hk : ((flip bind (descend hP))^[k] <| some q).isSome),
      (Option.get _ hk).fst = (descendToSurface hP q).get h ∧
        (Option.get _ hk).get = none ∧ (Option.get _ hk).fst ≠ q.fst :=
  by
  obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.mp h
  have hi' := hi'
  simp [descendToSurface] at hi'
  rcases hi' with ⟨j', hi'j'⟩
  refine ⟨_, Option.isSome_iff_exists.mpr ⟨_, hi'j'⟩, ?_⟩
  have hi'j' := hi'j'
  dsimp [findIterateOfIterateEventuallyNone] at hi'j'
  conv in (occs := *) (_^[_] _) => erw [hi'j']
  dsimp
  clear hi'j'
  constructor
  · exact Option.eq_some_iff_get_eq.mp hi' |>.snd.symm
  · have := hi'j' ▸ findIterate_spec _ _ q
    simpa

theorem descendToSurface_to_none_or_lt_val_fst {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : WithBot.lt.lt ((descendToSurface hP q).map Fin.val) q.val.fst :=
  by
  cases h : descendToSurface hP q
  · exact WithBot.bot_lt_coe _
  · have h' := Option.isSome_iff_exists.mpr ⟨_, h⟩
    obtain ⟨k, hk₁, hk₂⟩ := exists_iterate_descend_spec_of_descendToSurface_isSome hP q h'
    rw [Option.eq_some_iff_get_eq.mp h |>.snd] at hk₂
    erw [Option.map_some', WithBot.coe_lt_coe, ← hk₂.left]
    have h'' := iterate_descend_pairwise_le_of_it_isSome hk₁
    exact lt_of_le_of_ne h''.left (Fin.val_ne_of_ne hk₂.right.right)

theorem descendToSurface_isSome_iff {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    (descendToSurface hP q).isSome ↔ 0 < q.val.snd ∨ q.get.isSome :=
  by
  rw [descendToSurface, Option.isSome_iff_exists]
  generalize_proofs descend_finite
  simp only [Option.map_eq_some, Sigma.exists, exists_and_right, exists_eq_right]
  rw [← Index₂.exists_iff (p := fun q' => _ = some q'), ← Option.isSome_iff_exists,
    findIterate_isSome_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk₁, hk₂⟩
    have k_ne_zero : k ≠ 0 := by
      intro H
      subst H
      simp [Set.mem_def] at hk₂
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero k_ne_zero
    clear k_ne_zero hk₂
    by_contra H
    rcases q with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    rw [Decidable.or_iff_not_and_not, Decidable.not_not] at H
    rcases H with ⟨H', H⟩
    simp only [not_lt, nonpos_iff_eq_zero] at H'
    subst H'
    induction k with
    | zero => simp [flip, descend, H] at hk₁
    | succ k IH =>
      rw [imp_false, Option.not_isSome_iff_eq_none] at IH
      rw [Function.iterate_succ_apply', IH] at hk₁
      contradiction
  · have descend_finite_on_q := descend_finite (some q)
    generalize k_def : Nat.find descend_finite_on_q = k
    obtain ⟨hk_eq, hk_lt⟩ := (Nat.find_eq_iff descend_finite_on_q).mp k_def
    have k_ne_zero : k ≠ 0 := by
      intro H
      subst H
      contradiction
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero k_ne_zero
    clear k_ne_zero
    intro h
    have last_isSome := Option.ne_none_iff_isSome.mp (hk_lt k (lt_add_one k))
    refine' ⟨k, last_isSome, _⟩
    rw [Set.mem_def]
    have last_pairwise_le := iterate_descend_pairwise_le_of_it_isSome last_isSome
    extract_lets i j r i' j' at last_pairwise_le
    have hr : _ = some r := Option.eq_some_iff_get_eq.mpr ⟨_, rfl⟩
    rw [Function.iterate_succ_apply', hr] at hk_eq
    dsimp [flip] at hk_eq
    rw [descend_eq_none_iff'] at hk_eq
    change r.get = none ∧ r.fst ≠ q.fst
    constructor
    · exact hk_eq.left
    · conv at last_pairwise_le =>
        rw [le_iff_lt_or_eq, or_and_right]
        right
        rw [le_iff_lt_or_eq, and_or_left]
      rcases last_pairwise_le with hij | hij | hij
      · exact Fin.ne_of_val_ne (ne_of_lt hij.left)
      · refine' absurd hk_eq.left ((not_congr (hP.get_eq_none_iff r)).mpr (ne_of_lt _))
        rw [Nat.lt_sub_iff_add_lt]
        refine' lt_of_lt_of_le (Nat.succ_lt_succ hij.right) (Nat.succ_le_of_lt _)
        rw [Fin.eq_of_val_eq hij.left]
        exact q.val_snd_lt
      · rw [← Index₂.eq_iff_val_fst_eq_and_val_snd_eq] at hij
        rw [hij] at hk_eq
        cases h with
        | inl h => exact absurd hk_eq.right (ne_of_lt h).symm
        | inr h => exact absurd hk_eq.left (Option.ne_none_iff_isSome.mpr h)

def diagonalPreparentOf {P : ParentMountain} (hP : P.IsCoherent) (i : Index P.val) :
    Option (Index P.val) :=
  descendToSurface hP ⟨i, Index.last (P.index_get_ne_nil i)⟩

theorem diagonalPreparentOf_isSome_iff {P : ParentMountain} (hP : P.IsCoherent) (i : Index P.val) :
    (diagonalPreparentOf hP i).isSome ↔ 1 < i.get.length :=
  by
  simp [diagonalPreparentOf, descendToSurface_isSome_iff]
  intro h
  exfalso
  rw [← Option.ne_none_iff_isSome] at h
  apply h
  simp [hP.get_eq_none_iff]

theorem to_none_or_lt_diagonal_preparent {P : ParentMountain} (hP : P.IsCoherent) :
    ToNoneOrLtId <| inIndexElim (Option.map Fin.val ∘ diagonalPreparentOf hP) none :=
  by
  apply toNoneOrLtId_inIndexElim_yes_none_of_forall_index
  intro q
  exact descendToSurface_to_none_or_lt_val_fst hP _

def diagonal {x : Mountain} (h_coherent : x.parents.IsCoherent) (h_orphanless : x.IsOrphanless) :
    ValueParentListPair
    where
  values :=
    ⟨surfaceAt <$> List.finRange x.values.val.length,
      by
      split_ifs with h
      simp only [Index.get, surfaceAt, List.map_eq_map, List.get_map]
      rw [List.map_eq_map, List.length_map, List.length_finRange] at h
      convert Mountain.head_value_eq_one_of_parents_isCoherent_of_isOrphanless_of_length_pos
        h_coherent h_orphanless h
      · rw [List.get_finRange]
      · simp only [Index.last, List.map_eq_map, List.get_finRange]
        have h' := x.pairable.symm.snd _ ▸ (h_coherent.head_length <| x.pairable.fst.def ▸ h)
        erw [h']⟩
  parents :=
    ⟨(Option.map Fin.val ∘ diagonalPreparentOf h_coherent) <$>
        List.finRange x.parents.val.length,
      by
      rintro ⟨_, _⟩
      simp [Index.get]
      exact toNoneOrLtId_inIndexElim_yes_none_forall_index_of _
        (to_none_or_lt_diagonal_preparent h_coherent) _⟩
  pairable := by simp [Pairable]; exact x.pairable.fst

theorem diagonal_length_eq {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) :
    (diagonal h_coherent h_orphanless).values.val.length = x.values.val.length :=
  by simp [diagonal]

@[simp]
theorem diagonal_value_at {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) (i : Index (diagonal h_coherent h_orphanless).values.val) :
    i.get = surfaceAt (Pairable.transfer (diagonal_length_eq _ _) i) := by
  simp [Pairable.transfer, Index.get, diagonal]

@[simp]
theorem diagonal_parent_at {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) (i : Index (diagonal h_coherent h_orphanless).parents.val) :
    i.get =
      Fin.val <$>
        diagonalPreparentOf h_coherent
          (Pairable.transfer
            ((diagonal h_coherent h_orphanless).pairable.symm
              |>.trans (diagonal_length_eq h_coherent h_orphanless)
              |>.trans x.pairable.fst)
            i) :=
  by simp [Pairable.transfer, Index.get, diagonal]

theorem diagonal_isOrphanless {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) : (diagonal h_coherent h_orphanless).IsOrphanless :=
  by
  intro i
  simp [Pairable.transfer]
  intro h
  rw [diagonalPreparentOf_isSome_iff, Nat.one_lt_iff_ne_zero_and_ne_one]
  constructor
  · exact Ne.symm <| ne_of_lt <| List.length_pos_of_ne_nil <| x.parents.index_get_ne_nil _
  · intro H
    rw [surfaceAt, Index.last] at h
    simp [(x.pairable.snd _).def, Pairable.transfer, H] at h
    replace h := h_orphanless _ h
    rw [← Option.ne_none_iff_isSome, Ne, h_coherent.get_eq_none_iff] at h
    simp [Pairable.transfer, H] at h

theorem diagonal_lt_base_of_orphanless_of_ne_one {x : Mountain} (h_coherent : x.IsCoherent)
    {i :
      Index
        (diagonal h_coherent.to_isCrossCoherent.to_parent_isCoherent
          h_coherent.to_isOrphanless).values.val}
    (h_surface : i.get ≠ 1) :
    i.get <
      Index₂.get
        ⟨Pairable.transfer (diagonal_length_eq _ _) i,
          ⟨0, List.length_pos_of_ne_nil (x.values.index_get_ne_nil _)⟩⟩ :=
  by
  rw [diagonal_value_at] at h_surface ⊢
  exact surfaceAt_lt_base_of_orphanless_of_ne_one h_coherent h_surface

section DiagonalRec

set_option linter.unusedVariables false
variable {C : Mountain → Sort _}
  (base : ∀ ⦃x : Mountain⦄ (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent),
    surfaceAt (Index.last ne_nil) = 1 → C x)
  (rec : ∀ ⦃x : Mountain⦄ (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent),
    surfaceAt (Index.last ne_nil) ≠ 1 →
    C (buildMountain
      (diagonal h_coherent.to_isCrossCoherent.to_parent_isCoherent h_coherent.to_isOrphanless)) →
    C x)
  {x : Mountain} (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent)
set_option linter.unusedVariables true

lemma buildMountain_diagonal_ne_nil_of_ne_nil {x : Mountain} (ne_nil : x.values.val ≠ [])
    (h_coherent : x.IsCoherent) :
      (buildMountain
          (diagonal h_coherent.to_isCrossCoherent.to_parent_isCoherent h_coherent.to_isOrphanless)
        |>.values.val) ≠ [] :=
  by
  apply (List.ne_nil_iff_of_length_eq _).mp ne_nil
  rw [mountain_length_eq, diagonal_length_eq]

def diagonalRec : C x :=
  @WellFounded.fix { x : Mountain // x.values.val ≠ [] } (fun ⟨x, _⟩ => x.IsCoherent → C x)
    (LT.lt on fun ⟨x, ne_nil⟩ =>
      Index₂.get
        (⟨Index.last ne_nil, ⟨0, List.length_pos_of_ne_nil (x.values.index_get_ne_nil _)⟩⟩ :
          Index₂ x.values.val))
    IsWellFounded.wf.onFun
    (by
      clear! x
      rintro ⟨x, ne_nil⟩ f h_coherent
      exact
        if h_surface : surfaceAt (Index.last ne_nil) = 1 then base ne_nil h_coherent h_surface
        else
          rec ne_nil h_coherent h_surface
            (f
              ⟨buildMountain
                  (diagonal h_coherent.to_isCrossCoherent.to_parent_isCoherent h_coherent.to_isOrphanless),
                buildMountain_diagonal_ne_nil_of_ne_nil ne_nil h_coherent⟩
              (by
                simp [Function.onFun, mountain_value_at_index_eq_value]
                exact surfaceAt_lt_base_of_orphanless_of_ne_one h_coherent h_surface)
              (mountain_orphanless_isCoherent (diagonal_isOrphanless _ _))))
    ⟨x, ne_nil⟩ h_coherent

theorem diagonalRec_of_surface_eq_one (h_surface : surfaceAt (Index.last ne_nil) = 1) :
    diagonalRec base rec ne_nil h_coherent = base ne_nil h_coherent h_surface :=
  by
  rw [diagonalRec, WellFounded.fix_eq]
  simp [h_surface]

theorem diagonalRec_of_surface_ne_one (h_surface : surfaceAt (Index.last ne_nil) ≠ 1) :
    diagonalRec base rec ne_nil h_coherent =
      rec ne_nil h_coherent h_surface (diagonalRec base rec
        (buildMountain_diagonal_ne_nil_of_ne_nil ne_nil h_coherent)
        (mountain_orphanless_isCoherent (diagonal_isOrphanless _ _))) :=
  by
  rw [diagonalRec, diagonalRec, WellFounded.fix_eq]
  simp [h_surface]

theorem diagonalRec_eq_dite :
    diagonalRec base rec ne_nil h_coherent =
      if h_surface : surfaceAt (Index.last ne_nil) = 1 then base ne_nil h_coherent h_surface
      else rec ne_nil h_coherent h_surface (diagonalRec base rec
        (buildMountain_diagonal_ne_nil_of_ne_nil ne_nil h_coherent)
        (mountain_orphanless_isCoherent (diagonal_isOrphanless _ _))) :=
  by
  symm
  rw [dite_eq_iff']
  constructor <;> intro h_surface <;> symm
  · apply diagonalRec_of_surface_eq_one
  · apply diagonalRec_of_surface_ne_one

end DiagonalRec

end Diagonal

section Badroot

def indexSecondFromTopOfLast {α : Type} {m : GenericMountain α} (ne_nil : m.val ≠ []) :
    Index₂ m.val :=
  ⟨Index.last ne_nil, ⟨(Index.last ne_nil).get.length - 2,
    Nat.sub_lt (List.length_pos_of_ne_nil (m.index_get_ne_nil _)) Nat.two_pos⟩⟩

@[simp]
lemma indexSecondFromTopOfLast_val {α : Type} {m : GenericMountain α} (ne_nil : m.val ≠ []) :
    (indexSecondFromTopOfLast ne_nil).val = (m.val.length - 1, (Index.last ne_nil).get.length - 2) :=
  rfl

lemma indexSecondFromTopOfLast_parents_val_get_isSome_of_last_height_ne_one {x : Mountain}
    (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent)
    (h_last_length : (x.pairable.fst.transfer (Index.last ne_nil)).get.length ≠ 1) :
    (indexSecondFromTopOfLast <| List.ne_nil_iff_of_length_eq x.pairable.fst |>.mp ne_nil).get.isSome :=
  by
  have h_parent_isCoherent := h_coherent.to_isCrossCoherent.to_parent_isCoherent
  rw [h_parent_isCoherent.get_isSome_iff]
  simp
  apply Nat.ne_of_lt
  apply Nat.sub_succ_lt_self
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  exact
    ⟨Ne.symm <| ne_of_lt <| List.length_pos_of_ne_nil <| x.parents.index_get_ne_nil _,
      x.pairable.fst.transfer_last _ ▸ h_last_length⟩

/-- `@badroot x _ _` contains (↓BadRoot(x),↓BadRootHeight(x)) -/
def badroot : ∀ {x : Mountain}, x.values.val ≠ [] → x.IsCoherent → Option (Index₂ x.values.val) :=
  diagonalRec (C := fun x => Option (Index₂ x.values.val))
    (fun x ne_nil h_coherent _ =>
      if h_last_length : (x.pairable.fst.transfer (Index.last ne_nil)).get.length = 1 then none
      else
        some <| x.pairable.symm.transfer <| Subtype.val <|
          h_coherent.to_isCrossCoherent.to_parent_isCoherent.indexParentOfIsSome <|
          indexSecondFromTopOfLast_parents_val_get_isSome_of_last_height_ne_one ne_nil h_coherent
            h_last_length)
    (fun x _ _ _ p => p.map fun p =>
      ⟨Pairable.transfer (mountain_length_eq .. |>.trans <| diagonal_length_eq ..) p.fst,
        Index.last (x.values.index_get_ne_nil _)⟩)

theorem badroot_of_last_height_eq_one {x : Mountain} (ne_nil : x.values.val ≠ [])
    (h_coherent : x.IsCoherent)
    (h_last_length : (x.pairable.fst.transfer (Index.last ne_nil)).get.length = 1) :
    badroot ne_nil h_coherent = none :=
  by
  rw [badroot, diagonalRec_eq_dite]
  split_ifs with h
  · rfl
  · exfalso
    apply h
    rw [surfaceAt]
    have h_last_length' := (x.pairable.snd _).def.trans h_last_length
    conv in Index.last _ =>
      rw [Index.last]
      congr
      rw [h_last_length']
    exact
      Mountain.base_value_eq_one_of_parents_isCoherent_of_isOrphanless_of_height_eq_one
        h_coherent.to_isCrossCoherent.to_parent_isCoherent h_coherent.to_isOrphanless
        h_last_length'

theorem badroot_of_last_height_ne_one_of_last_surface_eq_one {x : Mountain}
    (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent)
    (h_last_length : (x.pairable.fst.transfer (Index.last ne_nil)).get.length ≠ 1)
    (h_surface : surfaceAt (Index.last ne_nil) = 1) :
    badroot ne_nil h_coherent =
      (some <| x.pairable.symm.transfer <| Subtype.val <|
        h_coherent.to_isCrossCoherent.to_parent_isCoherent.indexParentOfIsSome <|
        indexSecondFromTopOfLast_parents_val_get_isSome_of_last_height_ne_one ne_nil h_coherent
          h_last_length) :=
  by rw [badroot, diagonalRec_eq_dite]; split_ifs; rfl

theorem badroot_of_last_surface_ne_one {x : Mountain} (ne_nil : x.values.val ≠ [])
    (h_coherent : x.IsCoherent) (h_surface : surfaceAt (Index.last ne_nil) ≠ 1) :
    badroot ne_nil h_coherent =
      (badroot
          (x := buildMountain
            (diagonal h_coherent.to_isCrossCoherent.to_parent_isCoherent
              h_coherent.to_isOrphanless))
          (buildMountain_diagonal_ne_nil_of_ne_nil ne_nil h_coherent)
          (mountain_orphanless_isCoherent (diagonal_isOrphanless _ _))
        |>.map fun p =>
          ⟨Pairable.transfer (mountain_length_eq .. |>.trans <| diagonal_length_eq ..) p.fst,
            Index.last (x.values.index_get_ne_nil _)⟩) :=
  by rw [badroot, diagonalRec_of_surface_ne_one (h_surface := h_surface)]; rfl

/-- 𝕄ᴸ = {x : Mountain // x.IsLimit} -/
def Mountain.IsLimit (x : Mountain) : Prop :=
  ∃ (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent), (badroot ne_nil h_coherent).isSome

lemma Mountain.IsLimit.to_values_val_ne_nil {x : Mountain} (h : x.IsLimit) : x.values.val ≠ [] :=
  h.fst

lemma Mountain.IsLimit.to_isCoherent {x : Mountain} (h : x.IsLimit) : x.IsCoherent :=
  h.snd.fst

lemma Mountain.IsLimit.badroot_isSome {x : Mountain} (h : x.IsLimit) :
    (badroot h.to_values_val_ne_nil h.to_isCoherent).isSome :=
  h.snd.snd

theorem Mountain.IsLimit.last_length_ne_one {x : Mountain} (h : x.IsLimit) :
  (x.pairable.fst.transfer (Index.last h.to_values_val_ne_nil)).get.length ≠ 1 :=
  fun H => absurd h.badroot_isSome <| Option.not_isSome_iff_eq_none.mpr <|
    badroot_of_last_height_eq_one h.to_values_val_ne_nil h.to_isCoherent H

theorem Mountain.IsLimit.iff_last_length_ne_one {x : Mountain} :
    x.IsLimit ↔
      ∃ (ne_nil : x.values.val ≠ []),
        x.IsCoherent ∧ (x.pairable.fst.transfer (Index.last ne_nil)).get.length ≠ 1 :=
  by
  constructor
  · exact fun h => ⟨h.to_values_val_ne_nil, ⟨h.to_isCoherent, h.last_length_ne_one⟩⟩
  · rintro ⟨ne_nil, ⟨h_coherent, h⟩⟩
    revert h
    refine diagonalRec ?base ?rec ne_nil h_coherent
        (C := fun x => ∀ (ne_nil : x.values.val ≠ []),
          (x.pairable.fst.transfer (Index.last ne_nil)).get.length ≠ 1 → x.IsLimit)
        ne_nil
      <;> clear! x <;> intro x _ h_coherent h_surface
    case base =>
      intro ne_nil h_last_length
      refine ⟨ne_nil, h_coherent, Option.isSome_iff_exists.mpr ⟨?_, ?proof⟩⟩
      case proof =>
        exact badroot_of_last_height_ne_one_of_last_surface_eq_one
          ne_nil h_coherent h_last_length h_surface
    case rec =>
      intro IH ne_nil _h_last_length
      refine ⟨ne_nil, h_coherent, ?_⟩
      rw [badroot_of_last_surface_ne_one ne_nil h_coherent h_surface, Option.isSome_map]
      generalize_proofs _ _ diagonal_ne_nil diagonal_isCoherent
      apply badroot_isSome
      apply IH diagonal_ne_nil
      intro H
      apply absurd <|
        Mountain.base_value_eq_one_of_parents_isCoherent_of_isOrphanless_of_height_eq_one
          diagonal_isCoherent.to_isCrossCoherent.to_parent_isCoherent
          diagonal_isCoherent.to_isOrphanless
          (((Mountain.pairable _).snd _).def.trans H)
      simpa only [mountain_value_at_index_eq_value, Pairable.transfer_last, Index₂.mk_val_snd,
        value_zero, diagonal_value_at]

/-- `@cutChild x _` contains CutHeight(x) -/
def cutChild {V : ValueMountain} (ne_nil : V.val ≠ []) : Index (Index.last ne_nil).get :=
  if surfaceAt (Index.last ne_nil) = 1
  then
    ⟨(Index.last ne_nil).get.length - 2,
      Nat.sub_lt (List.length_pos_of_ne_nil (V.index_get_ne_nil _)) Nat.two_pos⟩
  else Index.last (V.index_get_ne_nil _)

/-- `@cutChild x _` contains CutHeight(x) -/
def cutChild.val_eq {V : ValueMountain} (ne_nil : V.val ≠ []) :
    (cutChild ne_nil).val =
      if surfaceAt (Index.last ne_nil) = 1
      then (Index.last ne_nil).get.length - 2
      else (Index.last ne_nil).get.length - 1 :=
  by unfold cutChild ; split_ifs <;> rfl

end Badroot

end Ysequence
