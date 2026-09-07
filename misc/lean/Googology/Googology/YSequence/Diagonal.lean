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
    simp only [Index₂.mk_val_snd, tsub_self, iff_true] at h
    have h' := h_coherent.to_isOrphanless i
    rw [← Decidable.not_imp_not, Option.not_isSome_iff_eq_none, not_lt] at h'
    specialize h' h
    erw [PNat.coe_le_coe _ 1, le_one_iff_eq_one] at h'
    simp_rw [surfaceAt, Index.last, (x.pairable.snd _).def, H] at h_surface
    contradiction

theorem surfaceAt_eq_one_of_height_eq_one {x : Mountain} (h_coherent : x.IsCoherent)
    {i : Index x.values.val} (h_height : (x.pairable.fst.transfer i).get.length = 1) :
    surfaceAt i = 1 :=
  by
  rw [surfaceAt]
  have h_height' := (x.pairable.snd _).def.trans h_height
  conv in Index.last _ =>
    rw [Index.last]
    congr
    rw [h_height']
  exact
    Mountain.base_value_eq_one_of_parents_isCoherent_of_isOrphanless_of_height_eq_one
      h_coherent.to_isCrossCoherent.to_parent_isCoherent h_coherent.to_isOrphanless
      h_height'

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
    descend hP q = none ↔ q.get = none ∧ q.val.snd = 0 :=
  by
  rw [← Option.not_isSome_iff_eq_none (o := q.get)]
  exact descend_eq_none_iff hP q

theorem descend_isSome_iff {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    (descend hP q).isSome ↔ q.get.isSome ∨ q.val.snd ≠ 0 :=
  by
  rw [descend]
  split_ifs with h
  · simp [h]
  · rcases q with ⟨_, ⟨_ | _, _⟩⟩ <;> simp [h]; sorry --Something weird

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
    have := hP.indexParentOfIsSome_val hq
    simp only [← q'_eq, Prod.ext_iff] at this
    refine ⟨?_, this.right⟩
    unfold i i'
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
      simp only [Index₂.eq_iff_val_fst_eq_and_val_snd_eq] at q'_eq
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
  induction k with
  | zero => constructor <;> rfl
  | succ k IH =>
    set p := (flip bind (descend hP))^[k] <| some q
    have : ((flip bind (descend hP))^[k + 1] <| some q) = p >>= descend hP :=
      by apply Function.iterate_succ_apply'
    sorry
    /-
    conv in (_^[_] _) => rw [this]
    rw [this] at h
    have hp : p.isSome :=
      by
      cases hp : p
      · rw [hp] at h; contradiction
      · trivial
    specialize IH hp
    have p_bind_eq : p >>= descend hP = descend hP (p.get hp) :=
      congrArg (· >>= _) <| Option.some_get hp |>.symm
    have hstep := descend_pairwise_le_of_it_isSome <| p_bind_eq ▸ h
    conv in (_ >>= _) => rw [p_bind_eq]
    exact ⟨le_trans hstep.left IH.left, le_trans hstep.right IH.right⟩
    -/

theorem iterate_descend_succ_ne_of_it_isSome {P : ParentMountain} {hP : P.IsCoherent}
    {q : Index₂ P.val} {k : ℕ} (h : ((flip bind (descend hP))^[k + 1] <| some q).isSome) :
    q ≠ Option.get _ h :=
  by
  set p := (flip bind (descend hP))^[k] <| some q
  have : ((flip bind (descend hP))^[k + 1] <| some q) = p >>= descend hP :=
    by apply Function.iterate_succ_apply'
  conv in (_^[_] _) => rw [this]
  rw [this] at h
  have hp : p.isSome :=
    by
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

open scoped Function in
theorem descend_finite {P : ParentMountain} (hP : P.IsCoherent) :
    IterateEventuallyNone <| descend hP :=
  by
  let r := (WithBot.instLT.lt on Option.map fun q : Index₂ P.val => q.val.fst + q.val.snd)
  have : IsWellFounded _ r := ⟨WellFounded.onFun wellFounded_lt⟩
  refine fun q => IsWellFounded.induction r q (fun q IH => ?_)
    (motive := fun q => ∃ k, (flip bind (descend hP))^[k] q = none)
  cases q with
  | none => exact ⟨0, rfl⟩
  | some q =>
    cases h : descend hP q with
    | none => exact ⟨1, h⟩
    | some q' =>
      specialize IH (descend hP q) _
      · sorry
        /-
        simp only [h, gt_iff_lt, Option.map_some, r]
        simp only [WithBot.some_eq_coe, WithBot.coe_lt_coe]
        have h' := descend_lt_and_eq_or_eq_and_lt_of_it_isSome (Option.isSome_iff_exists.mpr ⟨_, h⟩)
        simp_rw [← Index₂.snd_val] at h'
        simp only [h, Option.get_some, Index₂.snd_val, r] at h'
        rcases h' with h' | h'
        · exact Nat.add_lt_add_of_lt_of_le h'.left (le_of_eq h'.right)
        · exact Nat.add_lt_add_of_le_of_lt (le_of_eq h'.left) h'.right
        -/
      rcases IH with ⟨k, hk⟩
      exact ⟨k + 1, hk⟩

def descendToSurface {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    Option (Index₂ P.val) :=
  findIterateOfIterateEventuallyNone
    (descend_finite hP)
    (fun p : Index₂ P.val => p.get = none ∧ p.fst ≠ q.fst)
    q

theorem descendToSurface_eq_fst_last {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val)
    (h : (descendToSurface hP q).isSome) :
    (descendToSurface hP q).get h =
      ⟨((descendToSurface hP q).get h).fst, Index.last (P.index_get_ne_nil _)⟩ :=
  by
  ext
  · rfl
  · rw [Index₂.mk_val_snd, Index.last_val, ← hP.get_eq_none_iff]
    have :=
      findIndexIterate_spec
        (descend_finite hP)
        (fun p : Index₂ P.val => p.get = none ∧ p.fst ≠ q.fst)
        q
    exact Option.all_eq_true_iff_get .. |>.mp this _ |> of_decide_eq_true |>.left

theorem exists_iterate_descend_spec_of_descendToSurface_isSome {P : ParentMountain}
    (hP : P.IsCoherent) (q : Index₂ P.val) (h : (descendToSurface hP q).isSome) :
    ∃ (k : ℕ) (hk : ((flip bind (descend hP))^[k] <| some q).isSome),
      Option.get _ hk = (descendToSurface hP q).get h ∧
        (Option.get _ hk).get = none ∧ (Option.get _ hk).fst ≠ q.fst :=
  by
  refine ⟨_, h, ⟨rfl, ?_⟩⟩
  have :=
    findIndexIterate_spec
      (descend_finite hP)
      (fun p : Index₂ P.val => p.get = none ∧ p.fst ≠ q.fst)
      q
  exact Option.all_eq_true_iff_get .. |>.mp this _ |> of_decide_eq_true

theorem descendToSurface_to_none_or_lt_val_fst {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : WithBot.instLT.lt ((descendToSurface hP q).map (·.val.fst)) q.val.fst :=
  by
  cases h : descendToSurface hP q
  · exact WithBot.bot_lt_coe _
  · have h' := Option.isSome_iff_exists.mpr ⟨_, h⟩
    obtain ⟨k, hk₁, hk₂⟩ := exists_iterate_descend_spec_of_descendToSurface_isSome hP q h'
    rw [Option.eq_some_iff_get_eq.mp h |>.snd] at hk₂
    erw [Option.map_some, WithBot.coe_lt_coe, ← hk₂.left]
    have h'' := iterate_descend_pairwise_le_of_it_isSome hk₁
    exact lt_of_le_of_ne h''.left (Fin.val_ne_of_ne hk₂.right.right)

theorem descendToSurface_isSome_iff {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    (descendToSurface hP q).isSome ↔ 0 < q.val.snd ∨ q.get.isSome :=
  by
  rw [descendToSurface, findIterate_isSome_iff]
  constructor
  · rintro ⟨k, hk₁, hk₂⟩
    have k_ne_zero : k ≠ 0 :=
      by
      intro H
      simp [H] at hk₂
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero k_ne_zero
    clear hk₂
    revert hk₁
    rw [← Option.ne_none_iff_isSome, ← Option.ne_none_iff_isSome, Nat.pos_iff_ne_zero, ← Decidable.not_and_iff_or_not]
    apply mt
    intro H
    apply iterate_bind_eq_none_ge <| Nat.succ_le_succ <| Nat.zero_le k
    simp only [Option.bind_eq_bind, Nat.succ_eq_add_one, Function.iterate_succ_apply,
      Function.iterate_zero_apply, flip, descend, Option.bind_some, H, Option.isSome_none,
      Bool.false_eq_true, ↓reduceDIte]
    rw [← Index₂.snd_val] at H
    split <;> simp_all
  · have descend_finite_on_q := descend_finite hP (some q)
    generalize k_def : Nat.find descend_finite_on_q = k
    obtain ⟨hk_eq, hk_lt⟩ := (Nat.find_eq_iff descend_finite_on_q).mp k_def
    have k_ne_zero : k ≠ 0 :=
      by
      intro H
      subst H
      contradiction
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero k_ne_zero
    clear k_ne_zero
    intro h
    have last_isSome := Option.ne_none_iff_isSome.mp (hk_lt k (Nat.lt_succ_self k))
    refine ⟨k, last_isSome, ?_⟩
    have last_pairwise_le := iterate_descend_pairwise_le_of_it_isSome last_isSome
    extract_lets i j r i' j' at last_pairwise_le
    have hr : _ = some r := Option.eq_some_iff_get_eq.mpr ⟨_, rfl⟩
    rw [Function.iterate_succ_apply', hr] at hk_eq
    dsimp [flip] at hk_eq
    rw [descend_eq_none_iff'] at hk_eq
    apply decide_eq_true
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

theorem exists_iterate_parent_eq_descendToSurface_from_result_height_of_isSome
    {x : ValueParentListPair} (q : Index₂ (buildMountain x).parents.val)
    (h : (descendToSurface (mountain_parents_isCoherent x) q).isSome) :
    ∃ (k : ℕ),
      (Option.get _ h).val.fst ∈
        ((flip bind (inIndexElim (parent x · (Option.get _ h).val.snd) none))^[k] <|
          some q.val.fst) :=
  by
  unfold descendToSurface findIterateOfIterateEventuallyNone at *
  generalize findIndexIterateOfIterateEventuallyNone .. = k at *
  suffices ∀ j ≤ _, ∃ k, (flip bind (inIndexElim (parent x · j) none))^[k] _ = _
    from this _ (Nat.le_refl _)
  induction k with
  | zero => intros; exact ⟨0, rfl⟩
  | succ k IH =>
    intro j hj
    have h' := iterate_bind_isSome_le (Nat.le_succ k) h
    specialize IH h' j (Nat.le_trans hj _)
    · conv in _^[_] _ => rw [Function.iterate_succ_apply', ← Option.some_get h']
      exact (descend_pairwise_le_of_it_isSome _).right
    rcases IH with ⟨k₁, hk₁⟩
    refine Exists.casesOn ?_ fun k' hk' => ⟨k' + k₁, hk'⟩
    conv in _ = _ => rw [Function.iterate_add_apply, hk₁]
    have t_eq := Eq.refl <| (flip bind (descend (mountain_parents_isCoherent x)))^[k + 1] <| some q
    conv_rhs at t_eq =>
      rw [Function.iterate_succ_apply', ← Option.some_get h']
      conv in bind => rw [Option.bind_eq_bind]
      rw [flip, Option.bind_some]
      conv in (occs := 1) descend => unfold descend
    split_ifs at t_eq
    · simp only [t_eq, Option.get_some,
        (mountain_parents_isCoherent x).indexParentOfIsSome_val,
        mountain_parent_at_index_eq_parent, Option.some_get]
      convert exists_iterate_parent_eq_parent_upwards _ _; · rfl
      refine Nat.le_trans hj ?_
      conv in _^[_] _ => rw [Function.iterate_succ_apply', ← Option.some_get h']
      exact (descend_pairwise_le_of_it_isSome _).right
    · split at t_eq
      · rw [t_eq] at h
        contradiction
      · use 0
        simp only [t_eq]
        rfl

theorem exists_iterate_mountain_indexParentOfIsSome_eq_descendToSurface_from_result_height_of_isSome
    {x : ValueParentListPair} (q : Index₂ (buildMountain x).parents.val)
    (h : (descendToSurface (mountain_parents_isCoherent x) q).isSome) :
    let q' : Index₂ _ :=
      ⟨q.fst, ⟨(Option.get _ h).val.snd,
        lt_of_le_of_lt (iterate_descend_pairwise_le_of_it_isSome h).right q.val_snd_lt⟩⟩
    ∃ (k : ℕ),
      Option.get _ h ∈
        ((flip bind (fun q =>
          if h : q.get.isSome then some ((mountain_parents_isCoherent x).indexParentOfIsSome h)
          else none))^[k] <| some q') :=
  by
  intro q'
  have ⟨k', hk'⟩ :=
    exists_iterate_parent_eq_descendToSurface_from_result_height_of_isSome _ h
  use k'
  rw [Option.mem_def, Option.eq_some_iff_get_eq]
  refine have h' := ?_; ⟨h', ?_⟩
  · rw [← Option.isSome_map (f := (·.val.fst)),
      iterate_mountain_indexParentOfIsSome_map_val_fst_eq_iterate_mountain_parent,
      Option.isSome_iff_exists]
    exact ⟨_, hk'⟩
  · rw [Index₂.eq_iff_val_fst_eq_and_val_snd_eq,
      ← Option.get_map (f := (·.val.fst)) (h := (Option.isSome_map ..).trans h'),
      ← Option.get_map (f := (·.val.snd)) (h := (Option.isSome_map ..).trans h'),
      iterate_mountain_indexParentOfIsSome_map_val_snd_eq_of_isSome]
    simp only [iterate_mountain_indexParentOfIsSome_map_val_fst_eq_iterate_mountain_parent]
    exact ⟨Option.get_of_mem _ hk', rfl⟩

theorem exists_iterate_parent_list_get_eq_descendToSurface_from_result_height_of_isSome
    {x : ValueParentListPair} (q : Index₂ (buildMountain x).parents.val) :
    ∃ (k : ℕ),
      ((flip bind (inIndexElim (Index.get ∘ x.pairable.transfer) none))^[k] <| some q.val.fst) =
        (descendToSurface (mountain_parents_isCoherent x) q).map (·.val.fst) :=
  by
  have he : IterateEventuallyNone (inIndexElim (Index.get ∘ x.pairable.transfer) none) :=
    by
    apply iterateEventuallyNone_of_toNoneOrLtId
    apply toNoneOrLtId_parent_list_get
  by_cases h : (descendToSurface (mountain_parents_isCoherent x) q).isSome
  · rw [← Option.some_get h, Option.map_some]
    exact exists_iterate_bind_inIndexElim_trans_of_iterateEventuallyNone rfl he
      (exists_iterate_parent_list_get_eq_parent · _)
      (exists_iterate_parent_eq_descendToSurface_from_result_height_of_isSome q h)
  · rw [Option.not_isSome_iff_eq_none] at h
    rw [h, Option.map_none]
    exact he _

def diagonalPreparentOf {P : ParentMountain} (hP : P.IsCoherent) (i : Index P.val) :
    Option (Index₂ P.val) :=
  descendToSurface hP ⟨i, Index.last (P.index_get_ne_nil i)⟩

theorem diagonalPreparentOf_isSome_iff {P : ParentMountain} (hP : P.IsCoherent) (i : Index P.val) :
    (diagonalPreparentOf hP i).isSome ↔ 1 < i.get.length :=
  by
  simp only [diagonalPreparentOf, descendToSurface_isSome_iff _ ⟨_, _⟩, Index₂.mk_val_snd,
    Index.last_val, tsub_pos_iff_lt, or_iff_left_iff_imp]
  intro h
  exfalso
  rw [← Option.ne_none_iff_isSome] at h
  apply h
  simp [hP.get_eq_none_iff ⟨_, _⟩]

theorem iterate_bind_diagonalPreparentOf_eq_iterate_bind_descendToSurface_last_get_map_fst
    {P : ParentMountain} (hP : P.IsCoherent) (i : Index P.val) (k : ℕ) :
    ((flip bind (Option.map Sigma.fst ∘ diagonalPreparentOf hP))^[k] <| some i) =
      ((flip bind (descendToSurface hP))^[k] <| some ⟨i, Index.last (P.index_get_ne_nil i)⟩).map
        Sigma.fst :=
  by
  induction k with
  | zero => rfl
  | succ k IH =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', IH]
    cases h : _^[_] _ with
    | none => rfl
    | some q =>
      sorry
      /-
      simp only [flip, Option.map_some, Option.bind_eq_bind, Function.comp_apply,
        diagonalPreparentOf, Option.bind_some]
      congr
      cases k with
      | zero =>
        simp only [Function.iterate_zero_apply, Option.some_inj] at h
        apply eq_of_heq
        rw [Sigma.ext_iff] at h
        dsimp at h
        convert h.right <;> simp_all
      | succ _ =>
        have := iterate_bind_isSome_le (Nat.le_succ _) <| Option.isSome_iff_exists.mpr ⟨_, h⟩
        rw [Function.iterate_succ_apply', ← Option.some_get this] at h
        simp only [flip, Option.bind_eq_bind, Option.bind_some] at h
        obtain ⟨h', h''⟩ := Option.eq_some_iff_get_eq.mp h
        have : q = ⟨q.fst, Index.last (P.index_get_ne_nil _)⟩ :=
          h'' ▸ descendToSurface_eq_fst_last _ _ h'
        exact Sigma.ext_iff.mp this |>.right.symm |> eq_of_heq
      -/

theorem toNoneOrLtId_diagonalPreparentOf {P : ParentMountain} (hP : P.IsCoherent) :
    ToNoneOrLtId <| inIndexElim (Option.map (·.val.fst) ∘ diagonalPreparentOf hP) none :=
  by
  apply toNoneOrLtId_inIndexElim_val_none_of_forall_index
  intro q
  exact descendToSurface_to_none_or_lt_val_fst hP _

def diagonal {x : Mountain} (h_coherent : x.parents.IsCoherent) (h_orphanless : x.IsOrphanless) :
    ValueParentListPair
    where
  values :=
    ⟨surfaceAt <$> List.finRange x.values.val.length,
      by
      split_ifs with h
      simp_rw [Index.get, List.map_eq_map, List.get_eq_getElem, List.getElem_map, surfaceAt]
      rw [List.map_eq_map, List.length_map, List.length_finRange] at h
      convert Mountain.head_value_eq_one_of_parents_isCoherent_of_isOrphanless_of_length_pos
        h_coherent h_orphanless h
      sorry
      /-
      · rw [List.getElem_finRange]
        rfl
      · rw [Index.last_val, List.getElem_finRange, Fin.cast_mk, (x.pairable.snd _).def]
        exact Nat.sub_eq_of_eq_add <| h_coherent.head_length <| x.pairable.fst.def ▸ h
      -/⟩
  parents :=
    ⟨(Option.map (·.val.fst) ∘ diagonalPreparentOf h_coherent) <$>
        List.finRange x.parents.val.length,
      by
      rintro ⟨_, _⟩
      simp only [Index.get, List.map_eq_map, List.get_eq_getElem, List.getElem_map,
        List.getElem_finRange, Fin.cast_mk, Function.comp_apply]
      exact toNoneOrLtId_inIndexElim_val_none_forall_index_of _
        (toNoneOrLtId_diagonalPreparentOf h_coherent) _⟩
  pairable :=
    by
    simp only [Pairable, List.map_eq_map, List.length_map, List.length_finRange]
    exact x.pairable.fst

theorem diagonal_length_eq {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) :
    (diagonal h_coherent h_orphanless).values.val.length = x.values.val.length :=
  by simp [diagonal]

@[simp]
theorem diagonal_value_at {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) (i : Index (diagonal h_coherent h_orphanless).values.val) :
    i.get = surfaceAt (Pairable.transfer (diagonal_length_eq _ _) i) :=
  by sorry /- simp [Pairable.transfer, Index.get, diagonal] -/

@[simp]
theorem diagonal_parent_at {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) (i : Index (diagonal h_coherent h_orphanless).parents.val) :
    i.get =
      (·.val.fst) <$>
        diagonalPreparentOf h_coherent
          (Pairable.transfer
            ((diagonal h_coherent h_orphanless).pairable.symm
              |>.trans (diagonal_length_eq h_coherent h_orphanless)
              |>.trans x.pairable.fst)
            i) :=
  by sorry /- simp [Pairable.transfer, Index.get, diagonal] -/

theorem diagonal_isOrphanless {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) : (diagonal h_coherent h_orphanless).IsOrphanless :=
  by
  intro i
  simp only [diagonal_value_at, Pairable.transfer, diagonal_parent_at, Option.map_eq_map,
    Option.isSome_map]
  intro h
  rw [diagonalPreparentOf_isSome_iff, Nat.one_lt_iff_ne_zero_and_ne_one]
  constructor
  · exact Ne.symm <| ne_of_lt <| List.length_pos_of_ne_nil <| x.parents.index_get_ne_nil _
  · intro H
    rw [surfaceAt, Index.last] at h
    simp only [(x.pairable.snd _).def, Pairable.transfer, H, tsub_self] at h
    replace h := h_orphanless _ h
    rw [← Option.ne_none_iff_isSome, Ne, h_coherent.get_eq_none_iff ⟨_, _⟩] at h
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

theorem iterate_bind_diagonal_parent_get_eq_iterate_bind_diagonalPreparentOf
    {x : Mountain} (h_coherent : x.parents.IsCoherent) (h_orphanless : x.IsOrphanless)
    (i : Index x.parents.val) (k : ℕ) :
    ((flip bind (inIndexElim
          (Index.get ∘ (diagonal h_coherent h_orphanless).pairable.transfer) none))^[k] <|
        some i.val) =
      ((flip bind (Option.map Sigma.fst ∘ diagonalPreparentOf h_coherent))^[k] <| some i).map Fin.val :=
  by
  induction k with
  | zero => rfl
  | succ k IH =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', IH]
    cases _^[_] _ with
    | none => rfl
    | some q =>
      sorry
      /-
      simp only [flip, Option.map_some, Option.bind_eq_bind, Option.bind_some, Function.comp_apply,
        Option.map_map]
      rw [inIndexElim_of_lt _ _ <| Nat.lt_of_lt_of_eq q.isLt <|
          Eq.symm <| diagonal_length_eq .. |>.trans x.pairable.fst,
        Function.comp_apply, diagonal_parent_at]
      rfl
      -/

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

open scoped Function in
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
                  (diagonal
                    h_coherent.to_isCrossCoherent.to_parent_isCoherent
                    h_coherent.to_isOrphanless),
                buildMountain_diagonal_ne_nil_of_ne_nil ne_nil h_coherent⟩
              (by
                sorry
                /-
                simp only [Function.onFun, mountain_value_at_index_eq_value, Pairable.transfer_last,
                  Index₂.mk_val_snd, value_zero, diagonal_value_at, Option.get_some]
                exact surfaceAt_lt_base_of_orphanless_of_ne_one h_coherent h_surface
                -/)
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
  erw [h_parent_isCoherent.get_isSome_iff, indexSecondFromTopOfLast_val]
  dsimp
  apply Nat.ne_of_lt
  apply Nat.sub_succ_lt_self
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  exact
    ⟨Ne.symm <| ne_of_lt <| List.length_pos_of_ne_nil <| x.parents.index_get_ne_nil _,
      x.pairable.fst.transfer_last _ ▸ h_last_length⟩

/-- `@badroot x _ _` contains (↓BadRoot(x),↓BadRootHeight(x)) -/
def badroot : ∀ {x : Mountain}, x.values.val ≠ [] → x.IsCoherent → Option (Index₂ x.values.val) :=
  diagonalRec
    (fun x ne_nil h_coherent _ =>
      if h_last_length : (x.pairable.fst.transfer (Index.last ne_nil)).get.length = 1 then none
      else
        some <| x.pairable.symm.transfer <|
          h_coherent.to_isCrossCoherent.to_parent_isCoherent.indexParentOfIsSome <|
          indexSecondFromTopOfLast_parents_val_get_isSome_of_last_height_ne_one
            ne_nil h_coherent h_last_length)
    (fun x _ _ _ p => p.map fun p =>
      ⟨Pairable.transfer (mountain_length_eq .. |>.trans <| diagonal_length_eq ..) p.fst,
        Index.last (x.values.index_get_ne_nil _)⟩)

theorem badroot_of_last_height_eq_one {x : Mountain} (ne_nil : x.values.val ≠ [])
    (h_coherent : x.IsCoherent)
    (h_last_length : (x.pairable.fst.transfer (Index.last ne_nil)).get.length = 1) :
    badroot ne_nil h_coherent = none :=
  by
  rw [badroot,
    diagonalRec_of_surface_eq_one
      (h_surface := surfaceAt_eq_one_of_height_eq_one h_coherent h_last_length),
    dite_cond_eq_true (eq_true h_last_length)]

theorem badroot_of_last_height_ne_one_of_last_surface_eq_one {x : Mountain}
    (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent)
    (h_last_length : (x.pairable.fst.transfer (Index.last ne_nil)).get.length ≠ 1)
    (h_surface : surfaceAt (Index.last ne_nil) = 1) :
    badroot ne_nil h_coherent =
      (some <| x.pairable.symm.transfer <|
        h_coherent.to_isCrossCoherent.to_parent_isCoherent.indexParentOfIsSome <|
        indexSecondFromTopOfLast_parents_val_get_isSome_of_last_height_ne_one
          ne_nil h_coherent h_last_length) :=
  by
  rw [badroot, diagonalRec_of_surface_eq_one (h_surface := h_surface),
    dite_cond_eq_false (eq_false h_last_length)]

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

theorem Mountain.IsLimit.iff_last_length_ne_one (x : Mountain) :
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
      erw [badroot_of_last_surface_ne_one ne_nil h_coherent h_surface, Option.isSome_map]
      generalize_proofs _ _ diagonal_ne_nil diagonal_isCoherent
      apply badroot_isSome
      apply IH diagonal_ne_nil
      intro H
      apply absurd <|
        Mountain.base_value_eq_one_of_parents_isCoherent_of_isOrphanless_of_height_eq_one
          diagonal_isCoherent.to_isCrossCoherent.to_parent_isCoherent
          diagonal_isCoherent.to_isOrphanless
          (((Mountain.pairable _).snd _).def.trans H)
      rw [mountain_value_at_index_eq_value _ ⟨_, _⟩]
      dsimp
      erw [Option.get_some, diagonal_value_at, Pairable.transfer_transfer_apply,
        Pairable.transfer_last]
      exact h_surface

/-- `@cutChild x _` contains CutHeight(x) -/
def cutChild {V : ValueMountain} (ne_nil : V.val ≠ []) : Index (Index.last ne_nil).get :=
  if surfaceAt (Index.last ne_nil) = 1
  then
    ⟨(Index.last ne_nil).get.length - 2,
      Nat.sub_lt (List.length_pos_of_ne_nil (V.index_get_ne_nil _)) Nat.two_pos⟩
  else Index.last (V.index_get_ne_nil _)

/-- `@cutChild x _` contains CutHeight(x) -/
@[simp]
lemma cutChild_val {V : ValueMountain} (ne_nil : V.val ≠ []) :
    (cutChild ne_nil).val =
      if surfaceAt (Index.last ne_nil) = 1
      then (Index.last ne_nil).get.length - 2
      else (Index.last ne_nil).get.length - 1 :=
  by unfold cutChild ; split_ifs <;> rfl

theorem exists_iterate_descend_last_last_eq_badroot
    {x : Mountain} (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent) :
    ∃ (k : ℕ),
      ((flip bind (descend h_coherent.to_isCrossCoherent.to_parent_isCoherent))^[k] <|
          some
            ⟨x.pairable.fst.transfer (Index.last ne_nil),
              Index.last (x.parents.index_get_ne_nil _)⟩).map x.pairable.symm.transfer =
        badroot ne_nil h_coherent :=
  by
  refine diagonalRec ?base ?rec ne_nil h_coherent
      (C := fun x => ∀ ne_nil h_coherent,
        let hP := h_coherent.to_isCrossCoherent.to_parent_isCoherent
        ∃ (k : ℕ),
          ((flip bind (descend hP))^[k] <| some
              ⟨x.pairable.fst.transfer (Index.last ne_nil),
                Index.last (x.parents.index_get_ne_nil _)⟩).map x.pairable.symm.transfer =
            badroot ne_nil h_coherent)
      ne_nil h_coherent
     <;> clear! x <;> intro x _ _ h_surface
  case base =>
    intro ne_nil h_coherent hP
    by_cases h_last_length : (x.pairable.fst.transfer (Index.last ne_nil)).get.length = 1
    · rw [badroot_of_last_height_eq_one (h_last_length := h_last_length),
        exists_congr fun _ => Option.map_eq_none_iff]
      exact descend_finite ..
    · rw [badroot_of_last_height_ne_one_of_last_surface_eq_one
          (h_last_length := h_last_length) (h_surface := h_surface)]
      use 2
      sorry
      /-
      simp only [Option.bind_eq_bind, Function.iterate_succ_apply, Function.iterate_one, flip,
        Option.bind_some, Option.map_bind]
      unfold descend
      rw [dite_cond_eq_false (by simp [hP.get_isSome_iff])]
      dsimp
      split
      next _ _ heq =>
        exfalso
        apply h_last_length
        exact Nat.eq_add_of_sub_eq (by assumption) (Fin.val_eq_of_eq heq)
      next j hj heq =>
        rw [Option.bind_some, dite_cond_eq_true <| eq_true ?pf]
        case pf =>
          simp only [hP.get_isSome_iff, Index₂.mk_val_snd, Pairable.transfer_last]
          refine Nat.ne_of_lt <| Nat.lt_sub_of_add_lt <| Nat.lt_of_lt_of_eq hj ?_
          rw [Pairable.transfer_last]
        rw [Option.map_some]
        congr 2
        ext : 1
        iterate 2 rw [hP.indexParentOfIsSome_val]
        simp only [Index₂.mk_val_snd, indexSecondFromTopOfLast_val, Prod.ext_iff]
        refine and_iff_right_of_imp ?_ |>.mpr ?_
        · intro hj
          subst hj
          congr <;> simp
        · apply Nat.eq_sub_of_add_eq
          have := Fin.val_eq_of_eq heq
          simp only [Index.last_val, Pairable.transfer_last, Nat.succ_eq_add_one,
            Nat.pred_eq_succ_iff] at this
          exact this.symm
      -/
  case rec =>
    intro IH ne_nil h_coherent hP
    have badroot_isSome := Mountain.IsLimit.iff_last_length_ne_one x
      |>.mpr ⟨ne_nil, h_coherent, mt (surfaceAt_eq_one_of_height_eq_one h_coherent) h_surface⟩
      |>.badroot_isSome
    rw [badroot_of_last_surface_ne_one (h_surface := h_surface)] at badroot_isSome ⊢
    erw [Option.isSome_map] at badroot_isSome
    generalize_proofs _ ne_nil' h_coherent' _ _ _ _ _ at badroot_isSome ⊢
    specialize IH ne_nil' h_coherent'
    extract_lets hP' at IH
    have ⟨k, hk⟩ : ∃ k,
        ((flip bind (inIndexElim
            (Index.get ∘ (diagonal hP h_coherent.to_isOrphanless).pairable.transfer)
            none))^[k] <| some (Index.last ne_nil')) =
          (badroot ne_nil' h_coherent').map (·.val.fst) :=
      by
      rcases IH with ⟨k, hk⟩
      rw [← hk]
      clear hk
      conv in Option.map .. => rw [Option.map_map, Function.comp_def]
      simp only [Pairable₂.val_transfer]
      set p := _^[k] _
      by_cases hp : p.isSome
      · rw [← Option.some_get hp, Option.map_some]
        induction k with
        | zero =>
          use 0
          sorry
          /-
          simp only [Option.bind_eq_bind, Index.last_val, Function.iterate_zero_apply,
            Option.get_some, Index₂.mk_val_fst, Pairable.transfer_last, Option.some.injEq, p]
          exact congrArg (· - 1) (buildMountain _).pairable.fst
          -/
        | succ k IH =>
          extract_lets q at IH
          have hq : q.isSome := iterate_bind_isSome_le (Nat.le_succ _) hp
          obtain ⟨k₁, hk₁⟩ := IH hq
          refine Exists.casesOn ?_ fun k hk => ⟨k + k₁, hk⟩
          conv in _^[_] _ => rw [Function.iterate_add_apply, hk₁]
          have p_eq : p = _^[_] _ := rfl
          rw [Function.iterate_succ_apply', show _^[_] _ = q from rfl, flip, ← Option.some_get hq,
            Option.bind_eq_bind, Option.bind_some, descend] at p_eq
          split_ifs at p_eq with h
          · simp only [p_eq, Option.get_some, hP'.indexParentOfIsSome_val,
              mountain_parent_at_index_eq_parent, Option.some_get]
            convert exists_iterate_parent_list_get_eq_parent ..
            rw [Pairable.val_transfer, Index₂.fst_val]
          · split at p_eq
            next => rw [p_eq] at hp; contradiction
            next => exact ⟨0, by sorry /- simp [p_eq] -/⟩
      · rw [Option.not_isSome_iff_eq_none.mp hp, Option.map_none]
        apply iterateEventuallyNone_of_toNoneOrLtId
        apply toNoneOrLtId_parent_list_get
    rw [show Index.get = _ from funext <| diagonal_parent_at _ _] at hk
    replace hk :
        ((flip bind (descendToSurface hP))^[k] <| some
            ⟨x.pairable.fst.transfer (Index.last ne_nil),
              Index.last (x.parents.index_get_ne_nil _)⟩).map (·.val.fst) =
          (badroot ne_nil' h_coherent').map (·.val.fst) :=
      by
      rw [← hk]
      clear hk
      symm; trans; trans; swap
      · exact congrArg (Option.map Fin.val) <|
          iterate_bind_diagonalPreparentOf_eq_iterate_bind_descendToSurface_last_get_map_fst
            hP (Index.last <| List.ne_nil_iff_of_length_eq x.pairable.fst |>.mp ne_nil) k
      · induction k with
        | zero =>
          simp only [Function.iterate_zero_apply, Index.last_val, Option.map_some]
          congr 2
          exact mountain_length_eq .. |>.trans (diagonal_length_eq ..) |>.trans x.pairable.fst
        | succ k IH =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', IH]
          cases q_eq : _^[_] _ with
          | none => rfl
          | some q =>
            sorry
            /-
            simp only [flip, Option.map_some, Option.map_eq_map, Option.bind_eq_bind,
              Option.bind_some, Function.comp_apply, Option.map_map]
            rw [inIndexElim_of_lt]
            case hi =>
              clear IH
              induction k generalizing q with
              | zero =>
                rw [Function.iterate_zero_apply, Option.some.injEq] at q_eq
                rw [← q_eq, Index.last_val, diagonal_length_eq, ← x.pairable.fst]
                exact Nat.sub_lt (List.length_pos_of_ne_nil ne_nil) Nat.zero_lt_one
              | succ k IH =>
                have := Option.isSome_iff_exists.mpr ⟨_, q_eq⟩
                replace := iterate_bind_isSome_le (Nat.le_succ _) this
                obtain ⟨p, p_eq⟩ := Option.isSome_iff_exists.mp this
                specialize IH p p_eq
                rw [Function.iterate_succ_apply', p_eq] at q_eq
                have := toNoneOrLtId_diagonalPreparentOf hP p
                rw [inIndexElim_of_lt] at this
                case hi => rwa [diagonal_length_eq, x.pairable.fst] at IH
                simp only [flip, Option.bind_eq_bind, Function.comp_apply, Option.bind_some,
                  Option.map_eq_some_iff, Sigma.exists, exists_and_right, exists_eq_right] at q_eq
                rcases q_eq with ⟨_, q_eq⟩
                simp only [Fin.eta, Function.comp_apply, q_eq, Option.map_some,
                  Index₂.mk_val_fst] at this
                exact WithBot.coe_lt_coe.mp this |>.trans IH
            simp only [Pairable.transfer, Function.comp_apply, Fin.eta]
            congr
            -/
      · sorry
        /-
        rw [Option.map_map, Pairable.transfer_last]
        congr
        -/
    rw [← Option.some_get badroot_isSome, Option.map_some] at hk
    obtain ⟨K, hK⟩ := exists_iterate_bind_trans_of_iterateEventuallyNone
      (g := descendToSurface hP) (descend_finite _) (fun _ => ⟨_, rfl⟩) ⟨k, rfl⟩
    erw [← hK] at hk
    use K
    obtain ⟨hK', hk'⟩ := Option.eq_some_iff_get_eq.mp hk
    rw [Option.get_map] at hk'
    erw [← Option.some_get badroot_isSome, Option.map_some, Option.eq_some_iff_get_eq]
    use Option.isSome_map .. |>.symm ▸ by generalize_proofs at hk'; assumption
    rw [Option.get_map]
    ext
    · simp [← hk']
    · simp only [↓hK, Pairable₂.val_transfer, Index₂.mk_val_snd, Index.last_val]
      rw [(x.pairable.snd _).def,
        ← Fin.mk_val ((badroot ne_nil' h_coherent').get badroot_isSome).fst]
      simp only [Index₂.fst_val, ← hk', hK]
      cases k with
      | zero => rfl
      | succ k =>
        change let q : Index₂ _ := _; q.val.snd = (List.length <| Index.get ⟨q.val.fst, _⟩) - 1
        intro q
        have q_eq : q = Option.get .. := rfl
        conv at q_eq in _^[_] _ =>
          rw [Function.iterate_succ_apply',
            ← Option.some_get <| iterate_bind_isSome_le (Nat.le_succ _) <|
              Option.isSome_map .. |>.symm ▸ hK ▸ hK']
          simp [flip, ↓Option.bind_eq_bind, ↓Option.bind_some]
        rw [descendToSurface_eq_fst_last] at q_eq
        simp_rw [q_eq]
        rfl

theorem badroot_fst_ne_last_of_isLimit {x : Mountain} (h : x.IsLimit) :
    ((badroot ..).get h.badroot_isSome).fst ≠ Index.last h.to_values_val_ne_nil :=
  by
  refine diagonalRec ?base ?rec h.to_values_val_ne_nil h.to_isCoherent h
      (C := fun x => ∀ h, ((badroot ..).get h.badroot_isSome).fst ≠ Index.last h.to_values_val_ne_nil)
     <;> clear! x <;> intro x _ _ h_surface
  case base =>
    intro h
    simp_rw [badroot_of_last_height_ne_one_of_last_surface_eq_one
        (h_last_length := h.last_length_ne_one) (h_surface := h_surface)]
    rw [Fin.ne_iff_vne]
    apply Nat.ne_of_lt
    have hP := h.to_isCoherent.to_isCrossCoherent.to_parent_isCoherent
    simp only [Option.get_some, Index₂.fst_val, Pairable₂.val_transfer,
      ParentMountain.IsCoherent.indexParentOfIsSome_val, Index.last_val, gt_iff_lt]
    rw [← WithBot.coe_lt_coe, WithBot.some, Option.some_get, x.pairable.fst]
    apply hP.get_lt
  case rec =>
    intro IH h
    simp_rw [badroot_of_last_surface_ne_one (h_surface := h_surface)]
    generalize_proofs
    specialize IH ⟨_, _, Option.isSome_map .. ▸ show Option.isSome _ by assumption⟩
    rw [Fin.ne_iff_vne] at IH ⊢
    erw [Index₂.fst_val, Option.get_map, Index₂.mk_val_fst, Pairable.val_transfer, Index.last_val]
    conv_rhs at IH => rw [Index.last_val, mountain_length_eq, diagonal_length_eq]
    exact IH

theorem badroot_val_snd_le_cutChild_val_of_isLimit {x : Mountain} (h : x.IsLimit) :
    ((badroot ..).get h.badroot_isSome).val.snd ≤ (cutChild h.to_values_val_ne_nil).val :=
  by
  have ⟨k, hk⟩ := exists_iterate_descend_last_last_eq_badroot h.to_values_val_ne_nil h.to_isCoherent
  have k_ne_zero : k ≠ 0 :=
    by
    intro H
    subst H
    apply badroot_fst_ne_last_of_isLimit h
    ext
    sorry
    /-
    simp only [← hk, Function.iterate_zero_apply, Option.map_some, Option.get_some, Index₂.fst_val,
      Pairable₂.val_transfer, Index₂.mk_val_fst, Pairable.transfer_last, Index.last_val]
    rw [x.pairable.fst]
    -/
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero k_ne_zero
  rw [Function.iterate_succ_apply] at hk
  have h' := h.badroot_isSome
  rw [← hk, Option.isSome_map] at h'
  replace h' := isSome_of_iterate_bind_isSome h'
  rw [← Option.some_get h'] at hk
  simp only [cutChild_val, ← hk, Option.get_map, Pairable₂.val_transfer]
  refine Nat.le_trans (iterate_descend_pairwise_le_of_it_isSome _).right ?_
  dsimp [flip]
  unfold descend
  sorry
  /-
  simp only [ne_eq, h.to_isCoherent.to_isCrossCoherent.to_parent_isCoherent.get_isSome_iff,
    Index₂.mk_val_snd, Index.last_val, Pairable.transfer_last, not_true_eq_false, ↓reduceDIte]
  trans; swap
  · split_ifs
    · rfl
    · exact Nat.sub_le_sub_left (Nat.le_succ _) _
  rcases hj :
      id <| Index.last <| x.parents.index_get_ne_nil <|
        x.pairable.fst.transfer <| Index.last h.to_values_val_ne_nil
    with ⟨j, _⟩ -- work around a weird bug that makes "split"/"cases"/"match" fail
  dsimp at hj
  simp only [hj]
  cases j <;> dsimp
  case zero =>
    generalize_proofs
    contradiction
  case succ =>
    have hj := congrArg Fin.val hj
    simp only [Index.last_val, Pairable.transfer_last, Nat.pred_eq_succ_iff] at hj
    rw [x.pairable.snd]
    simp [hj]
  -/

end Badroot

end Ysequence
