import Googology.YSequence.Intro
import Mathlib.Data.Nat.WithBot

namespace Ysequence

variable {α β γ : Type}

abbrev Index (s : List α) : Type :=
  Fin s.length

def Index.get {s : List α} (i : Index s) : α :=
  s.get i

def Pairable (s : List α) (t : List β) : Prop :=
  s.length = t.length

theorem Index.eq_iff_val_eq {s : List α} (i : Index s) (i' : Index s) :
    i = i' ↔ i.val = i'.val :=
  Fin.ext_iff

theorem Index.eq_get_of_base_eq_of_heq {s t : List α} (h : s = t) {i : Index s} {i' : Index t} :
    HEq i i' → i.get = i'.get := by
  subst h
  rw [Fin.heq_ext_iff rfl, ← Index.eq_iff_val_eq]
  exact congr_arg _

theorem Index.exists_iff {s : List α} {p : Index s → Prop} :
    (∃ i : Index s, p i) ↔ ∃ (i : ℕ) (h : i < s.length), p ⟨i, h⟩ :=
  Fin.exists_iff

theorem Index.forall_iff {s : List α} {p : Index s → Prop} :
    (∀ i : Index s, p i) ↔ ∀ (i : ℕ) (h : i < s.length), p ⟨i, h⟩ :=
  Fin.forall_iff

theorem Index.get_mem {s : List α} (i : Index s) : i.get ∈ s :=
  List.get_mem ..

theorem Index.val_ne_pred_length_iff {s : List α} {i : Index s} :
    i.val ≠ s.length - 1 ↔ i.val < s.length - 1 :=
  ne_iff_lt_iff_le.mpr (Nat.le_pred_of_lt i.isLt)

def Index.last {s : List α} (h : s ≠ []) : Index s :=
  ⟨s.length - 1, Nat.sub_lt (List.length_pos_of_ne_nil h) (Nat.succ_pos 0)⟩

@[simp]
lemma Index.last_val {s : List α} (h : s ≠ []) : (Index.last h).val = s.length - 1 :=
  rfl

instance (s : List α) : Fintype (Index s) :=
  Fin.fintype _

def inIndexElim {s : List α} (f : Index s → β) (g : β) (i : ℕ) : β :=
  if h : i < s.length then f ⟨i, h⟩ else g

@[simp]
theorem inIndexElim_yes {s : List α} (f : Index s → β) (g : β) (i : Index s) :
    inIndexElim f g i.val = f i := by
  simp [inIndexElim, i.isLt]

theorem inIndexElim_of_lt {s : List α} (f : Index s → β) (g : β) {i : ℕ} (hi : i < s.length) :
    inIndexElim f g i = f ⟨i, hi⟩ :=
  inIndexElim_yes f g ⟨i, hi⟩

@[simp]
theorem inIndexElim_no {s : List α} (f : Index s → β) (g : β) (i : ℕ)
    (h : ¬∃ i' : Index s, i'.val = i) : inIndexElim f g i = g := by
  simp only [inIndexElim, dite_eq_right_iff]
  intro hi
  exact absurd ⟨⟨i, hi⟩, rfl⟩ h

theorem toNoneOrLtId_inIndexElim_yes_none_of_forall_index {s : List α} (f : Index s → Option ℕ)
    (h : ∀ i : Index s, WithBot.lt.lt (f i) ↑i.val) : ToNoneOrLtId (inIndexElim f none) := by
  intro i
  rw [inIndexElim]
  split_ifs with h'
  · exact h ⟨i, h'⟩
  · exact WithBot.bot_lt_coe i

theorem toNoneOrLtId_inIndexElim_yes_none_forall_index_of {s : List α} (f : Index s → Option ℕ)
    (h : ToNoneOrLtId (inIndexElim f none)) : ∀ i : Index s, WithBot.lt.lt (f i) ↑i.val := by
  intro i
  specialize h i.val
  rw [inIndexElim_yes] at h
  exact h

theorem Pairable.def {s : List α} {t : List β} : Pairable s t → s.length = t.length :=
  id

theorem Pairable.refl (s : List α) : Pairable s s :=
  Eq.refl _

theorem Pairable.symm {s : List α} {t : List β} : Pairable s t → Pairable t s :=
  Eq.symm

theorem Pairable.trans {s : List α} {t : List β} {u : List γ} :
    Pairable s t → Pairable t u → Pairable s u :=
  Eq.trans

def Pairable.transfer {s : List α} {t : List β} (h : Pairable s t) (i : Index s) : Index t :=
  ⟨i.val, lt_of_lt_of_eq i.isLt h⟩

@[simp]
theorem Pairable.transfer_self {s : List α} (h : Pairable s s) : h.transfer = id :=
  rfl

@[simp]
theorem Pairable.transfer_transfer_apply {s : List α} {t : List β} {u : List γ}
    (hst : Pairable s t) (htu : Pairable t u) (i : Index s) :
    htu.transfer (hst.transfer i) = (hst.trans htu).transfer i :=
  rfl

@[simp]
theorem Pairable.transfer_transfer {s : List α} {t : List β} {u : List γ}
    (hst : Pairable s t) (htu : Pairable t u) :
    htu.transfer ∘ hst.transfer = (hst.trans htu).transfer :=
  rfl

@[simp]
theorem Pairable.val_transfer {s : List α} {t : List β} (h : Pairable s t) (i : Index s) :
    (h.transfer i).val = i.val :=
  rfl

theorem List.eq_nil_iff_of_length_eq {s : List α} {t : List β} (h : s.length = t.length) :
    s = [] ↔ t = [] :=
  List.length_eq_zero.symm.trans <| Eq.congr h rfl |>.trans List.length_eq_zero

theorem List.ne_nil_iff_of_length_eq {s : List α} {t : List β} (h : s.length = t.length) :
    s ≠ [] ↔ t ≠ [] :=
  not_congr (List.eq_nil_iff_of_length_eq h)

@[simp]
theorem Pairable.transfer_last {s : List α} {t : List β} (h : Pairable s t) (ne_nil : s ≠ []) :
    h.transfer (Index.last ne_nil) = Index.last (List.ne_nil_iff_of_length_eq h |>.mp ne_nil) :=
  Fin.eq_of_val_eq <| congrArg (· - 1) h.def

instance (s : List α) (t : List β) : Decidable <| Pairable s t :=
  instDecidableEqNat _ _

theorem Pairable.list_ext {s t : List α} (h : Pairable s t)
    (h' : ∀ i : Index s, i.get = (h.transfer i).get) : s = t := by
  apply List.ext_get h
  intro n h₁ h₂
  rw [Index.forall_iff] at h'
  exact h' n h₁

theorem flip_bind_inIndexElim_val_eq_iff_of_pairable {s : List α} {t : List β}
    (h : Pairable s t) (f : Index s → Option γ) (f' : Index t → Option γ) (g : Option γ)
    (i : Index s) :
    (flip bind (inIndexElim f g) <| some i.val) = (flip bind (inIndexElim f' g) <| some i.val) ↔
      f i = f' (h.transfer i) :=
  by
  simp only [flip, Option.bind_eq_bind, Option.some_bind, inIndexElim_yes,
    inIndexElim_of_lt f' _ <| lt_of_lt_of_eq i.isLt h]
  rfl

theorem flip_bind_inIndexElim_forall_eq_iff_of_pairable {s : List α} {t : List β}
    (h : Pairable s t) (f : Index s → Option γ) (f' : Index t → Option γ) (g : Option γ) :
    (∀ (n : Option ℕ), flip bind (inIndexElim f g) n = flip bind (inIndexElim f' g) n) ↔
      ∀ (i : Index s), f i = f' (h.transfer i) :=
  ⟨fun h' _ => flip_bind_inIndexElim_val_eq_iff_of_pairable .. |>.mp (h' _),
    fun h' => Option.rec rfl fun _ => dite_congr (congrArg _ h) (fun _ => h' _) (fun _ => rfl)⟩

theorem flip_bind_inIndexElim_yes_none_val_apply {s : List α} (f : Index s → Option ℕ) (i : Index s) :
    (flip bind (inIndexElim f none) <| some i.val) = f i :=
  by simp only [flip, Option.bind_eq_bind, Option.some_bind, inIndexElim_yes]

theorem flip_bind_inIndexElim_yes_none_val {s : List α} (f : Index s → Option ℕ) :
    (fun i => flip bind (inIndexElim f none) <| some i.val) = f :=
  funext fun _ => flip_bind_inIndexElim_yes_none_val_apply ..

theorem flip_bind_inIndexElim_to_none_of_lt {s : List α} (f : Index s → Option ℕ) {i : ℕ}
    (hi : i < s.length) :
    (flip bind (inIndexElim f none) <| some i) = f ⟨i, hi⟩ :=
  flip_bind_inIndexElim_yes_none_val_apply f ⟨i, hi⟩

theorem exists_iterate_bind_join_dependent_of_iterateEventuallyNone {s : List α} {f : Index s → Option ℕ}
    (hf : IterateEventuallyNone (inIndexElim f none)) (g : Index s → ℕ) (n : Option ℕ) (k : ℕ) :
    ∃ (k' : ℕ),
      (flip bind (inIndexElim f none))^[k'] n =
        (flip bind (inIndexElim
            (fun i => (flip bind (inIndexElim f none))^[g i] <| some i.val)
          none))^[k] n :=
  by
  induction k generalizing n with
  | zero => exact ⟨0, rfl⟩
  | succ k IH =>
    set y := _^[k + 1] _
    by_cases h : y.isSome
    · obtain ⟨p, hp⟩ :=
        Option.isSome_iff_exists.mp <| iterate_bind_isSome_le (Nat.le_add_left 1 k) h
      unfold_let y
      obtain ⟨k'', hk''⟩ := IH (some p)
      rw [Function.iterate_add_apply, hp, ← hk'']
      cases n with
      | none => contradiction
      | some n =>
        simp only [Option.bind_eq_bind, Function.iterate_one, flip, inIndexElim,
          Option.some_bind] at hp
        split_ifs at hp
        exact hp ▸ ⟨k'' + g _, Function.iterate_add_apply ..⟩
    · rw [Option.not_isSome_iff_eq_none] at h
      rw [h]
      exact hf _

theorem exists_iterate_bind_trans_of_iterateEventuallyNone {s : List α} {t : List β} {u : List γ}
    {f₁ : Index s → Option ℕ} {f₂ : Index t → Option ℕ} {f₃ : Index u → Option ℕ}
    (hst : Pairable s t)
    (hf₁ : IterateEventuallyNone (inIndexElim f₁ none))
    (hf₂ : ∀ (i : Index t), ∃ (k : ℕ), ((flip bind (inIndexElim f₁ none))^[k] <| some i.val) = f₂ i)
    (i : Index u) (hf₃ : ∃ (k : ℕ), ((flip bind (inIndexElim f₂ none))^[k] <| some i.val) = f₃ i) :
    ∃ (k' : ℕ), ((flip bind (inIndexElim f₁ none))^[k'] <| some i.val) = f₃ i :=
  by
  have ⟨k, hk⟩ := hf₃
  choose g hg using hf₂
  simp_rw [← hk, ← funext hg]
  have ⟨k', hk'⟩ := exists_iterate_bind_join_dependent_of_iterateEventuallyNone
    hf₁ (g ∘ hst.transfer) (some i.val) k
  use k'
  rw [hk']
  congr
  symm
  apply funext
  rw [flip_bind_inIndexElim_forall_eq_iff_of_pairable hst.symm]
  intro i
  rfl

theorem not_map_isSome_and_lt_same {s : List α} (f : Index s → Option ℕ+) (i : Index s) :
    i.val ∉
      ((Finset.univ.filter fun j : Index s => ∃ m ∈ f j, ∃ n ∈ f i, m < n)
        |>.map ⟨Fin.val, Fin.val_injective⟩) :=
  by
  simp [Fin.val_inj]
  intros
  simp_all

def Index₂ (m : List (List α)) : Type :=
  Σ i : Index m, Index <| Index.get i

def Index₂.val {m : List (List α)} (q : Index₂ m) : ℕ × ℕ :=
  (q.fst.val, q.snd.val)

def Index₂.get {m : List (List α)} (q : Index₂ m) : α :=
  q.snd.get

def Pairable₂ (m₁ : List (List α)) (m₂ : List (List β)) : Prop :=
  ∃ h : Pairable m₁ m₂, ∀ i : Index m₁, Pairable i.get (h.transfer i).get

@[simp]
theorem Index₂.fst_val {m : List (List α)} (q : Index₂ m) : q.fst.val = q.val.fst :=
  rfl

@[simp]
theorem Index₂.snd_val {m : List (List α)} (q : Index₂ m) : q.snd.val = q.val.snd :=
  rfl

theorem Index₂.val_fst_lt {m : List (List α)} (q : Index₂ m) : q.val.fst < m.length :=
  q.fst.isLt

theorem Index₂.val_snd_lt {m : List (List α)} (q : Index₂ m) : q.val.snd < q.fst.get.length :=
  q.snd.isLt

@[simp]
theorem Index₂.mk_val_fst {m : List (List α)} {i : Index m} {j : Index i.get} :
    (Index₂.val ⟨i, j⟩).fst = i.val :=
  rfl

@[simp]
theorem Index₂.mk_val_snd {m : List (List α)} {i : Index m} {j : Index i.get} :
    (Index₂.val ⟨i, j⟩).snd = j.val :=
  rfl

theorem Index₂.eq_of_val_eq {m : List (List α)} {q : Index₂ m} {q' : Index₂ m}
    (h : q.val = q'.val) : q = q' :=
  have fst_eq : q.fst = q'.fst := Fin.ext (Index₂.fst_val q ▸ Index₂.fst_val q' ▸ congr_arg _ h)
  Sigma.ext fst_eq
    ((Fin.heq_ext_iff
        (congr_arg List.length (Index.eq_get_of_base_eq_of_heq rfl (heq_of_eq fst_eq)))).mpr
      (Index₂.snd_val q ▸ Index₂.snd_val q' ▸ congr_arg _ h))

theorem Index₂.val_eq_of_eq {m : List (List α)} {q : Index₂ m} {q' : Index₂ m} :
    q = q' → q.val = q'.val :=
  congr_arg _

theorem Index₂.ne_of_val_ne {m : List (List α)} {q : Index₂ m} {q' : Index₂ m} :
    q.val ≠ q'.val → q ≠ q' :=
  mt Index₂.val_eq_of_eq

theorem Index₂.val_ne_of_ne {m : List (List α)} {q : Index₂ m} {q' : Index₂ m} :
    q ≠ q' → q.val ≠ q'.val :=
  mt Index₂.eq_of_val_eq

@[ext]
theorem Index₂.ext {m : List (List α)} {q : Index₂ m} {q' : Index₂ m} :
    q.val = q'.val → q = q' :=
  Index₂.eq_of_val_eq

@[simp]
theorem Index₂.eta₂ {m : List (List α)} (q : Index₂ m) (h₁ : q.val.fst < m.length)
    (h₂ : q.val.snd < (Index.get ⟨q.val.fst, h₁⟩).length) :
    (⟨⟨q.val.fst, h₁⟩, ⟨q.val.snd, h₂⟩⟩ : Index₂ m) = q :=
  Index₂.ext rfl

@[simp]
theorem Index₂.eta₂' {m : List (List α)} (q : Index₂ m) (h₁ : q.val.fst < m.length)
    (h₂ : q.val.snd < q.fst.get.length) :
    (⟨⟨q.val.fst, h₁⟩, ⟨q.val.snd, (Fin.eta q.fst h₁).symm ▸ h₂⟩⟩ : Index₂ m) = q :=
  Index₂.eta₂ ..

theorem Index₂.ext_iff {m : List (List α)} {q : Index₂ m} {q' : Index₂ m} :
    q = q' ↔ q.val = q'.val :=
  ⟨Index₂.val_eq_of_eq, Index₂.eq_of_val_eq⟩

theorem Index₂.val_injective {m : List (List α)} : Function.Injective <| Index₂.val (m := m) :=
  @Index₂.eq_of_val_eq _ _

theorem Index₂.eq_iff_val_eq {m : List (List α)} (q : Index₂ m) (q' : Index₂ m) :
    q = q' ↔ q.val = q'.val :=
  Index₂.ext_iff

theorem Index₂.ne_iff_val_ne {m : List (List α)} (q : Index₂ m) (q' : Index₂ m) :
    q ≠ q' ↔ q.val ≠ q'.val :=
  Iff.not Index₂.ext_iff

theorem Index₂.eq_iff_val_fst_eq_and_val_snd_eq {m : List (List α)} (q : Index₂ m)
    (q' : Index₂ m) : q = q' ↔ q.val.fst = q'.val.fst ∧ q.val.snd = q'.val.snd := by
  rw [Index₂.eq_iff_val_eq, Prod.eq_iff_fst_eq_snd_eq]

theorem Index₂.ne_iff_val_fst_ne_or_val_snd_ne {m : List (List α)} (q : Index₂ m)
    (q' : Index₂ m) : q ≠ q' ↔ q.val.fst ≠ q'.val.fst ∨ q.val.snd ≠ q'.val.snd := by
  rw [Ne, Index₂.eq_iff_val_fst_eq_and_val_snd_eq]
  apply Decidable.not_and_iff_or_not

theorem Index₂.mk_eq_mk {m : List (List α)} {i : Index m} {j : Index i.get} {i' : Index m}
    {j' : Index i'.get} : (⟨i, j⟩ : Index₂ m) = ⟨i', j'⟩ ↔ i = i' ∧ HEq j j' :=
  Sigma.mk.inj_iff

@[simp]
theorem Index₂.mk_mk_eq_mk_mk {m : List (List α)} {i : ℕ} {hi : i < m.length} {j : ℕ}
    {hj : j < (Index.get ⟨i, hi⟩).length} {i' : ℕ} {hi' : i' < m.length} {j' : ℕ}
    {hj' : j' < (Index.get ⟨i', hi'⟩).length} :
    (⟨⟨i, hi⟩, ⟨j, hj⟩⟩ : Index₂ m) = ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ ↔ (i, j) = (i', j') := by
  simp
  intro i_eq
  refine' Fin.heq_ext_iff _
  congr

theorem Index₂.eq_mk_mk_iff_val_eq {m : List (List α)} {q : Index₂ m} {i' : ℕ}
    {hi' : i' < m.length} {j' : ℕ} {hj' : j' < (Index.get ⟨i', hi'⟩).length} :
    q = ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ ↔ q.val = (i', j') := by
  rw [Index₂.ext_iff]
  rfl

theorem Index₂.val_mk {m : List (List α)} {i : Index m} {j : Index i.get} :
    Index₂.val ⟨i, j⟩ = (i.val, j.val) :=
  rfl

@[simp]
theorem Index₂.val_mk_mk {m : List (List α)} {i : ℕ} {hi : i < m.length} {j : ℕ}
    {hj : j < (Index.get ⟨i, hi⟩).length} : Index₂.val ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ = (i, j) :=
  rfl

theorem Index₂.mk_mk_val {m : List (List α)} (q : Index₂ m) :
    (⟨⟨q.val.fst, q.fst.isLt⟩, ⟨q.val.snd, q.snd.isLt⟩⟩ : Index₂ m) = q :=
  Index₂.eta₂' _ _ q.snd.isLt

theorem Index₂.exists_iff {m : List (List α)} {p : Index₂ m → Prop} :
    (∃ q : Index₂ m, p q) ↔ ∃ (i : Index m) (j : Index i.get), p ⟨i, j⟩ :=
  Sigma.exists

theorem Index₂.forall_iff {m : List (List α)} {p : Index₂ m → Prop} :
    (∀ q : Index₂ m, p q) ↔ ∀ (i : Index m) (j : Index i.get), p ⟨i, j⟩ :=
  Sigma.forall

theorem Index₂.get_mem {m : List (List α)} (q : Index₂ m) : ∃ c ∈ m, q.get ∈ c :=
  ⟨q.fst.get, Index.get_mem _, Index.get_mem _⟩

instance (m : List (List α)) : Fintype (Index₂ m) :=
  Sigma.instFintype

instance (m₁ : List (List α)) (m₂ : List (List β)) : Decidable <| Pairable₂ m₁ m₂ :=
  exists_prop_decidable _

theorem Pairable₂.refl (m : List (List α)) : Pairable₂ m m :=
  ⟨Pairable.refl _, fun _ => Pairable.refl _⟩

theorem Pairable₂.symm {m₁ : List (List α)} {m₂ : List (List β)} :
    Pairable₂ m₁ m₂ → Pairable₂ m₂ m₁ := fun h =>
  ⟨h.fst.symm, fun i => (h.snd (Pairable.transfer _ i)).symm⟩

theorem Pairable₂.trans {m₁ : List (List α)} {m₂ : List (List β)} {m₃ : List (List γ)} :
    Pairable₂ m₁ m₂ → Pairable₂ m₂ m₃ → Pairable₂ m₁ m₃ := fun h₁ h₂ =>
  ⟨h₁.fst.trans h₂.fst, fun i => (h₁.snd i).trans (h₂.snd _)⟩

def Pairable₂.transfer {m₁ : List (List α)} {m₂ : List (List β)} (h : Pairable₂ m₁ m₂)
    (q : Index₂ m₁) : Index₂ m₂ :=
  ⟨h.fst.transfer q.fst, (h.snd q.fst).transfer q.snd⟩

@[simp]
theorem Pairable₂.transfer_self {m : List (List α)} (h : Pairable₂ m m) : h.transfer = id :=
  rfl

@[simp]
theorem Pairable₂.transfer_transfer_apply {m₁ : List (List α)} {m₂ : List (List β)} {m₃ : List (List γ)}
    (h₁ : Pairable₂ m₁ m₂) (h₂ : Pairable₂ m₂ m₃) (q : Index₂ m₁) :
    h₂.transfer (h₁.transfer q) = (h₁.trans h₂).transfer q :=
  rfl

@[simp]
theorem Pairable₂.transfer_transfer {m₁ : List (List α)} {m₂ : List (List β)} {m₃ : List (List γ)}
    (h₁ : Pairable₂ m₁ m₂) (h₂ : Pairable₂ m₂ m₃) :
    h₂.transfer ∘ h₁.transfer = (h₁.trans h₂).transfer :=
  rfl

@[simp]
theorem Pairable₂.val_transfer {m₁ : List (List α)} {m₂ : List (List β)}
    (h : Pairable₂ m₁ m₂) (q : Index₂ m₁) : (h.transfer q).val = q.val :=
  rfl

theorem Pairable₂.list_ext {m₁ m₂ : List (List α)} (h : Pairable₂ m₁ m₂)
    (h' : ∀ q : Index₂ m₁, q.get = (h.transfer q).get) : m₁ = m₂ :=
  by
  apply h.fst.list_ext
  intro i
  apply (h.snd i).list_ext
  intro j
  rw [Index₂.forall_iff] at h'
  exact h' i j

end Ysequence
