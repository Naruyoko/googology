import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.WithBot
import Mathlib.Data.Pnat.Basic
import Mathlib.Order.Iterate
import Mathlib.Order.WellFounded

#align_import ysequence.defs

namespace Ysequence

section Intro

variable {α β γ : Type}

instance (p : Prop) [Decidable p] (q : α → Prop) [DecidablePred q] :
    DecidablePred <| Option.elim' p q := by
  intro o
  cases o <;> simp <;> infer_instance

instance Option.CasesOn.decidable (o : Option α) (p : Prop) [Decidable p] (q : α → Prop)
    [DecidablePred q] : Decidable <| Option.casesOn o p q := by
  cases o <;> simp <;> infer_instance

instance Option.CasesOn.decidablePred (p : Prop) [Decidable p] (q : α → Prop) [DecidablePred q] :
    DecidablePred fun o => Option.casesOn o p q := by
  intro o
  cases o <;> simp <;> infer_instance

instance (r : α → α → Prop) [DecidableRel r] : DecidablePred <| Function.uncurry r := by
  unfold Function.uncurry
  infer_instance

def IterateEventuallyNone (f : α → Option α) : Prop :=
  ∀ x : Option α, ∃ k : ℕ, (flip bind f)^[k] x = none

theorem iterateEventuallyNone_or_mem_of_iterateEventuallyNone {f : α → Option α}
    (hf : IterateEventuallyNone f) (p : Set α) (x : α) :
    ∃ k : ℕ, Option.elim' True p <| (flip bind f)^[k] <| some x := by
  rcases hf (some x) with ⟨k, hk⟩
  use k
  rw [hk]
  trivial

def findIndexIterateOfIterateEventuallyNone {f : α → Option α} (hf : IterateEventuallyNone f)
    {p : Set α} (_ : DecidablePred p) (x : α) : ℕ :=
  Nat.find (iterateEventuallyNone_or_mem_of_iterateEventuallyNone hf p x)

theorem findIndexIterate_spec {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) :
    Option.elim' True p <|
      (flip bind f)^[findIndexIterateOfIterateEventuallyNone hf decidable_p x] <| some x :=
  Nat.find_spec (iterateEventuallyNone_or_mem_of_iterateEventuallyNone hf p x)

theorem findIndexIterate_min {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) {k : ℕ} :
    k < findIndexIterateOfIterateEventuallyNone hf decidable_p x →
      ¬(Option.elim' True p <| (flip bind f)^[k] <| some x) :=
  Nat.find_min (iterateEventuallyNone_or_mem_of_iterateEventuallyNone hf p x)

theorem findIndexIterate_eq_iff {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) (k : ℕ) :
    findIndexIterateOfIterateEventuallyNone hf decidable_p x = k ↔
      (Option.elim' True p <| (flip bind f)^[k] <| some x) ∧
        ∀ l < k, ¬(Option.elim' True p <| (flip bind f)^[l] <| some x) :=
  Nat.find_eq_iff (iterateEventuallyNone_or_mem_of_iterateEventuallyNone hf p x)

def findIterateOfIterateEventuallyNone {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) : Option α :=
  (flip bind f)^[findIndexIterateOfIterateEventuallyNone hf decidable_p x] <| some x

theorem findIterate_spec {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) :
    Option.elim' True p <| findIterateOfIterateEventuallyNone hf decidable_p x :=
  findIndexIterate_spec _ _ _

theorem findIterate_isSome_iff {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) :
    (findIterateOfIterateEventuallyNone hf decidable_p x).isSome ↔
      ∃ (k : ℕ) (h : ((flip bind f)^[k] <| some x).isSome), Option.get _ h ∈ p := by
  constructor
  · intro h
    refine' ⟨_, h, _⟩
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
    conv in Option.get _ _ =>
      congr
      change findIterateOfIterateEventuallyNone hf decidable_p x
    have := findIterate_spec hf decidable_p x
    simp_rw [hy] at this ⊢
    exact this
  · intro h
    rcases h with ⟨k, hk₁, hk₂⟩
    by_contra H
    apply findIndexIterate_min hf decidable_p x (k := k)
    · clear hk₂
      contrapose hk₁ with H'
      rw [not_lt] at H'
      refine' Nat.le_induction H _ k H'
      intro k _ IH
      rw [Option.not_isSome_iff_eq_none] at IH ⊢
      rw [Function.iterate_succ_apply', IH]
      rfl
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hk₁
      simp_rw [hy] at hk₂ ⊢
      exact hk₂

theorem findIterate_eq_none_iff {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) :
    findIterateOfIterateEventuallyNone hf decidable_p x = none ↔
      ∀ {k : ℕ} (h : ((flip bind f)^[k] <| some x).isSome), Option.get _ h ∉ p := by
  rw [← not_iff_not]
  push_neg
  rw [Option.ne_none_iff_isSome]
  exact findIterate_isSome_iff _ _ _

theorem findIndexIterate_pos_of_not_mem {f : α → Option α} (hf : IterateEventuallyNone f)
    {p : Set α} (decidable_p : DecidablePred p) {x : α} (hn : x ∉ p) :
    0 < findIndexIterateOfIterateEventuallyNone hf decidable_p x := by
  rw [pos_iff_ne_zero]
  intro H
  have := findIndexIterate_spec hf decidable_p x
  rw [H] at this
  contradiction

def ToNoneOrLtId (f : ℕ → Option ℕ) : Prop :=
  ∀ n : ℕ, WithBot.lt.lt (f n) (some n)

theorem iterateEventuallyNone_of_toNoneOrLtId {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) :
    IterateEventuallyNone f := by
  refine fun n => IsWellFounded.induction WithBot.lt.lt
    (C := fun n => ∃ k, (flip bind f)^[k] n = none) n ?_
  intro n IH
  cases' n with n
  · exact ⟨0, rfl⟩
  · choose! k h using IH
    exact ⟨k (f n) + 1, h _ (hf n)⟩

def findIterateOfToNoneOrLtId {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) {p : Set ℕ}
    (decidable_p : DecidablePred p) : ℕ → Option ℕ :=
  findIterateOfIterateEventuallyNone (iterateEventuallyNone_of_toNoneOrLtId hf) decidable_p

theorem iterate_bind_none (f : α → Option α) : ∀ n : ℕ, (flip bind f)^[n] none = none :=
  Nat.rec rfl fun n IH => (by rw [Function.iterate_succ_apply', IH]; rfl)

theorem toNoneOrLtId_iterate_succ {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) (n k : ℕ) :
    WithBot.lt.lt ((flip bind f)^[k + 1] <| some n) (some n) := by
  induction' k with k IH
  · exact hf n
  · rw [Function.iterate_succ_apply']
    cases' hl : (flip bind f)^[k + 1] <| some n
    · exact WithBot.bot_lt_coe n
    · exact lt_trans (hf _) (hl ▸ IH)

theorem toNoneOrLtId_iterate_pos {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) (n : ℕ) {k : ℕ}
    (hk : 0 < k) : WithBot.lt.lt ((flip bind f)^[k] <| some n) (some n) := by
  cases' k with k
  · exact absurd hk (by decide)
  · exact toNoneOrLtId_iterate_succ hf n k

theorem toNoneOrLtId_findIterate_of_not_mem {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) {p : Set ℕ}
    (decidable_p : DecidablePred p) {n : ℕ} (hn : n ∉ p) :
    WithBot.lt.lt (findIterateOfToNoneOrLtId hf decidable_p n) n :=
  toNoneOrLtId_iterate_pos hf _ (findIndexIterate_pos_of_not_mem _ _ hn)

theorem toNoneOrLtId_findIterate_of_all_not_mem {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f)
    {g : ℕ → Set ℕ} (hg₁ : ∀ n, DecidablePred <| g n) (hg₂ : ∀ n, n ∉ g n) :
    ToNoneOrLtId fun n => findIterateOfToNoneOrLtId hf (hg₁ n) n :=
  fun n => toNoneOrLtId_findIterate_of_not_mem hf (hg₁ n) (hg₂ n)

/- Very hard to make this work

example :
    let p n :=
      @findIterateOfToNoneOrLtId (fun m => Nat.casesOn m none some)
        (by
          intro m
          cases m
          · exact WithBot.bot_lt_coe 0
          · exact with_bot.coe_lt_coe.mpr (Nat.lt_succ_self m))
        ({1, 3, 4, 6} \ {n}) (by infer_instance) n
    p <$> [0, 1, 2, 8] = [none, none, some 1, some 6] ∧ ToNoneOrLtId p :=
  ⟨by
    simp [find_iterate_of_to_none_or_lt_id, find_iterate_of_iterate_eventually_none,
      find_index_iterate_of_iterate_eventually_none]
    repeat' constructor
    on_goal 1 => suffices : Nat.find _ = 1; rw [this]; rfl
    on_goal 2 => suffices : Nat.find _ = 2; rw [this]; rfl
    on_goal 3 => suffices : Nat.find _ = 1; rw [this]; rfl
    on_goal 4 => suffices : Nat.find _ = 2; rw [this]; rfl
    all_goals rw [Nat.find_eq_iff]; simp [flip]; decide,
    by
    apply to_none_or_lt_id_find_iterate_of_all_not_mem
    intro n
    simp [(· ∈ ·)]
    exact not_and_not_right.mpr (congr_fun rfl)⟩
-/

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
theorem Index.last_val {s : List α} (h : s ≠ []) : (Index.last h).val = s.length - 1 :=
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
    (h : ∀ i : Index s, WithBot.lt.lt (f i) i.val) : ToNoneOrLtId (inIndexElim f none) := by
  intro i
  rw [inIndexElim]
  split_ifs with h'
  · exact h ⟨i, h'⟩
  · exact WithBot.bot_lt_coe i

theorem toNoneOrLtId_inIndexElim_yes_none_forall_index_of {s : List α} (f : Index s → Option ℕ)
    (h : ToNoneOrLtId (inIndexElim f none)) : ∀ i : Index s, WithBot.lt.lt (f i) i.val := by
  intro i
  specialize h i.val
  rw [inIndexElim_yes] at h
  exact h

theorem not_map_isSome_and_lt_same {s : List α} (f : Index s → Option ℕ+) (i : Index s) :
    i.val ∉
      (Finset.toSet <| Finset.image Fin.val <| Finset.univ.filter fun j : Index s =>
        Option.casesOn (Prod.mk <$> f j <*> f i) False (Function.uncurry LT.lt)) := by
  dsimp
  simp
  intro j hj
  contrapose! hj
  rw [← Index.eq_iff_val_eq] at hj
  rw [hj]
  cases f i <;> dsimp [Seq.seq]
  · exact not_false
  · exact irrefl _

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
theorem Pairable.val_transfer {s : List α} {t : List β} (h : Pairable s t) (i : Index s) :
    (h.transfer i).val = i.val :=
  rfl

theorem Pairable.transfer_last {s : List α} {t : List β} (h : Pairable s t) (ne_nil : s ≠ []) :
    h.transfer (Index.last ne_nil) =
      Index.last (s := t)
        (by rw [← List.length_pos_iff_ne_nil] at ne_nil ⊢; exact h.def ▸ ne_nil) := by
  simp only [Pairable.transfer, Index.last, h.def, ge_iff_le, Fin.val_mk]

instance (s : List α) (t : List β) : Decidable <| Pairable s t :=
  instDecidableEqNat _ _

theorem Pairable.list_ext {s t : List α} (h : Pairable s t)
    (h' : ∀ i : Index s, i.get = (h.transfer i).get) : s = t := by
  apply List.ext_get h
  intro n h₁ h₂
  rw [Index.forall_iff] at h'
  exact h' n h₁

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

@[simp]
theorem Option.seq_none_right {f : Option (α → β)} : f <*> none = none := by cases f <;> rfl

end Intro

section Types

/-- 𝕊 -/
def ValueList : Type :=
  { s : List ℕ+ // if h : 0 < s.length then Index.get (⟨0, h⟩ : Index s) = 1 else True }

/-- ^𝕊 -/
def ParentList : Type :=
  { t : List (Option ℕ) // ∀ i : Index t, WithBot.lt.lt i.get i.val }

theorem ParentList.head_eq_none {t : ParentList} (h : 0 < t.val.length) :
    Index.get (⟨0, h⟩ : Index t.val) = none :=
  Nat.WithBot.lt_zero_iff.mp (t.property _)

/-- 𝕊⁽²⁾ -/
structure ValueParentListPair where
  values : ValueList
  parents : ParentList
  pairable : Pairable values.val parents.val

/-- 𝕊⁽²⁾* = {x : 𝕊⁽²⁾ // x.is_orphanless} -/
def ValueParentListPair.IsOrphanless (x : ValueParentListPair) : Prop :=
  ∀ i : Index x.values.val, 1 < i.get.val → (x.pairable.transfer i).get.isSome

instance : DecidablePred ValueParentListPair.IsOrphanless := fun _ => Fintype.decidableForallFintype

example : { x : ValueParentListPair // ValueParentListPair.IsOrphanless x } :=
  let s : List ℕ+ := [1, 3, 4]
  let t := [none, some 0, some 1]
  ⟨⟨⟨s, by decide⟩, ⟨t, by decide⟩, by decide⟩, by decide⟩

/-- 𝕄ᵥ -/
def ValueMountain : Type :=
  { V : List (List ℕ+) // ∀ c ∈ V, c ≠ [] }

theorem ValueMountain.index_get_ne_nil (V : ValueMountain) (i : Index V.val) : i.get ≠ [] :=
  V.property _ (Index.get_mem i)

/-- 𝕄ₚ⁻ -/
def ParentMountain : Type :=
  { P : List (List (Option ℕ)) // ∀ c ∈ P, c ≠ [] }

theorem ParentMountain.index_get_ne_nil (P : ParentMountain) (i : Index P.val) : i.get ≠ [] :=
  P.property _ (Index.get_mem i)

/-- 𝕄ₚ = {P : 𝕄ₚ⁻ // P.IsCoherent} -/
def ParentMountain.IsCoherent (P : ParentMountain) : Prop :=
  ∀ q : Index₂ P.val,
    let i := q.val.fst
    let j := q.val.snd
    (q.get = none ↔ j = q.fst.get.length - 1) ∧
      WithBot.lt.lt q.get i ∧
        Option.elim' True (fun p => ∃ q' : Index₂ P.val, q'.val = (p, j)) q.get

theorem ParentMountain.IsCoherent.get_eq_none_iff {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : q.get = none ↔ q.val.snd = q.fst.get.length - 1 :=
  (hP q).left

theorem ParentMountain.IsCoherent.get_lt {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : WithBot.lt.lt q.get q.val.fst :=
  (hP q).right.left

theorem ParentMountain.IsCoherent.elim'_exists_index {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) :
    Option.elim' True (fun p => ∃ q' : Index₂ P.val, q'.val = (p, q.val.snd)) q.get :=
  (hP q).right.right

instance : DecidablePred ParentMountain.IsCoherent := fun _ => Fintype.decidableForallFintype

theorem ParentMountain.IsCoherent.get_isSome_iff {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : q.get.isSome ↔ q.val.snd ≠ q.fst.get.length - 1 :=
  Option.ne_none_iff_isSome.symm.trans (Decidable.not_iff_not.mpr (hP.get_eq_none_iff _))

theorem ParentMountain.IsCoherent.exists_index_of_isSome {P : ParentMountain} (hP : P.IsCoherent)
    {q : Index₂ P.val} (hq : q.get.isSome) :
    ∃ q' : Index₂ P.val, q'.val = (q.get.get hq, q.val.snd) :=
  by
  have := hP.elim'_exists_index q
  rw [← Option.some_get hq] at this
  exact this

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
    {q : Index₂ P.val} (hq : q.get.isSome) :
    { q' : Index₂ P.val //
      let j := q.val.snd
      q'.val = (q.get.get hq, j) } :=
  by
  refine ⟨⟨⟨q.get.get hq, ?_⟩, ⟨q.val.snd, ?_⟩⟩, rfl⟩
  all_goals
    cases' hP.exists_index_of_isSome hq with q' hq'
    rw [Index₂.val, Prod.eq_iff_fst_eq_snd_eq] at hq'
    simp at hq'
  · exact lt_of_eq_of_lt hq'.left.symm q'.val_fst_lt
  · refine' lt_of_eq_of_lt hq'.right.symm (lt_of_lt_of_eq q'.val_snd_lt _)
    congr
    exact Fin.eq_of_val_eq hq'.left

def ParentMountain.IsCoherent.indexAboveOfIsSome {P : ParentMountain} (hP : P.IsCoherent)
    {q : Index₂ P.val} (hq : q.get.isSome) :
    { q' : Index₂ P.val //
      let i := q.val.fst
      let j := q.val.snd
      q'.val = (i, j + 1) } :=
  by
  refine ⟨⟨q.fst, ⟨q.val.snd + 1, ?_⟩⟩, rfl⟩
  have h := (not_iff_not.mpr (hP.get_eq_none_iff q)).mp (Option.ne_none_iff_isSome.mpr hq)
  rw [lt_iff_le_and_ne]
  constructor
  · exact Nat.succ_le_of_lt q.val_snd_lt
  · rw [← Ne, ← Nat.succ_ne_succ] at h
    apply ne_of_ne_of_eq h
    exact Nat.sub_add_cancel (List.length_pos_of_ne_nil (P.index_get_ne_nil _))

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
      (x.pairable.symm.transfer (hP.indexAboveOfIsSome hq).val).get.val =
        (x.pairable.symm.transfer q).get.val -
          (x.pairable.symm.transfer (hP.indexParentOfIsSome hq).val).get.val

theorem Mountain.IsCrossCoherent.to_parent_isCoherent {x : Mountain} (h : x.IsCrossCoherent) :
    x.parents.IsCoherent :=
  h.fst

theorem Mountain.IsCrossCoherent.get_value_above_eq_of_parent_isSome {x : Mountain}
    (h : x.IsCrossCoherent) {q : Index₂ x.parents.val} (hq : q.get.isSome) :
    have hP : x.parents.IsCoherent := h.to_parent_isCoherent
    (x.pairable.symm.transfer (hP.indexAboveOfIsSome hq).val).get.val =
      (x.pairable.symm.transfer q).get.val -
        (x.pairable.symm.transfer (hP.indexParentOfIsSome hq).val).get.val :=
  h.snd hq

theorem Pnat.sub_val_eq_iff_eq_add {a b c : ℕ+} : a.val - b.val = c.val ↔ a = c + b :=
  by
  cases' a with a a_pos
  cases' b with b b_pos
  cases' c with c c_pos
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt c_pos)
  dsimp
  constructor <;> intro h
  · have h' := congr_arg (· + b) h
    simp only at h'
    apply PNat.eq
    dsimp
    convert ← h'
    exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_of_sub_eq_succ h))
  · have h' := congr_arg Subtype.val h
    dsimp at h'
    exact tsub_eq_of_eq_add h'

theorem Mountain.IsCrossCoherent.value_above_lt_value_of_parent_isSome {x : Mountain}
    (h : x.IsCrossCoherent) {q : Index₂ x.parents.val} (hq : q.get.isSome) :
    have hP : x.parents.IsCoherent := h.to_parent_isCoherent
    (x.pairable.symm.transfer (hP.indexAboveOfIsSome hq).val).get <
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
    x₁ = x₂ := by
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
      simp [ParentMountain.IsCoherent.indexParentOfIsSome]
      have := hx₁.to_parent_isCoherent.get_lt (hVP₁.transfer ⟨⟨i, hi⟩, ⟨j, hj⟩⟩)
      simp at this
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hj'
      simp [hp] at this ⊢
      exact WithBot.coe_lt_coe.mp this
  · clear! j
    intro hj
    apply value_eq_where_parent_eq_none (hVP₁.transfer ⟨⟨i, hi⟩, ⟨l, hj⟩⟩)
    rw [hx₁.to_parent_isCoherent.get_eq_none_iff]
    simp [← hl']
    congr 1
    exact hVP₁.snd _

theorem Mountain.IsCrossCoherent.value_ne_one_where_parent_isSome {x : Mountain}
    (h : x.IsCrossCoherent) {q : Index₂ x.parents.val} (hq : q.get.isSome) :
    (x.pairable.symm.transfer q).get ≠ 1 := by
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

theorem Mountain.IsCoherent.to_isOrphanless {x : Mountain} (h : x.IsCoherent) : x.IsOrphanless :=
  h.left

theorem Mountain.IsCoherent.to_isCrossCoherent {x : Mountain} (h : x.IsCoherent) :
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
      (Option.casesOn (Prod.mk <$> value p <*> value i) False (Function.uncurry (· < ·)) : Prop)
  value_isSome_of_parent_isSome : ∀ {i : Index x.values.val}, (parent i).isSome → (value i).isSome
  value_parent_isSome_of_parent_isSome :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      let p := (parentAsIndex h).val
      (value p).isSome

def buildRowBuilder (x : ValueParentListPair) (value : Index x.values.val → Option ℕ+)
    (parentCandidateNext : Index x.values.val → Option ℕ)
    (toNoneOrLtId_parentCandidateNext :
      ToNoneOrLtId (inIndexElim parentCandidateNext none)) :
    RowBuilder x :=
  let parent : Index x.values.val → Option ℕ := fun i =>
    findIterateOfToNoneOrLtId toNoneOrLtId_parentCandidateNext
      (p := (Finset.univ.filter fun p : Index x.values.val =>
            Option.casesOn (Prod.mk <$> value p <*> value i) False (Function.uncurry (· < ·))).map
        ⟨Fin.val, Fin.val_injective⟩)
      (fun _ => decidable_of_decidable_of_iff Set.mem_def) i.val
  have toNoneOrLtId_parent : ToNoneOrLtId (inIndexElim parent none) :=
    by
    apply toNoneOrLtId_inIndexElim_yes_none_of_forall_index
    intro i
    apply toNoneOrLtId_findIterate_of_not_mem
    simp
    intro k
    contrapose!
    intro hk
    rw [Fin.eq_of_val_eq hk]
    cases value i
    · exact not_false
    · dsimp; exact irrefl _
  let parentAsIndex :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      { p : Index x.values.val // p.val = (parent i).get h } :=
    fun {i} h =>
    ⟨⟨(parent i).get h, by
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
      Option.casesOn (Prod.mk <$> value p <*> value i) False (Function.uncurry (· < ·)) :=
    by
    intro i h
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
    rcases parentAsIndex h with ⟨⟨p, hp₁⟩, hp₂⟩
    simp only [hk, Option.get_some] at hp₂
    subst hp₂
    have spec : Option.elim' True _ (parent i) := findIterate_spec _ _ _
    simp only [hk, Option.elim'] at spec
    replace spec := Set.mem_def.mpr spec
    simp at spec
    rcases spec with ⟨⟨p', hp'₁⟩, hp'₂, hp'₃⟩
    subst hp'₃
    exact hp'₂
  have value_isSome_of_parent_isSome :
    ∀ {i : Index x.values.val}, (parent i).isSome → (value i).isSome :=
    by
    intro i h
    specialize parent_spec h
    contrapose parent_spec with H
    rw [Option.not_isSome_iff_eq_none] at H
    simp [H]
  have value_parent_isSome_of_parent_isSome :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      let p := (parentAsIndex h).val
      (value p).isSome :=
    by
    intro i h p
    replace parent_spec : Option.casesOn (Prod.mk <$> value p <*> value i) _ _ := parent_spec h
    contrapose parent_spec with H
    rw [Option.not_isSome_iff_eq_none] at H
    rw [H, Option.map_none, seq_eq_bind, Option.bind_eq_bind, Option.none_bind]
    exact not_false
  { value := value
    parent := parent
    toNoneOrLtId_parent := toNoneOrLtId_parent
    parentAsIndex := parentAsIndex
    parent_spec := parent_spec
    value_isSome_of_parent_isSome := value_isSome_of_parent_isSome
    value_parent_isSome_of_parent_isSome := value_parent_isSome_of_parent_isSome }

def mountainBuilder (x : ValueParentListPair) : ℕ → RowBuilder x
  | 0 =>
    buildRowBuilder x (some ∘ Index.get) (Index.get ∘ x.pairable.transfer)
      (by
        apply toNoneOrLtId_inIndexElim_yes_none_of_forall_index
        intro
        rw [← Pairable.val_transfer x.pairable _]
        exact x.parents.property _)
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
    ToNoneOrLtId (inIndexElim (fun i => parent x i j) none) :=
  (mountainBuilder x j).toNoneOrLtId_parent

def parentAsIndex {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ}
    (h : (parent x i j).isSome) :
    { p : Index x.values.val // p.val = (parent x i j).get h } :=
  (mountainBuilder x j).parentAsIndex h

theorem parent_spec {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ}
    (h : (parent x i j).isSome) :
    let p := (parentAsIndex h).val
    (Option.casesOn (Prod.mk <$> value x p j <*> value x i j) False (Function.uncurry (· < ·)) :
      Prop) :=
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
  intro p
  have spec := parent_spec h
  generalize_proofs hvp₀ hvt₀
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hvp₀
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hvt₀
  simp only [Option.get_some, parent, hm, hn]
  replace spec : Option.casesOn (Prod.mk <$> value x _ j <*> value x i j) _ _ := spec
  rw [hm, hn] at spec
  exact spec

theorem parent_of_value_eq_none {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    value x i j = none → parent x i j = none := by
  contrapose
  iterate 2 rw [← Ne, Option.ne_none_iff_isSome]
  exact value_isSome_of_parent_isSome

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
          apply toNoneOrLtId_inIndexElim_yes_none_of_forall_index
          intro
          rw [← Pairable.val_transfer x.pairable _]
          exact x.parents.property _)
        (p := (Finset.univ.filter fun p : Index x.values.val =>
              Option.casesOn (Prod.mk <$> value x p 0 <*> value x i 0) False (Function.uncurry (· < ·))).map
          ⟨Fin.val, Fin.val_injective⟩)
        (fun _ => decidable_of_decidable_of_iff Set.mem_def) i.val :=
  by
  rfl

@[simp]
theorem parent_succ (x : ValueParentListPair) (i : Index x.values.val) (j : ℕ) :
    parent x i (j + 1) =
      findIterateOfToNoneOrLtId (f := inIndexElim (fun p => parent x p j) none)
        (toNoneOrLtId_parent x j)
        (p := (Finset.univ.filter fun p : Index x.values.val =>
              Option.casesOn (Prod.mk <$> value x p (j + 1) <*> value x i (j + 1)) False
                (Function.uncurry (· < ·))).map
          ⟨Fin.val, Fin.val_injective⟩)
        (fun _ => decidable_of_decidable_of_iff Set.mem_def) i.val :=
  rfl

theorem value_succ_isSome_iff_parent_isSome {x : ValueParentListPair} {i : Index x.values.val}
    {j : ℕ} : (value x i (j + 1)).isSome ↔ (parent x i j).isSome :=
  by
  constructor
  · contrapose
    intro H
    simp [H]
  · intro h
    simp [h]

theorem value_succ_eq_none_iff_parent_eq_none {x : ValueParentListPair} {i : Index x.values.val}
    {j : ℕ} : value x i (j + 1) = none ↔ parent x i j = none :=
  by
  rw [← not_iff_not]
  iterate 2 rw [← Ne, Option.ne_none_iff_isSome]
  exact value_succ_isSome_iff_parent_isSome

theorem get_value_above_eq_of_parent_isSome {x : ValueParentListPair} {i : Index x.values.val}
    {j : ℕ} (h : (parent x i j).isSome) :
    ((value x i (j + 1)).get (value_succ_isSome_iff_parent_isSome.mpr h)).val =
      let p := (parentAsIndex h).val
      ((value x i j).get (value_isSome_of_parent_isSome h)).val -
        ((value x p j).get (value_parent_isSome_of_parent_isSome h)).val :=
  by simp [h, value_parent_lt_value, PNat.sub_coe]

theorem value_above_lt_value_of_parent_isSome {x : ValueParentListPair} {i : Index x.values.val}
    {j : ℕ} (h : (parent x i j).isSome) :
    ((value x i (j + 1)).get (value_succ_isSome_iff_parent_isSome.mpr h)).val <
      ((value x i j).get (value_isSome_of_parent_isSome h)).val :=
  by
  rw [get_value_above_eq_of_parent_isSome h]
  exact Nat.sub_lt (PNat.pos _) (PNat.pos _)

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
      simp only [WithBot.some_eq_coe, WithBot.coe_le_coe, value_succ, ↓reduceDite, PNat.coe_lt_coe,
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
      forall_apply_eq_imp_iff, List.map_eq_nil, List.finRange_eq_nil]
    intro
    exact ne_of_gt (height_pos ..)


theorem mountain_length_eq (x : ValueParentListPair) :
    (buildMountain x).values.val.length = x.values.val.length := by simp [buildMountain]

theorem mountain_height_eq (x : ValueParentListPair) (i : Index (buildMountain x).values.val) :
    i.get.length = height x (Pairable.transfer (mountain_length_eq x) i) := by
  simp [Pairable.transfer, Index.get, buildMountain]

theorem mountain_height_eq' (x : ValueParentListPair) (i : Index x.values.val) :
    (Pairable.transfer (mountain_length_eq x).symm i).get.length = height x i := by
  simp [mountain_height_eq, Pairable.transfer, buildMountain]

theorem mountain_value_at_index_eq_value (x : ValueParentListPair)
    (q : Index₂ (buildMountain x).values.val) :
    q.get = (value x (Pairable.transfer (mountain_length_eq x) q.fst) q.val.snd).get
      (by
        apply value_isSome_of_lt_height
        rw [← mountain_height_eq]
        exact q.val_snd_lt) :=
  by
  simp [Index₂.get, Index.get, buildMountain] at q ⊢
  rw [List.get_eq_iff, Option.eq_some_iff_get_eq]
  simp only [List.get_map, List.get_finRange, List.get?_map, Option.get_map, Option.isSome_map]
  constructor
  · congr 2
    conv_lhs =>
      congr
      congr
      rw [List.get?_eq_get (by convert q.snd.isLt; simp [Index.get])]
    simp
  · rw [Option.isSome_iff_exists]
    constructor
    rw [List.get?_eq_some]
    refine ⟨?_, rfl⟩
    convert q.snd.isLt
    simp [Index.get]

theorem mountain_parent_at_index_eq_parent (x : ValueParentListPair)
    (q : Index₂ (buildMountain x).parents.val) :
    q.get =
      parent x
        (Pairable.transfer ((buildMountain x).pairable.fst.symm.trans (mountain_length_eq x)) q.fst)
        q.val.snd :=
  by
  simp [Index₂.get, Index.get, buildMountain] at q ⊢
  rw [List.get_eq_iff, Option.eq_some_iff_get_eq]
  simp only [List.get_map, List.get_finRange, List.get?_map, Option.get_map, Option.isSome_map]
  constructor
  · congr 1
    conv_lhs =>
      congr
      congr
      rw [List.get?_eq_get (by convert q.snd.isLt; simp [Index.get])]
    simp
  · rw [Option.isSome_iff_exists]
    constructor
    rw [List.get?_eq_some]
    refine ⟨?_, rfl⟩
    convert q.snd.isLt
    simp [Index.get]

theorem mountain_parents_isCoherent (x : ValueParentListPair) :
    (buildMountain x).parents.IsCoherent :=
  by
  rintro ⟨i, j⟩
  dsimp
  refine' ⟨_, _, _⟩
  · rw [mountain_parent_at_index_eq_parent, ← value_succ_eq_none_iff_parent_eq_none,
      value_eq_none_iff_height_le]
    simp [Pairable.transfer]
    rw [Nat.le_add_one_iff]
    conv in height _ _ = j.val + 1 =>
      rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt (height_pos _ _))]
    have iheight :=
      Eq.trans ((buildMountain x).pairable.snd _).symm
        (mountain_height_eq _ ((buildMountain x).pairable.fst.symm.transfer i))
    simp [Pairable.transfer] at iheight
    rw [← iheight, eq_comm, add_left_inj, or_iff_right_iff_imp]
    intro h
    exact absurd j.isLt (not_lt_of_le h)
  · refine' lt_of_eq_of_lt _ (toNoneOrLtId_parent x j.val i.val)
    symm
    simp only [inIndexElim]
    rw [dite_eq_iff', and_iff_left]
    swap
    · intro h
      refine' absurd (lt_of_lt_of_eq i.isLt _) h
      exact (buildMountain x).pairable.fst.symm.trans (mountain_length_eq x)
    intro
    rw [mountain_parent_at_index_eq_parent]
    rfl
  · cases' h : Index₂.get _ with k
    · trivial
    · rw [mountain_parent_at_index_eq_parent] at h
      have parent_isSome := Option.isSome_iff_exists.mpr ⟨k, h⟩
      let q := parentAsIndex parent_isSome
      let p := q.val
      refine'
        ⟨⟨Pairable.transfer ((mountain_length_eq x).symm.trans (buildMountain x).pairable.fst) p,
            ⟨j.val, _⟩⟩,
          _⟩
      · apply Eq.subst ((mountain_height_eq' x _).symm.trans ((buildMountain x).pairable.snd _))
        rw [← value_isSome_iff_lt_height]
        exact value_parent_isSome_of_parent_isSome parent_isSome
      · have hp := q.property
        simp only [h, Option.get_some] at hp
        exact Prod.ext hp rfl

theorem mountain_orphanless_isOrphanless {x : ValueParentListPair} (h : x.IsOrphanless) :
    (buildMountain x).IsOrphanless := by
  rintro ⟨i, hi⟩
  simp [mountain_value_at_index_eq_value, mountain_parent_at_index_eq_parent, Pairable.transfer,
    findIterateOfToNoneOrLtId]
  intro value_gt_one
  rw [findIterate_isSome_iff]
  simp
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
      rw [inIndexElim_yes]
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
      rw [inIndexElim_yes]
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

end Build

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
    · specialize IH (descend hP q) <|
        by
        simp [r, h]
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
      (fun p => Finset.decidableMem' p <|
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
  refine' ⟨_, Option.isSome_iff_exists.mpr ⟨_, hi'j'⟩, _⟩
  have hi'j' := hi'j'
  dsimp [findIterateOfIterateEventuallyNone] at hi'j'
  conv in (occs := *) (_^[_] _) => erw [hi'j']
  dsimp
  clear hi'j'
  constructor
  · exact Option.eq_some_iff_get_eq.mp hi' |>.snd.symm
  · have := hi'j' ▸ findIterate_spec ..
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
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
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
      have :=
        toNoneOrLtId_inIndexElim_yes_none_forall_index_of _
          (to_none_or_lt_diagonal_preparent h_coherent)
      rintro ⟨i, hi⟩
      simp [Index.get]
      exact this _⟩
  pairable := by simp [Pairable]; exact x.pairable.fst

theorem diagonal_length_eq {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) :
    (diagonal h_coherent h_orphanless).values.val.length = x.values.val.length := by simp [diagonal]

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
            (((diagonal h_coherent h_orphanless).pairable.symm.trans
                  (diagonal_length_eq h_coherent h_orphanless)).trans
              x.pairable.fst)
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
                by
                rw [← List.length_pos_iff_ne_nil] at ne_nil ⊢
                rwa [mountain_length_eq, diagonal_length_eq]⟩
              (by
                simp [Function.onFun, mountain_value_at_index_eq_value, Pairable.transfer_last]
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
        (by
          rw [← List.length_pos_iff_ne_nil] at ne_nil ⊢
          rwa [mountain_length_eq, diagonal_length_eq])
        (mountain_orphanless_isCoherent (diagonal_isOrphanless _ _))) :=
  by
  rw [diagonalRec, diagonalRec, WellFounded.fix_eq]
  simp [h_surface]

theorem diagonalRec_eq_dite :
    diagonalRec base rec ne_nil h_coherent =
      if h_surface : surfaceAt (Index.last ne_nil) = 1 then base ne_nil h_coherent h_surface
      else rec ne_nil h_coherent h_surface (diagonalRec base rec
        (by
          rw [← List.length_pos_iff_ne_nil] at ne_nil ⊢
          rwa [mountain_length_eq, diagonal_length_eq])
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

/-- `@badroot x _ _` contains (↓BadRoot(x),↓BadRootHeight(x)) -/
def badroot : ∀ {x : Mountain}, x.values.val ≠ [] → x.IsCoherent → Option (Index₂ x.values.val) :=
  diagonalRec (C := fun x => Option (Index₂ x.values.val))
    (fun x ne_nil h_coherent _ =>
      if h_last_length : (x.pairable.fst.transfer (Index.last ne_nil)).get.length = 1 then none
      else
        have h_parent_isCoherent := h_coherent.to_isCrossCoherent.to_parent_isCoherent
        some <| x.pairable.symm.transfer <| Subtype.val <| h_parent_isCoherent.indexParentOfIsSome
          (q :=
            ⟨x.pairable.fst.transfer (Index.last ne_nil),
              ⟨(x.pairable.fst.transfer (Index.last ne_nil)).get.length - 2,
                Nat.sub_lt
                  (List.length_pos_of_ne_nil (x.parents.index_get_ne_nil _))
                  two_pos⟩⟩)
          (by
            rw [h_parent_isCoherent.get_isSome_iff]
            simp
            apply Nat.ne_of_lt
            apply Nat.sub_succ_lt_self
            rw [Nat.one_lt_iff_ne_zero_and_ne_one]
            exact
              ⟨Ne.symm <| ne_of_lt <| List.length_pos_of_ne_nil <| x.parents.index_get_ne_nil _,
                h_last_length⟩))
    (by
      intro x ne_nil h_coherent _ p
      exact
        p.map fun p =>
          let i : Index x.values.val :=
            Pairable.transfer (by rw [Pairable, mountain_length_eq, diagonal_length_eq]) p.fst
          ⟨i, Index.last (x.values.index_get_ne_nil _)⟩)

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
      have h_parent_isCoherent := h_coherent.to_isCrossCoherent.to_parent_isCoherent
      some <| x.pairable.symm.transfer <| Subtype.val <|
        h_parent_isCoherent.indexParentOfIsSome
          (q :=
            ⟨x.pairable.fst.transfer (Index.last ne_nil),
              ⟨(x.pairable.fst.transfer (Index.last ne_nil)).get.length - 2,
                Nat.sub_lt (List.length_pos_of_ne_nil (x.parents.index_get_ne_nil _)) two_pos⟩⟩) <|
          by
            rw [h_parent_isCoherent.get_isSome_iff]
            simp
            apply Nat.ne_of_lt
            apply Nat.sub_succ_lt_self
            rw [Nat.one_lt_iff_ne_zero_and_ne_one]
            exact
              ⟨Ne.symm <| ne_of_lt <| List.length_pos_of_ne_nil <| x.parents.index_get_ne_nil _,
                h_last_length⟩ :=
  by rw [badroot, diagonalRec_eq_dite]; split_ifs; rfl

theorem badroot_of_last_surface_ne_one {x : Mountain} (ne_nil : x.values.val ≠ [])
    (h_coherent : x.IsCoherent) (h_surface : surfaceAt (Index.last ne_nil) ≠ 1) :
    badroot ne_nil h_coherent =
      (badroot
          (x := buildMountain
            (diagonal h_coherent.to_isCrossCoherent.to_parent_isCoherent
              h_coherent.to_isOrphanless))
          (by
            rw [← List.length_pos_iff_ne_nil] at ne_nil ⊢
            rwa [mountain_length_eq, diagonal_length_eq])
          (mountain_orphanless_isCoherent (diagonal_isOrphanless _ _))
        |>.map fun p =>
          let i : Index x.values.val :=
            Pairable.transfer (by rw [Pairable, mountain_length_eq, diagonal_length_eq]) p.fst
          ⟨i, Index.last (x.values.index_get_ne_nil _)⟩) :=
  by rw [badroot, diagonalRec_of_surface_ne_one (h_surface := h_surface)]; rfl

/-- 𝕄ᴸ = {x : Mountain // x.IsLimit} -/
def Mountain.IsLimit (x : Mountain) : Prop :=
  ∃ (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent), (badroot ne_nil h_coherent).isSome

theorem Mountain.IsLimit.badroot_isSome {x : Mountain} (h : x.IsLimit) :
    (badroot h.fst h.snd.fst).isSome :=
  h.snd.snd

theorem Mountain.IsLimit.iff_last_length_ne_one {x : Mountain} (ne_nil : x.values.val ≠ [])
    (h_coherent : x.IsCoherent) :
    x.IsLimit ↔ (x.pairable.fst.transfer (Index.last ne_nil)).get.length ≠ 1 :=
  by
  constructor
  · intro h H
    exact absurd h.badroot_isSome <| Option.not_isSome_iff_eq_none.mpr <|
      badroot_of_last_height_eq_one ne_nil h_coherent H
  · refine diagonalRec ?base ?rec ne_nil h_coherent
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

end Badroot

end Ysequence
