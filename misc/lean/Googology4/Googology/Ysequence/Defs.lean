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
    DecidablePred <| Option.elim' p q := by intro o; cases o <;> simp <;> infer_instance

instance Option.CasesOn.decidable (o : Option α) (p : Prop) [Decidable p] (q : α → Prop)
    [DecidablePred q] : Decidable <| Option.casesOn o p q := by cases o <;> simp <;> infer_instance

instance Option.CasesOn.decidablePred (p : Prop) [Decidable p] (q : α → Prop) [DecidablePred q] :
    DecidablePred fun o => Option.casesOn o p q := by intro o; cases o <;> simp <;> infer_instance

instance (r : α → α → Prop) [DecidableRel r] : DecidablePred <| Function.uncurry r := by
  rw [Function.uncurry]; infer_instance

def IterateEventuallyNone (f : α → Option α) : Prop :=
  ∀ x : Option α, ∃ k : ℕ, (flip bind f^[k]) x = none

theorem iterateEventuallyNone_or_mem_of_iterateEventuallyNone {f : α → Option α}
    (hf : IterateEventuallyNone f) (p : Set α) (x : α) :
    ∃ k : ℕ, Option.elim' True p <| flip bind f^[k] <| some x :=
  by
  rcases hf (some x) with ⟨k, hk⟩
  use k
  rw [hk]
  triv

def findIndexIterateOfIterateEventuallyNone {f : α → Option α} (hf : IterateEventuallyNone f)
    {p : Set α} (decidable_p : DecidablePred p) : α → ℕ := fun x =>
  Nat.find (iterateEventuallyNone_or_mem_of_iterateEventuallyNone hf p x)

theorem find_index_iterate_spec {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) :
    Option.elim' True p <|
      flip bind f^[findIndexIterateOfIterateEventuallyNone hf decidable_p x] <| some x :=
  Nat.find_spec (iterateEventuallyNone_or_mem_of_iterateEventuallyNone hf p x)

theorem find_index_iterate_min {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) {k : ℕ} :
    k < findIndexIterateOfIterateEventuallyNone hf decidable_p x →
      ¬(Option.elim' True p <| flip bind f^[k] <| some x) :=
  Nat.find_min (iterateEventuallyNone_or_mem_of_iterateEventuallyNone hf p x)

theorem find_index_iterate_eq_iff {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) (k : ℕ) :
    findIndexIterateOfIterateEventuallyNone hf decidable_p x = k ↔
      (Option.elim' True p <| flip bind f^[k] <| some x) ∧
        ∀ l < k, ¬(Option.elim' True p <| flip bind f^[l] <| some x) :=
  Nat.find_eq_iff (iterateEventuallyNone_or_mem_of_iterateEventuallyNone hf p x)

def findIterateOfIterateEventuallyNone {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) : α → Option α := fun x =>
  flip bind f^[findIndexIterateOfIterateEventuallyNone hf decidable_p x] <| some x

theorem find_iterate_spec {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) :
    Option.elim' True p <| findIterateOfIterateEventuallyNone hf decidable_p x :=
  find_index_iterate_spec _ _ _

theorem find_iterate_isSome_iff {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) :
    (findIterateOfIterateEventuallyNone hf decidable_p x).isSome ↔
      ∃ (k : ℕ) (h : (flip bind f^[k] <| some x).isSome), Option.get h ∈ p :=
  by
  constructor
  · intro h
    refine' ⟨_, h, _⟩
    obtain ⟨y, hy⟩ := option.is_some_iff_exists.mp h
    conv in Option.get _ =>
      congr
      change find_iterate_of_iterate_eventually_none hf decidable_p x
    have := find_iterate_spec hf decidable_p x
    simp_rw [hy] at this ⊢
    exact this
  · intro h
    rcases h with ⟨k, hk₁, hk₂⟩
    by_contra H
    apply @find_index_iterate_min _ _ hf _ decidable_p x k
    · clear hk₂
      contrapose hk₁ with H'
      rw [not_lt] at H'
      refine' Nat.le_induction H _ k H'
      intro k _ IH
      rw [Option.not_isSome_iff_eq_none] at IH ⊢
      rw [Function.iterate_succ_apply', IH]
      rfl
    · obtain ⟨y, hy⟩ := option.is_some_iff_exists.mp hk₁
      simp_rw [hy] at hk₂ ⊢
      exact hk₂

theorem find_iterate_eq_none_iff {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) :
    findIterateOfIterateEventuallyNone hf decidable_p x = none ↔
      ∀ {k : ℕ} (h : (flip bind f^[k] <| some x).isSome), Option.get h ∉ p :=
  by
  rw [← not_iff_not]
  push_neg
  rw [Option.ne_none_iff_isSome]
  exact find_iterate_is_some_iff _ _ _

theorem find_index_iterate_pos_of_not_mem {f : α → Option α} (hf : IterateEventuallyNone f)
    {p : Set α} (decidable_p : DecidablePred p) {x : α} (hn : x ∉ p) :
    0 < findIndexIterateOfIterateEventuallyNone hf decidable_p x :=
  by
  rw [pos_iff_ne_zero]
  intro H
  have := find_index_iterate_spec hf decidable_p x
  rw [H] at this
  contradiction

def ToNoneOrLtId (f : ℕ → Option ℕ) : Prop :=
  ∀ n : ℕ, WithBot.hasLt.lt (f n) n

theorem iterateEventuallyNone_of_toNoneOrLtId {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) :
    IterateEventuallyNone f :=
  by
  refine' fun n => @IsWellFounded.induction _ with_bot.has_lt.lt IsWellOrder.to_isWellFounded _ n _
  intro n IH
  cases' n with n
  · exact ⟨0, rfl⟩
  · choose! k h using IH
    exact ⟨k (f n) + 1, h _ (hf n)⟩

def findIterateOfToNoneOrLtId {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) {p : Set ℕ}
    (decidable_p : DecidablePred p) : ℕ → Option ℕ :=
  findIterateOfIterateEventuallyNone (iterateEventuallyNone_of_toNoneOrLtId hf) decidable_p

theorem iterate_bind_none (f : α → Option α) (n : ℕ) : (flip bind f^[n]) none = none :=
  flip n.recOn (by intro n IH; simpa only [Function.iterate_succ_apply', IH]) rfl

theorem toNoneOrLtId_iterate_succ {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) (n k : ℕ) :
    WithBot.hasLt.lt (flip bind f^[k + 1] <| some n : Option ℕ) n :=
  by
  induction' k with k IH
  · exact hf n
  · rw [Function.iterate_succ_apply']
    cases' flip bind f^[k + 1] <| some n with l
    · exact WithBot.bot_lt_coe n
    · exact lt_trans (hf l) IH

theorem toNoneOrLtId_iterate_pos {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) (n : ℕ) {k : ℕ}
    (hk : 0 < k) : WithBot.hasLt.lt (flip bind f^[k] <| some n : Option ℕ) n :=
  by
  cases k
  · exact absurd hk (by decide)
  · exact to_none_or_lt_id_iterate_succ hf n k

theorem toNoneOrLtId_find_iterate_of_not_mem {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) {p : Set ℕ}
    (decidable_p : DecidablePred p) {n : ℕ} (hn : n ∉ p) :
    WithBot.hasLt.lt (findIterateOfToNoneOrLtId hf decidable_p n : Option ℕ) n :=
  toNoneOrLtId_iterate_pos hf _ (find_index_iterate_pos_of_not_mem _ _ hn)

theorem toNoneOrLtId_find_iterate_of_all_not_mem {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f)
    {g : ℕ → Set ℕ} (hg₁ : ∀ n, DecidablePred <| g n) (hg₂ : ∀ n, n ∉ g n) :
    ToNoneOrLtId fun n => findIterateOfToNoneOrLtId hf (hg₁ n) n := fun n =>
  toNoneOrLtId_find_iterate_of_not_mem hf (hg₁ n) (hg₂ n)

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

def Index (s : List α) : Type :=
  Fin s.length

def Index.index {s : List α} (i : Index s) : ℕ :=
  i.val

def Index.val {s : List α} (i : Index s) : α :=
  s.nthLe i.Index i.property

def Pairable (s : List α) (t : List β) : Prop :=
  s.length = t.length

theorem Index.index_lt {s : List α} (i : Index s) : i.Index < s.length :=
  i.property

theorem Index.eq_of_index_eq {s : List α} {i : Index s} {i' : Index s} :
    i.Index = i'.Index → i = i' :=
  Fin.eq_of_veq

theorem Index.index_eq_of_eq {s : List α} {i : Index s} {i' : Index s} :
    i = i' → i.Index = i'.Index :=
  Fin.veq_of_eq

theorem Index.ne_of_index_ne {s : List α} {i : Index s} {i' : Index s} :
    i.Index ≠ i'.Index → i ≠ i' :=
  Fin.ne_of_vne

theorem Index.index_ne_of_ne {s : List α} {i : Index s} {i' : Index s} :
    i ≠ i' → i.Index ≠ i'.Index :=
  Fin.vne_of_ne

@[simp]
theorem Index.eta {s : List α} (i : Index s) (h : i.Index < s.length) :
    (⟨i.Index, h⟩ : Index s) = i :=
  Fin.eta _ _

@[ext]
theorem Index.ext {s : List α} {i : Index s} {i' : Index s} : i.Index = i'.Index → i = i' :=
  Fin.ext

theorem Index.ext_iff {s : List α} {i : Index s} {i' : Index s} : i = i' ↔ i.Index = i'.Index :=
  Fin.ext_iff

theorem Index.index_injective {s : List α} : Function.Injective <| @Index.index _ s :=
  Fin.val_injective

theorem Index.eq_iff_index_eq {s : List α} (i : Index s) (i' : Index s) :
    i = i' ↔ i.Index = i'.Index :=
  Fin.eq_iff_veq _ _

theorem Index.ne_iff_index_ne {s : List α} (i : Index s) (i' : Index s) :
    i ≠ i' ↔ i.Index ≠ i'.Index :=
  Fin.ne_iff_vne _ _

@[simp]
theorem Index.mk_eq_mk {s : List α} {i : ℕ} {h : i < s.length} {i' : ℕ} {h' : i' < s.length} :
    (⟨i, h⟩ : Index s) = ⟨i', h'⟩ ↔ i = i' :=
  Fin.mk_eq_mk

theorem Index.eq_mk_iff_index_eq {s : List α} {i : Index s} {i' : ℕ} {h : i' < s.length} :
    i = ⟨i', h⟩ ↔ i.Index = i' :=
  Fin.eq_mk_iff_val_eq

@[simp]
theorem Index.index_mk {s : List α} {i : ℕ} (h : i < s.length) : Index.index ⟨i, h⟩ = i :=
  Fin.val_mk _

theorem Index.mk_index {s : List α} (i : Index s) : (⟨i.Index, i.property⟩ : Index s) = i :=
  Fin.mk_val _

theorem Index.hEq_ext_iff {s : List α} {t : List β} (h : Pairable s t) {i : Index s}
    {i' : Index t} : HEq i i' ↔ i.Index = i'.Index :=
  Fin.heq_ext_iff h

theorem Index.eq_val_of_base_eq_of_hEq {s t : List α} (h : s = t) {i : Index s} {i' : Index t} :
    HEq i i' → i.val = i'.val := by subst h; rw [index.heq_ext_iff rfl, ← index.eq_iff_index_eq];
  exact congr_arg _

theorem Index.exists_iff {s : List α} {p : Index s → Prop} :
    (∃ i : Index s, p i) ↔ ∃ (i : ℕ) (h : i < s.length), p ⟨i, h⟩ :=
  Fin.exists_iff

theorem Index.forall_iff {s : List α} {p : Index s → Prop} :
    (∀ i : Index s, p i) ↔ ∀ (i : ℕ) (h : i < s.length), p ⟨i, h⟩ :=
  Fin.forall_iff

theorem Index.val_mem {s : List α} (i : Index s) : i.val ∈ s :=
  List.nthLe_mem _ _ _

theorem Index.index_ne_pred_length_iff {s : List α} {i : Index s} :
    i.Index ≠ s.length - 1 ↔ i.Index < s.length - 1 :=
  ne_iff_lt_iff_le.mpr (Nat.le_pred_of_lt i.index_lt)

def Index.last {s : List α} (h : s ≠ []) : Index s :=
  ⟨s.length - 1, Nat.sub_lt (List.length_pos_of_ne_nil h) (Nat.succ_pos 0)⟩

@[simp]
theorem Index.last_index {s : List α} (h : s ≠ []) : (Index.last h).Index = s.length - 1 :=
  rfl

instance (s : List α) : Fintype (Index s) :=
  Fin.fintype _

def inIndexElim {s : List α} (f : Index s → β) (g : β) (i : ℕ) : β :=
  if h : i < s.length then f ⟨i, h⟩ else g

@[simp]
theorem inIndexElim_yes {s : List α} (f : Index s → β) (g : β) (i : Index s) :
    inIndexElim f g i.Index = f i := by simp [in_index_elim, i.index_lt]

@[simp]
theorem inIndexElim_no {s : List α} (f : Index s → β) (g : β) (i : ℕ)
    (h : ¬∃ i' : Index s, i'.Index = i) : inIndexElim f g i = g := by
  simp [in_index_elim, fun h' => h ⟨⟨i, h'⟩, rfl⟩]

theorem toNoneOrLtId_inIndexElim_yes_none_of_forall_index {s : List α} (f : Index s → Option ℕ)
    (h : ∀ i : Index s, WithBot.hasLt.lt (f i) i.Index) : ToNoneOrLtId (inIndexElim f none) :=
  by
  intro i
  rw [in_index_elim]
  split_ifs with h'
  · exact h ⟨i, h'⟩
  · exact WithBot.bot_lt_coe i

theorem toNoneOrLtId_inIndexElim_yes_none_forall_index_of {s : List α} (f : Index s → Option ℕ)
    (h : ToNoneOrLtId (inIndexElim f none)) : ∀ i : Index s, WithBot.hasLt.lt (f i) i.Index :=
  by
  intro i
  specialize h i.index
  rw [in_index_elim_yes] at h
  exact h

theorem not_map_is_some_and_lt_same {s : List α} (f : Index s → Option ℕ+) (i : Index s) :
    i.Index ∉
      (Finset.image Index.index <|
          Finset.univ.filterₓ fun j : Index s =>
            Option.casesOn (Prod.mk <$> f j <*> f i) False (Function.uncurry (· < ·)) :
        Set ℕ) :=
  by
  dsimp
  simp
  intro j hj
  contrapose! hj
  rw [← index.eq_iff_index_eq] at hj
  rw [hj]
  cases f i <;> dsimp [(· <*> ·)]
  · exact not_false
  · exact irrefl _

theorem Pairable.def {s : List α} {t : List β} : Pairable s t → s.length = t.length :=
  id

theorem Pairable.refl (s : List α) : Pairable s s :=
  Eq.refl _

theorem Pairable.symm {s : List α} {t : List β} : Pairable s t → Pairable t s :=
  symm

theorem Pairable.trans {s : List α} {t : List β} {u : List γ} :
    Pairable s t → Pairable t u → Pairable s u :=
  Eq.trans

def Pairable.transfer {s : List α} {t : List β} (h : Pairable s t) (i : Index s) : Index t :=
  ⟨i.Index, lt_of_lt_of_eq i.property h⟩

@[simp]
theorem Pairable.index_transfer {s : List α} {t : List β} (h : Pairable s t) (i : Index s) :
    (h.transfer i).Index = i.Index :=
  rfl

theorem Pairable.transfer_last {s : List α} {t : List β} (h : Pairable s t) (ne_nil : s ≠ []) :
    h.transfer (Index.last ne_nil) =
      @Index.last _ t (by rw [← List.length_pos_iff_ne_nil] at ne_nil ⊢; exact h.def ▸ ne_nil) :=
  by simpa only [pairable.transfer, index.last, h.def]

instance (s : List α) (t : List β) : Decidable <| Pairable s t :=
  Nat.decidableEq _ _

theorem Pairable.list_ext {s t : List α} (h : Pairable s t)
    (h' : ∀ i : Index s, i.val = (h.transfer i).val) : s = t :=
  by
  apply List.ext_nthLe h
  intro n h₁ h₂
  rw [index.forall_iff] at h'
  exact h' n h₁

def Index₂ (m : List (List α)) : Type :=
  Σ i : Index m, Index <| Index.val i

def Index₂.index {m : List (List α)} (q : Index₂ m) : ℕ × ℕ :=
  (q.fst.Index, q.snd.Index)

def Index₂.val {m : List (List α)} (q : Index₂ m) : α :=
  q.snd.val

def Pairable₂ (m₁ : List (List α)) (m₂ : List (List β)) : Prop :=
  ∃ h : Pairable m₁ m₂, ∀ i : Index m₁, Pairable i.val (h.transfer i).val

theorem Index₂.fst_index_lt {m : List (List α)} (q : Index₂ m) : q.fst.Index < m.length :=
  q.fst.index_lt

theorem Index₂.snd_index_lt {m : List (List α)} (q : Index₂ m) : q.snd.Index < q.fst.val.length :=
  q.snd.index_lt

@[simp]
theorem Index₂.index_fst {m : List (List α)} (q : Index₂ m) : q.Index.fst = q.fst.Index :=
  rfl

@[simp]
theorem Index₂.index_snd {m : List (List α)} (q : Index₂ m) : q.Index.snd = q.snd.Index :=
  rfl

theorem Index₂.eq_of_index_eq {m : List (List α)} {q : Index₂ m} {q' : Index₂ m}
    (h : q.Index = q'.Index) : q = q' :=
  have fst_eq : q.fst = q'.fst :=
    Index.ext (Index₂.index_fst q ▸ Index₂.index_fst q' ▸ congr_arg _ h)
  Sigma.ext fst_eq
    ((Index.hEq_ext_iff
          (congr_arg List.length (Index.eq_val_of_base_eq_of_hEq rfl (hEq_of_eq fst_eq)))).mpr
      (Index₂.index_snd q ▸ Index₂.index_snd q' ▸ congr_arg _ h))

theorem Index₂.index_eq_of_eq {m : List (List α)} {q : Index₂ m} {q' : Index₂ m} :
    q = q' → q.Index = q'.Index :=
  congr_arg _

theorem Index₂.ne_of_index_ne {m : List (List α)} {q : Index₂ m} {q' : Index₂ m} :
    q.Index ≠ q'.Index → q ≠ q' :=
  mt Index₂.index_eq_of_eq

theorem Index₂.index_ne_of_ne {m : List (List α)} {q : Index₂ m} {q' : Index₂ m} :
    q ≠ q' → q.Index ≠ q'.Index :=
  mt Index₂.eq_of_index_eq

@[simp]
theorem Index₂.eta {m : List (List α)} (q : Index₂ m) : (⟨q.fst, q.snd⟩ : Index₂ m) = q :=
  Sigma.eta _

@[ext]
theorem Index₂.ext {m : List (List α)} {q : Index₂ m} {q' : Index₂ m} :
    q.Index = q'.Index → q = q' :=
  Index₂.eq_of_index_eq

@[simp]
theorem Index₂.eta₂ {m : List (List α)} (q : Index₂ m) (h₁ : q.fst.Index < m.length)
    (h₂ : q.snd.Index < (Index.val ⟨q.fst.Index, h₁⟩).length) :
    (⟨⟨q.fst.Index, h₁⟩, ⟨q.snd.Index, h₂⟩⟩ : Index₂ m) = q :=
  Index₂.ext rfl

@[simp]
theorem Index₂.eta₂' {m : List (List α)} (q : Index₂ m) (h₁ : q.fst.Index < m.length)
    (h₂ : q.snd.Index < q.fst.val.length) :
    (⟨⟨q.fst.Index, h₁⟩, ⟨q.snd.Index, (Index.eta q.fst h₁).symm ▸ h₂⟩⟩ : Index₂ m) = q :=
  Index₂.eta₂ _ _ _

theorem Index₂.ext_iff {m : List (List α)} {q : Index₂ m} {q' : Index₂ m} :
    q = q' ↔ q.Index = q'.Index :=
  ⟨Index₂.index_eq_of_eq, Index₂.eq_of_index_eq⟩

theorem Index₂.index_injective {m : List (List α)} : Function.Injective <| @Index₂.index _ m :=
  @Index₂.eq_of_index_eq _ _

theorem Index₂.eq_iff_index_eq {m : List (List α)} (q : Index₂ m) (q' : Index₂ m) :
    q = q' ↔ q.Index = q'.Index :=
  Index₂.ext_iff

theorem Index₂.ne_iff_index_ne {m : List (List α)} (q : Index₂ m) (q' : Index₂ m) :
    q ≠ q' ↔ q.Index ≠ q'.Index :=
  Iff.not Index₂.ext_iff

theorem Index₂.eq_iff_fst_index_eq_and_snd_index_eq {m : List (List α)} (q : Index₂ m)
    (q' : Index₂ m) : q = q' ↔ q.fst.Index = q'.fst.Index ∧ q.snd.Index = q'.snd.Index := by
  simp [index₂.eq_iff_index_eq, Prod.eq_iff_fst_eq_snd_eq]

theorem Index₂.ne_iff_fst_index_ne_or_snd_index_ne {m : List (List α)} (q : Index₂ m)
    (q' : Index₂ m) : q ≠ q' ↔ q.fst.Index ≠ q'.fst.Index ∨ q.snd.Index ≠ q'.snd.Index := by
  rw [Ne.def, index₂.eq_iff_fst_index_eq_and_snd_index_eq]; tauto

theorem Index₂.mk_eq_mk {m : List (List α)} {i : Index m} {j : Index i.val} {i' : Index m}
    {j' : Index i'.val} : (⟨i, j⟩ : Index₂ m) = ⟨i', j'⟩ ↔ i = i' ∧ HEq j j' :=
  Sigma.mk.inj_iff

@[simp]
theorem Index₂.mk_mk_eq_mk_mk {m : List (List α)} {i : ℕ} {hi : i < m.length} {j : ℕ}
    {hj : j < (Index.val ⟨i, hi⟩).length} {i' : ℕ} {hi' : i' < m.length} {j' : ℕ}
    {hj' : j' < (Index.val ⟨i', hi'⟩).length} :
    (⟨⟨i, hi⟩, ⟨j, hj⟩⟩ : Index₂ m) = ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ ↔ (i, j) = (i', j') :=
  by
  simp
  intro i_eq
  refine' index.heq_ext_iff _
  congr
  exact i_eq

theorem Index₂.eq_mk_mk_iff_index_eq {m : List (List α)} {q : Index₂ m} {i' : ℕ}
    {hi' : i' < m.length} {j' : ℕ} {hj' : j' < (Index.val ⟨i', hi'⟩).length} :
    q = ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ ↔ q.Index = (i', j') := by rw [index₂.ext_iff]; rfl

theorem Index₂.index_mk {m : List (List α)} {i : Index m} {j : Index i.val} :
    Index₂.index ⟨i, j⟩ = (i.Index, j.Index) :=
  rfl

@[simp]
theorem Index₂.index_mk_mk {m : List (List α)} {i : ℕ} {hi : i < m.length} {j : ℕ}
    {hj : j < (Index.val ⟨i, hi⟩).length} : Index₂.index ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ = (i, j) :=
  rfl

theorem Index₂.mk_mk_index {m : List (List α)} (q : Index₂ m) :
    (⟨⟨q.fst.Index, q.fst.property⟩, ⟨q.snd.Index, q.snd.property⟩⟩ : Index₂ m) = q :=
  Index₂.eta₂' _ _ q.snd.property

theorem Index₂.exists_iff {m : List (List α)} {p : Index₂ m → Prop} :
    (∃ q : Index₂ m, p q) ↔ ∃ (i : Index m) (j : Index i.val), p ⟨i, j⟩ :=
  Sigma.exists

theorem Index₂.forall_iff {m : List (List α)} {p : Index₂ m → Prop} :
    (∀ q : Index₂ m, p q) ↔ ∀ (i : Index m) (j : Index i.val), p ⟨i, j⟩ :=
  Sigma.forall

theorem Index₂.val_mem {m : List (List α)} (q : Index₂ m) : ∃ c ∈ m, q.val ∈ c :=
  ⟨q.fst.val, Index.val_mem _, Index.val_mem _⟩

instance (m : List (List α)) : Fintype (Index₂ m) :=
  Sigma.fintype _

instance (m₁ : List (List α)) (m₂ : List (List β)) : Decidable <| Pairable₂ m₁ m₂ :=
  existsPropDecidable _

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
theorem Pairable₂.index₂_fst_transfer {m₁ : List (List α)} {m₂ : List (List β)}
    (h : Pairable₂ m₁ m₂) (q : Index₂ m₁) : (h.transfer q).fst.Index = q.fst.Index :=
  rfl

@[simp]
theorem Pairable₂.index₂_snd_transfer {m₁ : List (List α)} {m₂ : List (List β)}
    (h : Pairable₂ m₁ m₂) (q : Index₂ m₁) : (h.transfer q).snd.Index = q.snd.Index :=
  rfl

theorem Pairable₂.list_ext {m₁ m₂ : List (List α)} (h : Pairable₂ m₁ m₂)
    (h' : ∀ q : Index₂ m₁, q.val = (h.transfer q).val) : m₁ = m₂ :=
  by
  apply h.fst.list_ext
  intro i
  apply (h.snd i).list_ext
  intro j
  rw [index₂.forall_iff] at h'
  exact h' i j

@[simp]
theorem Option.seq_none_right {f : Option (α → β)} : f <*> none = none := by cases f <;> rfl

end Intro

section Types

/-- 𝕊 -/
def ValueList : Type :=
  { s : List ℕ+ // if h : 0 < s.length then Index.val (⟨0, h⟩ : Index s) = 1 else True }

/-- ^𝕊 -/
def ParentList : Type :=
  { t : List (Option ℕ) // ∀ i : Index t, WithBot.hasLt.lt i.val i.Index }

theorem ParentList.head_eq_none {t : ParentList} (h : 0 < t.val.length) :
    Index.val (⟨0, h⟩ : Index t.val) = none :=
  (Nat.WithBot.lt_zero_iff _).mp (t.property _)

/-- 𝕊⁽²⁾ -/
structure ValueParentListPair where
  values : ValueList
  parents : ParentList
  Pairable : Pairable values.val parents.val

/-- 𝕊⁽²⁾* = {x : 𝕊⁽²⁾ // x.is_orphanless} -/
def ValueParentListPair.IsOrphanless (x : ValueParentListPair) : Prop :=
  ∀ i : Index x.values.val, 1 < i.val.val → (x.Pairable.transfer i).val.isSome

instance : DecidablePred ValueParentListPair.IsOrphanless := fun x => Fintype.decidableForallFintype

example : { x : ValueParentListPair // ValueParentListPair.IsOrphanless x } :=
  let s : List ℕ+ := [1, 3, 4]
  let t := [none, some 0, some 1]
  ⟨⟨⟨s, by decide⟩, ⟨t, by decide⟩, by decide⟩, by decide⟩

/-- 𝕄ᵥ -/
def ValueMountain : Type :=
  { V : List (List ℕ+) // ∀ c ∈ V, c ≠ [] }

theorem ValueMountain.index_val_ne_nil (V : ValueMountain) (i : Index V.val) : i.val ≠ [] :=
  V.property _ (Index.val_mem i)

/-- 𝕄ₚ⁻ -/
def ParentMountain : Type :=
  { P : List (List (Option ℕ)) // ∀ c ∈ P, c ≠ [] }

theorem ParentMountain.index_val_ne_nil (P : ParentMountain) (i : Index P.val) : i.val ≠ [] :=
  P.property _ (Index.val_mem i)

/-- 𝕄ₚ = {P : 𝕄ₚ⁻ // P.is_coherent} -/
def ParentMountain.IsCoherent (P : ParentMountain) : Prop :=
  ∀ q : Index₂ P.val,
    let i := q.fst.Index
    let j := q.snd.Index
    (q.val = none ↔ j = q.fst.val.length - 1) ∧
      WithBot.hasLt.lt q.val i ∧
        Option.elim' True (fun p => ∃ q' : Index₂ P.val, q'.Index = (p, j)) q.val

theorem ParentMountain.IsCoherent.val_eq_none_iff {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : q.val = none ↔ q.snd.Index = q.fst.val.length - 1 :=
  (hP q).left

theorem ParentMountain.IsCoherent.val_lt {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : WithBot.hasLt.lt q.val q.fst.Index :=
  (hP q).right.left

theorem ParentMountain.IsCoherent.elim'_exists_index {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) :
    Option.elim' True (fun p => ∃ q' : Index₂ P.val, q'.Index = (p, q.snd.Index)) q.val :=
  (hP q).right.right

instance : DecidablePred ParentMountain.IsCoherent := fun P => Fintype.decidableForallFintype

theorem ParentMountain.IsCoherent.val_isSome_iff {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : q.val.isSome ↔ q.snd.Index ≠ q.fst.val.length - 1 :=
  Option.ne_none_iff_isSome.symm.trans (Decidable.not_iff_not.mpr (hP.val_eq_none_iff _))

theorem ParentMountain.IsCoherent.exists_index_of_isSome {P : ParentMountain} (hP : P.IsCoherent)
    {q : Index₂ P.val} (hq : q.val.isSome) :
    ∃ q' : Index₂ P.val, q'.Index = (Option.get hq, q.snd.Index) :=
  by
  have := hP.elim_exists_index q
  rw [← Option.some_get hq] at this
  exact this

theorem ParentMountain.IsCoherent.head_eq_none {P : ParentMountain} (hP : P.IsCoherent)
    (h : 0 < P.val.length) (j : Index (Index.val (⟨0, h⟩ : Index P.val))) :
    Index₂.val (⟨⟨0, h⟩, j⟩ : Index₂ P.val) = none :=
  (Nat.WithBot.lt_zero_iff _).mp (hP.val_lt _)

theorem ParentMountain.IsCoherent.head_length {P : ParentMountain} (hP : P.IsCoherent)
    (h : 0 < P.val.length) : (Index.val (⟨0, h⟩ : Index P.val)).length = 1 :=
  by
  have head_length_pos := List.length_pos_of_ne_nil (P.index_val_ne_nil ⟨0, h⟩)
  rw [← Nat.sub_eq_iff_eq_add head_length_pos]
  exact ((hP.val_eq_none_iff ⟨⟨0, h⟩, ⟨0, head_length_pos⟩⟩).mp (hP.head_eq_none _ _)).symm

def ParentMountain.IsCoherent.indexParentOfIsSome {P : ParentMountain} (hP : P.IsCoherent)
    {q : Index₂ P.val} (hq : q.val.isSome) :
    { q' : Index₂ P.val //
      let i := q.fst.Index
      let j := q.snd.Index
      q'.Index = (Option.get hq, j) } :=
  ⟨⟨⟨Option.get hq, by
        cases' hP.exists_index_of_is_some hq with q' hq'
        rw [index₂.index] at hq'
        simp at hq'
        exact lt_of_eq_of_lt hq'.left.symm q'.fst_index_lt⟩,
      ⟨q.snd.Index, by
        cases' hP.exists_index_of_is_some hq with q' hq'
        rw [index₂.index] at hq'
        simp at hq'
        refine' lt_of_eq_of_lt hq'.right.symm (lt_of_lt_of_eq q'.snd_index_lt _)
        congr
        exact index.eq_of_index_eq hq'.left⟩⟩,
    rfl⟩

def ParentMountain.IsCoherent.indexAboveOfIsSome {P : ParentMountain} (hP : P.IsCoherent)
    {q : Index₂ P.val} (hq : q.val.isSome) :
    { q' : Index₂ P.val //
      let i := q.fst.Index
      let j := q.snd.Index
      q'.Index = (i, j + 1) } :=
  ⟨⟨q.fst,
      ⟨q.snd.Index + 1,
        by
        have h := (not_iff_not.mpr (hP.val_eq_none_iff q)).mp (option.ne_none_iff_is_some.mpr hq)
        rw [lt_iff_le_and_ne]
        constructor
        · exact Nat.succ_le_of_lt q.snd_index_lt
        · rw [← Ne.def, ← Nat.succ_ne_succ] at h
          rw [← Nat.sub_add_cancel (List.length_pos_of_ne_nil (P.index_val_ne_nil _))]
          exact h⟩⟩,
    rfl⟩

/-- 𝕄⁻ -/
structure Mountain where
  values : ValueMountain
  parents : ParentMountain
  Pairable : Pairable₂ values.val parents.val

/-- 𝕄* = {x : mountain // x.parents.is_coherent ∧ x.is_orphanless} -/
def Mountain.IsOrphanless (x : Mountain) : Prop :=
  ∀ i : Index x.values.val,
    1 < (Index₂.val ⟨i, ⟨0, List.length_pos_of_ne_nil (x.values.index_val_ne_nil _)⟩⟩).val →
      (Index₂.val
          ⟨x.Pairable.fst.transfer i,
            ⟨0, List.length_pos_of_ne_nil (x.parents.index_val_ne_nil _)⟩⟩).isSome

instance : DecidablePred Mountain.IsOrphanless := fun x => Fintype.decidableForallFintype

theorem Mountain.base_value_eq_one_of_parents_isCoherent_of_isOrphanless_of_height_eq_one
    {x : Mountain} (h_coherent : x.parents.IsCoherent) (h_orphanless : x.IsOrphanless)
    {i : Index x.values.val} (h : i.val.length = 1) :
    Index₂.val ⟨i, ⟨0, List.length_pos_of_ne_nil (x.values.index_val_ne_nil _)⟩⟩ = 1 :=
  by
  by_contra H
  have := h_orphanless i (by apply lt_of_le_of_ne (PNat.one_le _) (Ne.symm H))
  rw [← Option.ne_none_iff_isSome] at this
  apply this
  rw [h_coherent.val_eq_none_iff]
  conv_rhs =>
    rw [(x.pairable.symm.snd _).def]
    simp only [pairable.transfer]
    erw [h]
  simp

theorem Mountain.head_value_eq_one_of_parents_isCoherent_of_isOrphanless_of_length_pos
    {x : Mountain} (h_coherent : x.parents.IsCoherent) (h_orphanless : x.IsOrphanless)
    (len_pos : 0 < x.values.val.length) :
    Index₂.val ⟨⟨0, len_pos⟩, ⟨0, List.length_pos_of_ne_nil (x.values.index_val_ne_nil _)⟩⟩ = 1 :=
  by
  apply
    mountain.base_value_eq_one_of_parents_is_coherent_of_is_orphanless_of_height_eq_one h_coherent
      h_orphanless
  rw [(x.pairable.snd _).def]
  exact h_coherent.head_length (lt_of_lt_of_eq len_pos x.pairable.fst)

def Mountain.IsCrossCoherent (x : Mountain) : Prop :=
  ∃ hP : x.parents.IsCoherent,
    ∀ {q : Index₂ x.parents.val} (hq : q.val.isSome),
      (x.Pairable.symm.transfer (hP.indexAboveOfIsSome hq).val).val.val =
        (x.Pairable.symm.transfer q).val.val -
          (x.Pairable.symm.transfer (hP.indexParentOfIsSome hq).val).val.val

theorem Mountain.IsCrossCoherent.to_parent_isCoherent {x : Mountain} (h : x.IsCrossCoherent) :
    x.parents.IsCoherent :=
  h.fst

theorem Mountain.IsCrossCoherent.val_value_above_eq_of_parent_isSome {x : Mountain}
    (h : x.IsCrossCoherent) {q : Index₂ x.parents.val} (hq : q.val.isSome) :
    have hP : x.parents.IsCoherent := h.to_parent_isCoherent
    (x.Pairable.symm.transfer (hP.indexAboveOfIsSome hq).val).val.val =
      (x.Pairable.symm.transfer q).val.val -
        (x.Pairable.symm.transfer (hP.indexParentOfIsSome hq).val).val.val :=
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
    (h : x.IsCrossCoherent) {q : Index₂ x.parents.val} (hq : q.val.isSome) :
    have hP : x.parents.IsCoherent := h.to_parent_isCoherent
    (x.Pairable.symm.transfer (hP.indexAboveOfIsSome hq).val).val <
      (x.Pairable.symm.transfer q).val :=
  by
  have := (h.val_value_above_eq_of_parent_is_some hq).symm
  rw [pnat.sub_val_eq_iff_eq_add] at this
  rw [this]
  exact PNat.lt_add_right _ _

theorem Mountain.IsCrossCoherent.value_decrease_upwards {x : Mountain} (h : x.IsCrossCoherent)
    {i : Index x.values.val} {j₁ j₂ : Index i.val} (hj : j₁.Index < j₂.Index) : j₂.val < j₁.val :=
  by
  cases' j₁ with j₁ hj₁
  cases' j₂ with j₂ hj₂
  simp only [Ysequence.Index.index_mk] at hj
  revert j₂ hj hj₁ hj₂
  refine' Nat.le_induction _ _
  · intro hj₁ hj₁'
    have hj₁'' := Nat.pred_lt_pred (Nat.succ_ne_zero _) hj₁'
    change j₁ with index.index ⟨j₁, hj₁⟩ at hj₁''
    rw [Nat.pred_succ, Nat.pred_eq_sub_one, ← index.index_ne_pred_length_iff] at hj₁''
    conv_rhs at hj₁'' => rw [(x.pairable.snd i).def]
    erw [← h.to_parent_is_coherent.val_is_some_iff (x.pairable.transfer ⟨i, ⟨j₁, hj₁⟩⟩)] at hj₁''
    exact h.value_above_lt_value_of_parent_is_some hj₁''
  · intro j₂ hj IH hj₁ hj₂'
    have hj₂ := Nat.lt_trans (Nat.lt_succ_self _) hj₂'
    refine' lt_trans _ (IH _ hj₂)
    have hj₂'' := hj₂'
    change j₂ with index.index ⟨j₂, hj₂⟩ at hj₂''
    rw [← Nat.lt_pred_iff, Nat.pred_eq_sub_one, ← index.index_ne_pred_length_iff] at hj₂''
    conv_rhs at hj₂'' => rw [(x.pairable.snd i).def]
    erw [← h.to_parent_is_coherent.val_is_some_iff (x.pairable.transfer ⟨i, ⟨j₂, hj₂⟩⟩)] at hj₂''
    exact h.value_above_lt_value_of_parent_is_some hj₂''

theorem Mountain.IsCrossCoherent.eq_of_parents_eq_of_value_eq_where_parent_eq_none
    {x₁ x₂ : Mountain} (hx₁ : x₁.IsCrossCoherent) (hx₂ : x₂.IsCrossCoherent)
    (parents_eq : x₁.parents = x₂.parents)
    (value_eq_where_parent_eq_none :
      ∀ q : Index₂ x₁.parents.val,
        q.val = none →
          (x₁.Pairable.symm.transfer q).val =
            (((parents_eq ▸ Pairable₂.refl x₁.parents.val :
                        Pairable₂ x₁.parents.val x₂.parents.val).trans
                    x₂.Pairable.symm).transfer
                q).val) :
    x₁ = x₂ := by
  cases' x₁ with V₁ P₁ hVP₁
  cases' x₂ with V₂ P₂ hVP₂
  dsimp only at *
  subst parents_eq
  rename' P₁ => P
  simp only [and_true_iff, eq_self_iff_true]
  apply Subtype.ext
  apply (hVP₁.trans hVP₂.symm).list_ext
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  induction' i using Nat.strong_induction_on with i IH₁ generalizing j
  obtain ⟨l, hl⟩ :=
    Nat.exists_eq_succ_of_ne_zero
      (ne_of_lt (List.length_pos_of_ne_nil (V₁.index_val_ne_nil ⟨i, hi⟩))).symm
  have hjl : j ≤ l := Nat.le_of_lt_succ (hl ▸ hj)
  have hl' := Nat.pred_eq_of_eq_succ hl
  revert hj
  apply Nat.decreasingInduction' _ hjl
  · clear! j
    intro hj
    apply value_eq_where_parent_eq_none (hVP₁.transfer ⟨⟨i, hi⟩, ⟨l, hj⟩⟩)
    rw [hx₁.to_parent_is_coherent.val_eq_none_iff]
    simp [← hl']
    congr 1
    exact hVP₁.snd _
  · intro j' hj'l hjj' IH₂
    clear! j
    rename' j' => j, hj'l => hjl
    intro hj
    have hj' := lt_of_lt_of_eq hjl (hl'.symm.trans (congr_arg _ (hVP₁.snd _)))
    replace hj' := ne_of_lt hj'
    erw [← hx₁.to_parent_is_coherent.val_is_some_iff (hVP₁.transfer ⟨⟨i, hi⟩, ⟨j, hj⟩⟩)] at hj'
    have lhs_eq := (hx₁.val_value_above_eq_of_parent_is_some hj').symm
    have rhs_eq := (hx₂.val_value_above_eq_of_parent_is_some hj').symm
    rw [pnat.sub_val_eq_iff_eq_add] at lhs_eq rhs_eq
    erw [lhs_eq, rhs_eq]
    congr 1
    · apply IH₂
    · apply IH₁
      simp [parent_mountain.is_coherent.index_parent_of_is_some]
      have := hx₁.to_parent_is_coherent.val_lt (hVP₁.transfer ⟨⟨i, hi⟩, ⟨j, hj⟩⟩)
      simp at this
      obtain ⟨p, hp⟩ := option.is_some_iff_exists.mp hj'
      simp [hp] at this ⊢
      exact with_bot.coe_lt_coe.mp this

theorem Mountain.IsCrossCoherent.value_ne_one_where_parent_isSome {x : Mountain}
    (h : x.IsCrossCoherent) {q : Index₂ x.parents.val} (hq : q.val.isSome) :
    (x.Pairable.symm.transfer q).val ≠ 1 := by
  intro H
  have := h.value_above_lt_value_of_parent_is_some hq
  rw [H] at this
  exact PNat.not_lt_one _ this

theorem Mountain.IsCrossCoherent.parent_eq_none_where_value_eq_one {x : Mountain}
    (h : x.IsCrossCoherent) {q : Index₂ x.values.val} :
    q.val = 1 → (x.Pairable.transfer q).val = none :=
  by
  rw [← Decidable.not_imp_not, ← Ne.def, Option.ne_none_iff_isSome]
  exact h.value_ne_one_where_parent_is_some

/-- 𝕄** = {x : mountain // x.is_orphanless ∧ x.is_coherent} -/
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
      { p : Index x.values.val // p.Index = @Option.get _ (parent i) h }
  parentSpec :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      let p := (@parent_as_index i h).val
      (Option.casesOn (Prod.mk <$> value p <*> value i) False (Function.uncurry (· < ·)) : Prop)
  valueIsSomeOfParentIsSome : ∀ {i : Index x.values.val}, (parent i).isSome → (value i).isSome
  valueParentIsSomeOfParentIsSome :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      let p := (@parent_as_index i h).val
      (value p).isSome

def buildRowBuilder (x : ValueParentListPair) (value : Index x.values.val → Option ℕ+)
    (parent_candidate_next : Index x.values.val → Option ℕ)
    (to_none_or_lt_id_parent_candidate_next :
      ToNoneOrLtId (inIndexElim parent_candidate_next none)) :
    RowBuilder x :=
  let parent : Index x.values.val → Option ℕ := fun i =>
    @findIterateOfToNoneOrLtId (inIndexElim parent_candidate_next none)
      to_none_or_lt_id_parent_candidate_next
      ((Finset.univ.filterₓ fun p : Index x.values.val =>
            Option.casesOn (Prod.mk <$> value p <*> value i) False (Function.uncurry (· < ·))).map
        ⟨Index.index, Index.index_injective⟩)
      (by infer_instance) i.Index
  have to_none_or_lt_id_parent : ToNoneOrLtId (inIndexElim parent none) :=
    by
    apply to_none_or_lt_id_in_index_elim_yes_none_of_forall_index
    intro i
    apply to_none_or_lt_id_find_iterate_of_not_mem
    simp
    intro k
    contrapose!
    intro hk
    rw [index.eq_of_index_eq hk]
    cases value i
    · exact not_false
    · dsimp; exact irrefl _
  let parent_as_index :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      { p : Index x.values.val // p.Index = @Option.get _ (parent i) h } :=
    fun i h =>
    ⟨⟨@Option.get _ (parent i) h, by
        cases' i with i hi
        have parent_i := to_none_or_lt_id_parent i
        simp [in_index_elim, hi] at parent_i
        obtain ⟨p, hp⟩ := option.is_some_iff_exists.mp h
        simp [hp] at parent_i ⊢
        exact lt_trans (with_bot.coe_lt_coe.mp parent_i) hi⟩,
      rfl⟩
  have parent_spec :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      let p := (@parent_as_index i h).val
      (Option.casesOn (Prod.mk <$> value p <*> value i) False (Function.uncurry (· < ·)) : Prop) :=
    by
    intro i h
    obtain ⟨k, hk⟩ := option.is_some_iff_exists.mp h
    rcases@parent_as_index i h with ⟨⟨p, hp₁⟩, hp₂⟩
    simp [hk, index.index] at hp₂
    subst hp₂
    have spec : Option.elim' True _ (parent i) := find_iterate_spec _ _ _
    rw [hk, Option.elim', ← @Set.mem_def _ _ (coe _)] at spec
    simp at spec
    rcases spec with ⟨⟨p', hp'₁⟩, hp'₂, hp'₃⟩
    simp [hk, index.index] at hp'₃
    symm at hp'₃
    subst hp'₃
    exact hp'₂
  have value_is_some_of_parent_is_some :
    ∀ {i : Index x.values.val}, (parent i).isSome → (value i).isSome :=
    by
    intro i h
    specialize parent_spec h
    contrapose parent_spec with H
    rw [Option.not_isSome_iff_eq_none] at H
    delta
    rw [H, option.seq_none_right]
    tauto
  have value_parent_is_some_of_parent_is_some :
    ∀ {i : Index x.values.val} (h : (parent i).isSome),
      let p := (@parent_as_index i h).val
      (value p).isSome :=
    by
    intro i h
    specialize parent_spec h
    contrapose parent_spec with H
    rw [Option.not_isSome_iff_eq_none] at H
    delta
    rw [H]
    tauto
  { value := @value
    parent := @parent
    toNoneOrLtId_parent := @to_none_or_lt_id_parent
    parentAsIndex := @parent_as_index
    parentSpec := @parent_spec
    valueIsSomeOfParentIsSome := @value_is_some_of_parent_is_some
    valueParentIsSomeOfParentIsSome := @value_parent_is_some_of_parent_is_some }

def mountainBuilder (x : ValueParentListPair) : ℕ → RowBuilder x
  | 0 =>
    buildRowBuilder x (some ∘ Index.val) (Index.val ∘ x.Pairable.transfer)
      (by
        apply to_none_or_lt_id_in_index_elim_yes_none_of_forall_index
        intro
        rw [← pairable.index_transfer x.pairable _]
        exact x.parents.property _)
  | j + 1 =>
    let prev := mountain_builder j
    buildRowBuilder x
      (fun i =>
        if h : (prev.parent i).isSome then
          let p :=
            prev.parentAsIndex-- i
              h
          some <|
            @Option.get _ (prev.value i) (prev.valueIsSomeOfParentIsSome h) -
              @Option.get _ (prev.value p) (prev.valueParentIsSomeOfParentIsSome h)
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
    { p : Index x.values.val // p.Index = @Option.get _ (parent x i j) h } :=
  (mountainBuilder x j).parentAsIndex h

theorem parent_spec {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ}
    (h : (parent x i j).isSome) :
    let p := (@parentAsIndex x i j h).val
    (Option.casesOn (Prod.mk <$> value x p j <*> value x i j) False (Function.uncurry (· < ·)) :
      Prop) :=
  (mountainBuilder x j).parentSpec h

theorem value_isSome_of_parent_isSome {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    (parent x i j).isSome → (value x i j).isSome :=
  (mountainBuilder x j).valueIsSomeOfParentIsSome

theorem value_parent_isSome_of_parent_isSome {x : ValueParentListPair} {i : Index x.values.val}
    {j : ℕ} (h : (parent x i j).isSome) :
    let p := (@parentAsIndex x i j h).val
    (value x p j).isSome :=
  (mountainBuilder x j).valueParentIsSomeOfParentIsSome h

theorem value_parent_lt_value {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ}
    (h : (parent x i j).isSome) :
    let p := (@parentAsIndex x i j h).val
    @Option.get _ (value x p j) (value_parent_isSome_of_parent_isSome h) <
      @Option.get _ (value x i j) (value_isSome_of_parent_isSome h) :=
  by
  have spec := parent_spec h
  generalize_proofs hvp₀ hvt₀
  obtain ⟨m, hm⟩ := option.is_some_iff_exists.mp hvp₀
  obtain ⟨n, hn⟩ := option.is_some_iff_exists.mp hvt₀
  simp only [Option.get_some, parent, hm, hn]
  delta at spec
  rw [hm, hn] at spec
  exact spec

theorem parent_of_value_eq_none {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    value x i j = none → parent x i j = none := by contrapose;
  simp_rw [← Ne.def, Option.ne_none_iff_isSome]; exact value_is_some_of_parent_is_some

@[simp]
theorem value_zero (x : ValueParentListPair) (i : Index x.values.val) : value x i 0 = some i.val :=
  rfl

@[simp]
theorem value_succ (x : ValueParentListPair) (i : Index x.values.val) (j : ℕ) :
    value x i (j + 1) =
      if h : (parent x i j).isSome then
        let p := (@parentAsIndex x i j h).val
        some <|
          @Option.get _ (value x i j) (value_isSome_of_parent_isSome h) -
            @Option.get _ (value x p j) (value_parent_isSome_of_parent_isSome h)
      else none :=
  rfl

@[simp]
theorem parent_zero (x : ValueParentListPair) (i : Index x.values.val) :
    parent x i 0 =
      @findIterateOfToNoneOrLtId (inIndexElim (Index.val ∘ x.Pairable.transfer) none)
        (by
          apply to_none_or_lt_id_in_index_elim_yes_none_of_forall_index
          intro
          rw [← pairable.index_transfer x.pairable _]
          exact x.parents.property _)
        ((Finset.univ.filterₓ fun p : Index x.values.val =>
              Option.casesOn (Prod.mk <$> value x p 0 <*> value x i 0) False
                (Function.uncurry (· < ·))).map
          ⟨Index.index, Index.index_injective⟩)
        (by infer_instance) i.Index :=
  rfl

@[simp]
theorem parent_succ (x : ValueParentListPair) (i : Index x.values.val) (j : ℕ) :
    parent x i (j + 1) =
      @findIterateOfToNoneOrLtId (inIndexElim (fun p => parent x p j) none)
        (toNoneOrLtId_parent x j)
        ((Finset.univ.filterₓ fun p : Index x.values.val =>
              Option.casesOn (Prod.mk <$> value x p (j + 1) <*> value x i (j + 1)) False
                (Function.uncurry (· < ·))).map
          ⟨Index.index, Index.index_injective⟩)
        (by infer_instance) i.Index :=
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
  simp_rw [← Ne.def, Option.ne_none_iff_isSome]
  exact value_succ_is_some_iff_parent_is_some

theorem val_value_above_eq_of_parent_isSome {x : ValueParentListPair} {i : Index x.values.val}
    {j : ℕ} (h : (parent x i j).isSome) :
    (@Option.get _ (value x i (j + 1)) (value_succ_isSome_iff_parent_isSome.mpr h)).val =
      let p := (@parentAsIndex x i j h).val
      (@Option.get _ (value x i j) (value_isSome_of_parent_isSome h)).val -
        (@Option.get _ (value x p j) (value_parent_isSome_of_parent_isSome h)).val :=
  by
  generalize_proofs hva₀ hvt₀ hvp₀
  obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := option.is_some_iff_exists.mp hvt₀
  obtain ⟨⟨vp, vp_pos⟩, hvp⟩ := option.is_some_iff_exists.mp hvp₀
  have vp_lt_vt := value_parent_lt_value h
  simp [hvt, hvp, value_succ, -Subtype.val_eq_coe] at vp_lt_vt ⊢
  simp [Option.get_some, h, PNat.sub_coe, vp_lt_vt]

theorem value_above_lt_value_of_parent_isSome {x : ValueParentListPair} {i : Index x.values.val}
    {j : ℕ} (h : (parent x i j).isSome) :
    (@Option.get _ (value x i (j + 1)) (value_succ_isSome_iff_parent_isSome.mpr h)).val <
      (@Option.get _ (value x i j) (value_isSome_of_parent_isSome h)).val :=
  by
  rw [val_value_above_eq_of_parent_is_some]
  generalize_proofs hvt₀ hvp₀
  obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := option.is_some_iff_exists.mp hvt₀
  obtain ⟨⟨vp, vp_pos⟩, hvp⟩ := option.is_some_iff_exists.mp hvp₀
  simp [hvt, hvp, value_succ, -Subtype.val_eq_coe]
  exact Nat.sub_lt vt_pos vp_pos

def height_finite (x : ValueParentListPair) (i : Index x.values.val) :
    ∃ j : ℕ, value x i j = none :=
  by
  refine'
    @WellFounded.induction_bot (WithBot ℕ+) (· < ·) (WithBot.wellFounded_lt IsWellFounded.wf) _ _
      (fun r => ∃ j : ℕ, value x i j = r) _ ⟨0, rfl⟩
  dsimp
  intro a ha IH
  rcases IH with ⟨j, rfl⟩
  refine' ⟨_, _, j + 1, rfl⟩
  have value_succ_eq := value_succ x i j
  split_ifs at value_succ_eq  with h
  · have va_lt_vt := value_above_lt_value_of_parent_is_some h
    generalize_proofs hva₀ hvp₀ at va_lt_vt
    obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := option.is_some_iff_exists.mp hvp₀
    obtain ⟨⟨va, va_pos⟩, hva⟩ := option.is_some_iff_exists.mp hva₀
    simp [*] at va_lt_vt ⊢
    exact va_lt_vt
  · rw [value_succ_eq]
    exact Ne.bot_lt ha

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
  simp at H
  have := height_spec x i
  rw [H] at this
  contradiction

theorem value_eq_none_of_height_le {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ}
    (h : height x i ≤ j) : value x i j = none :=
  by
  refine' Nat.le_induction (height_spec x i) _ j h
  simp
  intro j hj IH H
  exact absurd (parent_of_value_eq_none IH) (option.ne_none_iff_is_some.mpr H)

theorem value_isSome_of_lt_height {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    j < height x i → (value x i j).isSome :=
  Option.ne_none_iff_isSome.mp ∘ height_min

theorem value_isSome_iff_lt_height {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    (value x i j).isSome ↔ j < height x i :=
  ⟨by
    contrapose
    simp
    intro H
    exact option.is_none_iff_eq_none.mpr (value_eq_none_of_height_le H), value_isSome_of_lt_height⟩

theorem value_eq_none_iff_height_le {x : ValueParentListPair} {i : Index x.values.val} {j : ℕ} :
    value x i j = none ↔ height x i ≤ j :=
  by
  rw [← not_iff_not, ← Ne.def, Option.ne_none_iff_isSome, not_le]
  exact value_is_some_iff_lt_height

def buildMountain (x : ValueParentListPair) : Mountain
    where
  values :=
    ⟨(fun i : Index x.values.val =>
          (fun j : Fin (height x i) =>
              @Option.get _ (value x i j.val) (value_isSome_of_lt_height j.property)) <$>
            List.finRange (height x i)) <$>
        List.finRange x.values.val.length,
      by
      intro _ h
      simp at h
      cases' h with i h
      rw [← h, Ne.def, List.map_eq_nil, List.finRange_eq_nil, ← Ne.def]
      exact ne_of_gt (height_pos x i)⟩
  parents :=
    ⟨(fun i : Index x.values.val =>
          (fun j : Fin (height x i) => parent x i j.val) <$> List.finRange (height x i)) <$>
        List.finRange x.values.val.length,
      by
      intro _ h
      simp at h
      cases' h with i h
      rw [← h, Ne.def, List.map_eq_nil, List.finRange_eq_nil, ← Ne.def]
      exact ne_of_gt (height_pos x i)⟩
  Pairable := by simp [pairable₂, pairable, index.val]

theorem mountain_length_eq (x : ValueParentListPair) :
    (buildMountain x).values.val.length = x.values.val.length := by simp [build_mountain]

theorem mountain_height_eq (x : ValueParentListPair) (i : Index (buildMountain x).values.val) :
    i.val.length = height x (Pairable.transfer (mountain_length_eq x) i) := by
  simp [pairable.transfer, index.val, build_mountain, index.index]

theorem mountain_height_eq' (x : ValueParentListPair) (i : Index x.values.val) :
    (Pairable.transfer (mountain_length_eq x).symm i).val.length = height x i := by
  simp [mountain_height_eq, pairable.transfer, build_mountain, index.index]

theorem mountain_value_at_index_eq_value (x : ValueParentListPair)
    (q : Index₂ (buildMountain x).values.val) :
    q.val =
      @Option.get _ (value x (Pairable.transfer (mountain_length_eq x) q.fst) q.snd.Index)
        (by
          apply value_is_some_of_lt_height
          rw [← mountain_height_eq]
          exact q.snd_index_lt) :=
  by simp [pairable.transfer, index₂.val, index.val, build_mountain, index.index]

theorem mountain_parent_at_index_eq_parent (x : ValueParentListPair)
    (q : Index₂ (buildMountain x).parents.val) :
    q.val =
      parent x
        (Pairable.transfer ((buildMountain x).Pairable.fst.symm.trans (mountain_length_eq x)) q.fst)
        q.snd.Index :=
  by simp [pairable.transfer, index₂.val, index.val, build_mountain, index.index]

theorem mountain_parents_isCoherent (x : ValueParentListPair) :
    (buildMountain x).parents.IsCoherent :=
  by
  rintro ⟨i, j⟩
  dsimp
  refine' ⟨_, _, _⟩
  · rw [mountain_parent_at_index_eq_parent, ← value_succ_eq_none_iff_parent_eq_none,
      value_eq_none_iff_height_le]
    simp [pairable.transfer]
    rw [Nat.le_add_one_iff]
    conv in height _ _ = j.index + 1 =>
      rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt (height_pos _ _))]
    have iheight :=
      Eq.trans ((build_mountain x).Pairable.snd _).symm
        (mountain_height_eq _ ((build_mountain x).Pairable.fst.symm.transfer i))
    simp [pairable.transfer, index.index] at iheight
    conv at iheight in coe i => change i.index
    rw [eq_comm, iheight, add_left_inj, or_iff_right_iff_imp]
    rw [← iheight]
    intro h
    exact absurd j.index_lt (not_lt_of_le h)
  · refine' lt_of_eq_of_lt _ (to_none_or_lt_id_parent x j.index i.index)
    symm
    simp only [in_index_elim]
    rw [dite_eq_iff', and_iff_left]
    swap
    · intro h
      refine' absurd (lt_of_lt_of_eq i.index_lt _) h
      exact (build_mountain x).Pairable.fst.symm.trans (mountain_length_eq x)
    intro
    rw [mountain_parent_at_index_eq_parent]
    rfl
  · cases' h : index₂.val _ with k
    · triv
    · rw [mountain_parent_at_index_eq_parent] at h
      have parent_is_some := option.is_some_iff_exists.mpr ⟨k, h⟩
      let q := parent_as_index parent_is_some
      let p := q.val
      refine'
        ⟨⟨pairable.transfer ((mountain_length_eq x).symm.trans (build_mountain x).Pairable.fst) p,
            ⟨j.index, _⟩⟩,
          _⟩
      · apply Eq.subst ((mountain_height_eq' x _).symm.trans ((build_mountain x).Pairable.snd _))
        rw [← value_is_some_iff_lt_height]
        exact value_parent_is_some_of_parent_is_some parent_is_some
      · have hp := q.property
        simp only [h, Option.get_some] at hp
        exact Prod.ext hp rfl

theorem mountain_orphanless_isOrphanless {x : ValueParentListPair} (h : x.IsOrphanless) :
    (buildMountain x).IsOrphanless := by
  rintro ⟨i, hi⟩
  simp [mountain_value_at_index_eq_value, mountain_parent_at_index_eq_parent, pairable.transfer,
    index.index, find_iterate_of_to_none_or_lt_id]
  intro value_gt_one
  have i_has_parent_candidate := h _ value_gt_one
  simp [pairable.transfer, index.index] at i_has_parent_candidate
  rw [find_iterate_is_some_iff]
  dsimp
  simp
  revert i_has_parent_candidate
  rename' i => i₀, hi => hi₀, value_gt_one => value₀_gt_one
  let i₀_on_mv : index _ := ⟨i₀, hi₀⟩
  let i₀_on_lv : index _ := pairable.transfer (mountain_length_eq x) i₀_on_mv
  refine'
    @Nat.strong_induction_on
      (fun i =>
        ∀ hi : _ < _,
          _ < _ →
            Option.isSome _ → ∃ (k : ℕ) (h : Option.isSome _) (p : index _), _ < i₀_on_lv.val ∧ _)
      i₀ _ hi₀ value₀_gt_one
  intro i IH hi value_gt_one i_has_parent_candidate
  let i_on_mv : index _ := ⟨i, hi⟩
  let i_on_lv : index _ := pairable.transfer (mountain_length_eq x) i_on_mv
  let i_on_lp : index _ := pairable.transfer ((mountain_length_eq x).trans x.pairable) i_on_mv
  let p := Option.get i_has_parent_candidate
  have hp := Option.some_get i_has_parent_candidate
  have p_lt_i : p < i := by
    have := x.parents.property i_on_lp
    simp [i_on_lp, pairable.transfer, index.index] at this
    rw [← hp] at this
    exact with_bot.some_lt_some.mp this
  have p_lt_length : p < x.values.val.length :=
    p_lt_i.trans (lt_of_lt_of_eq hi (mountain_length_eq x))
  let p' : index _ := ⟨p, p_lt_length⟩
  by_cases h' : p'.val < i₀_on_lv.val
  on_goal 1 =>
    suffices
    · refine' ⟨1, _, _⟩
      · rw [Option.isSome_iff_exists]
        exact ⟨p, this⟩
      · refine' ⟨p', ⟨h', _⟩⟩
        rw [← Option.some_inj, Option.some_get]
        exact this.symm
  on_goal 2 =>
    rw [not_lt] at h'
    have value_parent_gt_one := lt_of_lt_of_le value₀_gt_one h'
    have p_has_parent_candidate := h _ value_parent_gt_one
    specialize
      IH p p_lt_i (lt_of_lt_of_eq p_lt_length (mountain_length_eq x).symm) value_parent_gt_one
        p_has_parent_candidate
    rcases IH with ⟨k, hk, ⟨tp, ⟨htp₁, htp₂⟩⟩⟩
    suffices
    · refine' ⟨k + 1, _, _⟩
      · rw [Option.isSome_iff_exists]
        exact ⟨tp.index, this⟩
      · refine' ⟨tp, ⟨htp₁, _⟩⟩
        rw [← Option.some_inj, Option.some_get]
        exact this.symm
    rw [← Option.some_inj, Option.some_get] at htp₂
    rw [Function.iterate_succ_apply, htp₂]
    congr
  all_goals
    have := i_on_lv.index_lt
    simp [i_on_lv, i_on_mv, pairable.transfer, index.index] at this
    simp [flip, in_index_elim, this]
    rfl

theorem mountain_orphanless_isCrossCoherent {x : ValueParentListPair} (h : x.IsOrphanless) :
    (buildMountain x).IsCrossCoherent :=
  by
  have hP := mountain_parents_is_coherent x
  use hP
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ hq
  dsimp [pairable₂.transfer, pairable.transfer, index.index,
    parent_mountain.is_coherent.index_above_of_is_some,
    parent_mountain.is_coherent.index_parent_of_is_some]
  simp only [mountain_value_at_index_eq_value, mountain_parent_at_index_eq_parent,
    pairable.transfer, index.index, Option.get_some]
  generalize_proofs hi' hva₀ hvt₀ hp₀ hj' hvp₀
  simp [mountain_parent_at_index_eq_parent, pairable.transfer, index.index] at hq
  obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := option.is_some_iff_exists.mp hvt₀
  obtain ⟨⟨vp, vp_pos⟩, hvp⟩ := option.is_some_iff_exists.mp hvp₀
  obtain ⟨⟨va, va_pos⟩, hva⟩ := option.is_some_iff_exists.mp hva₀
  simp only [hvt, hvp, hva, Option.get_some]
  clear hi' hj' hvt₀ hvp₀ hva₀
  rcases hp : parent_as_index hq with ⟨⟨p, hp₁⟩, hp₂⟩
  simp only [← hp₂, index.index] at hvp
  have vp_lt_vt := value_parent_lt_value hq
  simp [hvt, hp, hvp, Option.get_some] at vp_lt_vt
  have va_eq := val_value_above_eq_of_parent_is_some hq
  simp [hvt, hp, hvp, hva, -Subtype.val_eq_coe] at va_eq
  simp [va_eq, ← PNat.coe_inj, PNat.sub_coe, vp_lt_vt]

theorem mountain_orphanless_isCoherent {x : ValueParentListPair} (h : x.IsOrphanless) :
    (buildMountain x).IsCoherent :=
  ⟨mountain_orphanless_isOrphanless h, mountain_orphanless_isCrossCoherent h⟩

end Build

section Diagonal

def surfaceAt {V : ValueMountain} (i : Index V.val) : ℕ+ :=
  Index₂.val ⟨i, Index.last (V.index_val_ne_nil i)⟩

theorem surfaceAt_lt_base_of_orphanless_of_ne_one {x : Mountain} (h_coherent : x.IsCoherent)
    {i : Index x.values.val} (h_surface : surfaceAt i ≠ 1) :
    surfaceAt i < Index₂.val ⟨i, ⟨0, List.length_pos_of_ne_nil (x.values.index_val_ne_nil _)⟩⟩ :=
  by
  have h_cross_coherent := h_coherent.to_is_cross_coherent
  apply h_cross_coherent.value_decrease_upwards
  simp only [index.last, index.index_mk]
  rw [(x.pairable.snd _).def, tsub_pos_iff_lt, ← Nat.succ_le_iff, Nat.two_le_iff]
  constructor
  · exact (ne_of_lt (List.length_pos_of_ne_nil (x.parents.index_val_ne_nil _))).symm
  · intro H
    have h :=
      h_cross_coherent.to_parent_is_coherent.val_eq_none_iff
        ⟨x.pairable.fst.transfer i, ⟨0, List.length_pos_of_ne_nil (x.parents.index_val_ne_nil _)⟩⟩
    conv at h in _ - 1 => simp only [index.index_mk, H]
    simp at h
    have h' := h_coherent.to_is_orphanless i
    rw [← Decidable.not_imp_not, Option.not_isSome_iff_eq_none, not_lt] at h'
    specialize h' h
    erw [PNat.coe_le_coe _ 1, PNat.le_one_iff] at h'
    rw [surface_at] at h_surface
    conv at h_surface =>
      lhs
      congr
      congr
      rw [index.last]
      congr
      rw [(x.pairable.snd _).def, H]
      simp
    contradiction

def descend {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) : Option (Index₂ P.val) :=
  if h : q.val.isSome then some (hP.indexParentOfIsSome h)
  else
    match q.snd with
    | ⟨0, _⟩ => none
    | ⟨j + 1, h⟩ => some ⟨q.fst, ⟨j, lt_trans (Nat.lt_succ_self j) h⟩⟩

theorem descend_eq_none_iff {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    descend hP q = none ↔ ¬q.val.isSome ∧ q.snd.Index = 0 :=
  by
  rw [descend]
  split_ifs with h
  · simp [h]
  · rcases q.snd with ⟨_ | j, hj⟩ <;> simp [descend, h]

theorem descend_eq_none_iff' {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    descend hP q = none ↔ q.val = none ∧ q.snd.Index = 0 := by
  rw [← @Option.not_isSome_iff_eq_none _ q.val]; exact descend_eq_none_iff hP q

theorem descend_isSome_iff {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    (descend hP q).isSome ↔ q.val.isSome ∨ q.snd.Index ≠ 0 :=
  by
  rw [descend]
  split_ifs with h
  · simp [h]
  · rcases q.snd with ⟨_ | j, hj⟩ <;> simp [descend, h]

theorem descend_lt_and_eq_or_eq_and_lt_of_it_isSome {P : ParentMountain} {hP : P.IsCoherent}
    {q : Index₂ P.val} (h : (descend hP q).isSome) :
    let i := q.fst.Index
    let j := q.snd.Index
    let q' := Option.get h
    let i' := q'.fst.Index
    let j' := q'.snd.Index
    i' < i ∧ j' = j ∨ i' = i ∧ j' < j :=
  by
  intro i j q' i' j'
  have q'_eq := Eq.refl q'
  conv_rhs at q'_eq => simp only [q']
  simp only [descend] at q'_eq
  split_ifs at q'_eq  with hq_val
  · left
    simp only [Option.get_some] at q'_eq
    obtain ⟨k, hk⟩ := option.is_some_iff_exists.mp hq_val
    obtain ⟨p, hp⟩ := hP.index_parent_of_is_some hq_val
    intro q'_eq
    simp only [Subtype.coe_mk] at q'_eq
    subst q'_eq
    simp [hk, Option.get_some, Prod.eq_iff_fst_eq_snd_eq] at hp
    cases' hp with hp₁ hp₂
    have q_val_lt := (hP q).right.left
    rw [hk, ← hp₁, WithBot.some_eq_coe, WithBot.coe_lt_coe] at q_val_lt
    exact ⟨q_val_lt, hp₂⟩
  · rcases q_eq : q with ⟨⟨i₁, hi⟩, ⟨j₁, hj⟩⟩
    have : i = i₁ := congr_arg (fun q : index₂ P.val => q.fst.index) q_eq
    subst this
    have : j = j₁ := congr_arg (fun q : index₂ P.val => q.snd.index) q_eq
    subst this
    conv_rhs at q'_eq =>
      congr
      rw [q_eq]
    cases' hk : j with k
    · generalize_proofs H at q'_eq
      simp [hk, descend, Option.get] at H
      contradiction
    · right
      simp [hk] at q'_eq
      replace q'_eq := congr_arg index₂.index q'_eq
      simp [index₂.index, index.index] at q'_eq
      exact ⟨q'_eq.left, lt_of_eq_of_lt q'_eq.right (lt_add_one k)⟩

theorem descend_pairwise_le_of_it_isSome {P : ParentMountain} {hP : P.IsCoherent} {q : Index₂ P.val}
    (h : (descend hP q).isSome) :
    let i := q.fst.Index
    let j := q.snd.Index
    let q' := Option.get h
    let i' := q'.fst.Index
    let j' := q'.snd.Index
    i' ≤ i ∧ j' ≤ j :=
  by
  rcases descend_lt_and_eq_or_eq_and_lt_of_it_is_some h with (⟨h'₁, h'₂⟩ | ⟨h'₁, h'₂⟩)
  · exact ⟨le_of_lt h'₁, le_of_eq h'₂⟩
  · exact ⟨le_of_eq h'₁, le_of_lt h'₂⟩

theorem descend_pairwise_ne_of_it_isSome {P : ParentMountain} {hP : P.IsCoherent} {q : Index₂ P.val}
    (h : (descend hP q).isSome) : q ≠ Option.get h :=
  by
  intro H
  rcases descend_lt_and_eq_or_eq_and_lt_of_it_is_some h with (⟨h'₁, h'₂⟩ | ⟨h'₁, h'₂⟩)
  · exact absurd (congr_arg (fun q : index₂ P.val => q.fst.index) H.symm) (ne_of_lt h'₁)
  · exact absurd (congr_arg (fun q : index₂ P.val => q.snd.index) H.symm) (ne_of_lt h'₂)

theorem iterate_descend_pairwise_le_of_it_isSome {P : ParentMountain} {hP : P.IsCoherent}
    {q : Index₂ P.val} {k : ℕ} (h : (flip bind (descend hP)^[k] <| some q).isSome) :
    let i := q.fst.Index
    let j := q.snd.Index
    let q' := Option.get h
    let i' := q'.fst.Index
    let j' := q'.snd.Index
    i' ≤ i ∧ j' ≤ j :=
  by
  induction' k with k IH
  · constructor <;> rfl
  · simp_rw [← index₂.index_snd]
    simp only [Function.iterate_succ_apply'] at h ⊢
    suffices
    · specialize IH this
      obtain ⟨q', hq'⟩ := option.is_some_iff_exists.mp this
      simp_rw [← index₂.index_snd] at IH
      simp [hq'] at IH h ⊢
      have h' := descend_pairwise_le_of_it_is_some h
      exact ⟨le_trans h'.left IH.left, le_trans h'.right IH.right⟩
    by_contra H
    rw [Option.not_isSome_iff_eq_none] at H
    rw [H] at h
    contradiction

theorem iterate_descend_succ_ne_of_it_isSome {P : ParentMountain} {hP : P.IsCoherent}
    {q : Index₂ P.val} {k : ℕ} (h : (flip bind (descend hP)^[k + 1] <| some q).isSome) :
    q ≠ Option.get h :=
  by
  have h' : (descend hP q).isSome := by
    induction' k with k IH
    · exact h
    · apply IH
      by_contra H
      rw [Option.not_isSome_iff_eq_none] at H
      rw [Function.iterate_succ_apply', H] at h
      contradiction
  obtain ⟨q', hq'⟩ := option.is_some_iff_exists.mp h'
  have eq_iterate_from := Function.iterate_succ_apply (flip bind (descend hP)) k (some q)
  change flip bind (descend hP) (some q) with descend hP q at eq_iterate_from
  rw [hq'] at eq_iterate_from
  rw [eq_iterate_from] at h
  simp only [eq_iterate_from]
  have hq'₂ := Eq.refl (Option.get h')
  conv_rhs at hq'₂ => simp only [hq', Option.get_some]
  have h₁ := descend_lt_and_eq_or_eq_and_lt_of_it_is_some h'
  rw [hq'₂] at h₁
  have h₂ := iterate_descend_pairwise_le_of_it_is_some h
  rw [Ne, index₂.eq_iff_index_eq, Prod.eq_iff_fst_eq_snd_eq, Decidable.not_and]
  simp
  cases h₁
  · exact Or.inl (ne_of_lt (lt_of_le_of_lt h₂.left h₁.left)).symm
  · exact Or.inr (ne_of_lt (lt_of_le_of_lt h₂.right h₁.right)).symm

theorem descend_finite {P : ParentMountain} (hP : P.IsCoherent) :
    IterateEventuallyNone <| descend hP :=
  by
  refine' fun q =>
    @IsWellFounded.induction (Option (index₂ P.val))
      (with_bot.has_lt.lt on Option.map fun q => q.fst.index + q.snd.index)
      ⟨is_well_founded.wf.on_fun⟩ _ q _
  clear q
  intro q IH
  cases' q with q
  · exact ⟨0, rfl⟩
  · choose! k hk using IH
    cases' h : descend hP q with q'
    · exact ⟨1, h⟩
    · refine' ⟨k (descend hP q) + 1, hk _ _⟩
      simp [h, Function.onFun]
      have h' := descend_lt_and_eq_or_eq_and_lt_of_it_is_some (option.is_some_iff_exists.mpr ⟨_, h⟩)
      simp_rw [← index₂.index_snd] at h'
      simp [h] at h'
      rcases h' with (⟨h'₁, h'₂⟩ | ⟨h'₁, h'₂⟩)
      · simp only [add_lt_add_iff_right, h'₁, h'₂]
      · simp only [add_lt_add_iff_left, h'₁, h'₂]

def descendToSurface {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    Option (Index P.val) :=
  Sigma.fst <$>
    @findIterateOfIterateEventuallyNone _ (descend hP) (descend_finite hP)
      (Finset.univ.filterₓ fun p : Index₂ P.val => p.val = none ∧ p.fst ≠ q.fst) (by infer_instance)
      q

theorem exists_iterate_descend_spec_of_descendToSurface_isSome {P : ParentMountain}
    (hP : P.IsCoherent) (q : Index₂ P.val) (h : (descendToSurface hP q).isSome) :
    ∃ (k : ℕ) (hk : (flip bind (descend hP)^[k] <| some q).isSome),
      (Option.get hk).fst = Option.get h ∧
        (Option.get hk).val = none ∧ (Option.get hk).fst ≠ q.fst :=
  by
  obtain ⟨i', hi'⟩ := option.is_some_iff_exists.mp h
  have hi'₂ := hi'
  simp only [descend_to_surface] at hi'₂
  simp at hi'₂
  cases' hi'₂ with j' hi'j'
  refine' ⟨_, option.is_some_iff_exists.mpr ⟨_, hi'j'⟩, ⟨_, _⟩⟩
  · conv_lhs =>
      congr
      congr
      change find_iterate_of_iterate_eventually_none _ _ q
    simp [hi'j', hi']
  · have : Option.elim' True _ _ := @Eq.subst _ _ _ _ hi'j' (find_iterate_spec _ _ _)
    rw [Option.elim', ← @Set.mem_def _ _ (coe _)] at this
    simp at this
    convert this
    · rw [← Option.some.inj_eq, Option.some_get]
      exact hi'j'
    · conv_lhs =>
        congr
        congr
        change find_iterate_of_iterate_eventually_none _ _ q
      simp [hi'j']

theorem descendToSurface_to_none_or_lt_fst_index {P : ParentMountain} (hP : P.IsCoherent)
    (q : Index₂ P.val) : WithBot.hasLt.lt ((descendToSurface hP q).map Index.index) q.fst.Index :=
  by
  cases h : descend_to_surface hP q
  · exact WithBot.none_lt_some _
  · have h' := option.is_some_iff_exists.mpr ⟨_, h⟩
    obtain ⟨k, hk₁, hk₂⟩ := exists_iterate_descend_spec_of_descend_to_surface_is_some hP q h'
    simp only [h, Option.get_some] at hk₂
    rw [Option.map_some', WithBot.some_eq_coe, WithBot.coe_lt_coe, ← hk₂.left]
    have h'' := iterate_descend_pairwise_le_of_it_is_some hk₁
    exact lt_of_le_of_ne h''.left (index.index_ne_of_ne hk₂.right.right)

theorem descendToSurface_isSome_iff {P : ParentMountain} (hP : P.IsCoherent) (q : Index₂ P.val) :
    (descendToSurface hP q).isSome ↔ 0 < q.snd.Index ∨ q.val.isSome :=
  by
  rw [descend_to_surface, Option.isSome_iff_exists]
  generalize_proofs descend_finite
  generalize fun _ => Finset.decidableMem' _ _ = mem_decidable
  simp
  rw [←
    @index₂.exists_iff _ _ fun q' =>
      find_iterate_of_iterate_eventually_none descend_finite mem_decidable q = some q',
    ← Option.isSome_iff_exists, find_iterate_is_some_iff]
  constructor
  · rintro ⟨k, hk₁, hk₂⟩
    have k_ne_zero : k ≠ 0 := by
      intro H
      subst H
      simp at hk₂
      simp [Set.mem_def] at hk₂
      exact hk₂
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero k_ne_zero
    clear k_ne_zero hk₂
    by_contra H
    rcases q with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    rw [Decidable.not_or_iff_and_not] at H
    cases' H with H' H
    simp [index.index] at H'
    subst H'
    induction' k with k IH
    · simp [flip, descend, H] at hk₁ ; exact hk₁
    · rw [imp_false, Option.not_isSome_iff_eq_none] at IH
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
    have last_is_some := option.ne_none_iff_is_some.mp (hk_lt k (lt_add_one k))
    refine' ⟨k, last_is_some, _⟩
    simp
    rw [Set.mem_def]
    have last_pairwise_le := iterate_descend_pairwise_le_of_it_is_some last_is_some
    dsimp at last_pairwise_le
    generalize hr : Option.get last_is_some = r
    rw [hr] at last_pairwise_le
    have hr' := congr_arg Option.some hr
    rw [Option.some_get] at hr'
    rw [Function.iterate_succ_apply', hr'] at hk_eq
    simp [flip, descend_eq_none_iff'] at hk_eq
    constructor
    · exact hk_eq.left
    · conv at last_pairwise_le =>
        rw [le_iff_lt_or_eq, or_and_right]
        congr
        skip
        rw [le_iff_lt_or_eq, and_or_left]
      rcases last_pairwise_le with (_ | _ | _)
      · exact index.ne_of_index_ne (ne_of_lt last_pairwise_le.left)
      · refine' absurd hk_eq.left ((not_congr (hP.val_eq_none_iff r)).mpr (ne_of_lt _))
        rw [← Nat.pred_eq_sub_one, Nat.lt_pred_iff]
        refine' lt_of_lt_of_le (Nat.succ_lt_succ last_pairwise_le.right) (Nat.succ_le_of_lt _)
        rw [index.eq_of_index_eq last_pairwise_le.left]
        exact q.snd_index_lt
      · rw [← index₂.eq_iff_fst_index_eq_and_snd_index_eq] at last_pairwise_le
        subst last_pairwise_le
        cases h
        · exact absurd hk_eq.right (ne_of_lt h).symm
        · exact absurd hk_eq.left (option.ne_none_iff_is_some.mpr h)

def diagonalPreparentOf {P : ParentMountain} (hP : P.IsCoherent) (i : Index P.val) :
    Option (Index P.val) :=
  descendToSurface hP ⟨i, Index.last (P.index_val_ne_nil i)⟩

theorem diagonalPreparentOf_isSome_iff {P : ParentMountain} (hP : P.IsCoherent) (i : Index P.val) :
    (diagonalPreparentOf hP i).isSome ↔ 1 < i.val.length :=
  by
  simp [diagonal_preparent_of, descend_to_surface_is_some_iff]
  intro h
  exfalso
  rw [← Option.ne_none_iff_isSome] at h
  apply h
  simp [hP.val_eq_none_iff]

theorem to_none_or_lt_diagonal_preparent {P : ParentMountain} (hP : P.IsCoherent) :
    ToNoneOrLtId <| inIndexElim (Option.map Index.index ∘ diagonalPreparentOf hP) none :=
  by
  apply to_none_or_lt_id_in_index_elim_yes_none_of_forall_index
  intro q
  exact descend_to_surface_to_none_or_lt_fst_index hP _

def diagonal {x : Mountain} (h_coherent : x.parents.IsCoherent) (h_orphanless : x.IsOrphanless) :
    ValueParentListPair
    where
  values :=
    ⟨surfaceAt <$> List.finRange x.values.val.length,
      by
      simp
      split_ifs
      · rw [index.val]
        simp [surface_at, index.last]
        have := Eq.trans (x.pairable.snd ⟨0, h⟩) (h_coherent.head_length _)
        generalize_proofs
        simp [this]
        exact
          mountain.head_value_eq_one_of_parents_is_coherent_of_is_orphanless_of_length_pos
            h_coherent h_orphanless h
      · triv⟩
  parents :=
    ⟨(Option.map Index.index ∘ diagonalPreparentOf h_coherent) <$>
        List.finRange x.parents.val.length,
      by
      have :=
        to_none_or_lt_id_in_index_elim_yes_none_forall_index_of _
          (to_none_or_lt_diagonal_preparent h_coherent)
      rintro ⟨i, hi⟩
      simp [index.val]
      exact this _⟩
  Pairable := by simp [pairable]; exact x.pairable.fst

theorem diagonal_length_eq {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) :
    (diagonal h_coherent h_orphanless).values.val.length = x.values.val.length := by simp [diagonal]

@[simp]
theorem diagonal_value_at {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) (i : Index (diagonal h_coherent h_orphanless).values.val) :
    i.val = surfaceAt (Pairable.transfer (diagonal_length_eq _ _) i) := by
  simp [pairable.transfer, index.val, diagonal]

@[simp]
theorem diagonal_parent_at {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) (i : Index (diagonal h_coherent h_orphanless).parents.val) :
    i.val =
      Index.index <$>
        diagonalPreparentOf h_coherent
          (Pairable.transfer
            (((diagonal h_coherent h_orphanless).Pairable.symm.trans
                  (diagonal_length_eq h_coherent h_orphanless)).trans
              x.Pairable.fst)
            i) :=
  by simp [pairable.transfer, index.val, diagonal]

theorem diagonal_isOrphanless {x : Mountain} (h_coherent : x.parents.IsCoherent)
    (h_orphanless : x.IsOrphanless) : (diagonal h_coherent h_orphanless).IsOrphanless :=
  by
  intro i
  simp [pairable.transfer]
  intro h
  rw [Option.isSome_iff_exists]
  simp
  rw [exists_comm]
  simp [exists_and_left]
  rw [← Option.isSome_iff_exists, diagonal_preparent_of_is_some_iff,
    Nat.one_lt_iff_ne_zero_and_ne_one]
  constructor
  · exact (ne_of_lt (List.length_pos_of_ne_nil (x.parents.index_val_ne_nil _))).symm
  · intro H
    rw [surface_at, index.last] at h
    simp [(x.pairable.snd _).def, pairable.transfer, H] at h
    replace h := h_orphanless _ h
    rw [← Option.ne_none_iff_isSome, Ne.def, h_coherent.val_eq_none_iff] at h
    simp [pairable.transfer, H] at h
    exact h

theorem diagonal_lt_base_of_orphanless_of_ne_one {x : Mountain} (h_coherent : x.IsCoherent)
    {i :
      Index
        (@diagonal x h_coherent.to_isCrossCoherent.to_parent_isCoherent
              h_coherent.to_isOrphanless).values.val}
    (h_surface : i.val ≠ 1) :
    i.val <
      Index₂.val
        ⟨Pairable.transfer (diagonal_length_eq _ _) i,
          ⟨0, List.length_pos_of_ne_nil (x.values.index_val_ne_nil _)⟩⟩ :=
  by
  rw [diagonal_value_at] at h_surface ⊢
  exact surface_at_lt_base_of_orphanless_of_ne_one h_coherent h_surface

section DiagonalRec

variable {C : Mountain → Sort _}
  (base :
    ∀ {x : Mountain} (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent),
      surfaceAt (Index.last ne_nil) = 1 → C x)
  (rec :
    ∀ {x : Mountain} (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent),
      surfaceAt (Index.last ne_nil) ≠ 1 →
        C
            (buildMountain
              (@diagonal x h_coherent.to_isCrossCoherent.to_parent_isCoherent
                h_coherent.to_isOrphanless)) →
          C x)
  {x : Mountain} (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent)

def diagonalRec : C x :=
  @WellFounded.fix { x : Mountain // x.values.val ≠ [] } (fun ⟨x, ne_nil⟩ => x.IsCoherent → C x)
    ((· < ·) on fun ⟨x, ne_nil⟩ =>
      Index₂.val
        (⟨Index.last ne_nil, ⟨0, List.length_pos_of_ne_nil (x.values.index_val_ne_nil _)⟩⟩ :
          Index₂ x.values.val))
    IsWellFounded.wf.onFun
    (by
      clear! x
      rintro ⟨x, ne_nil⟩ f
      intro h_coherent
      exact
        if h_surface : surface_at (index.last ne_nil) = 1 then base ne_nil h_coherent h_surface
        else
          rec ne_nil h_coherent h_surface
            (f
              ⟨build_mountain
                  (diagonal h_coherent.to_is_cross_coherent.to_parent_is_coherent
                    h_coherent.to_is_orphanless),
                by
                rw [← List.length_pos_iff_ne_nil] at ne_nil ⊢
                rwa [mountain_length_eq, diagonal_length_eq]⟩
              (by
                simp [Function.onFun, diagonal_rec._match_2, mountain_value_at_index_eq_value,
                  pairable.transfer_last]
                exact surface_at_lt_base_of_orphanless_of_ne_one h_coherent h_surface)
              (mountain_orphanless_is_coherent (diagonal_is_orphanless _ _))))
    ⟨x, ne_nil⟩ h_coherent

theorem diagonalRec_of_surface_eq_one (h_surface : surfaceAt (Index.last ne_nil) = 1) :
    diagonalRec (@base) (@rec) ne_nil h_coherent = base ne_nil h_coherent h_surface :=
  by
  rw [diagonal_rec, WellFounded.fix_eq]
  simp
  split_ifs
  rfl

theorem diagonalRec_of_surface_ne_one (h_surface : surfaceAt (Index.last ne_nil) ≠ 1) :
    diagonalRec (@base) (@rec) ne_nil h_coherent =
      rec ne_nil h_coherent h_surface
        (diagonalRec (@base) (@rec)
          (by
            rw [← List.length_pos_iff_ne_nil] at ne_nil ⊢
            rwa [mountain_length_eq, diagonal_length_eq])
          (mountain_orphanless_isCoherent (diagonal_isOrphanless _ _))) :=
  by
  rw [diagonal_rec, WellFounded.fix_eq]
  simp
  rw [Ne.def] at h_surface
  split_ifs
  rfl

theorem diagonalRec_eq_dite :
    diagonalRec (@base) (@rec) ne_nil h_coherent =
      if h_surface : surfaceAt (Index.last ne_nil) = 1 then base ne_nil h_coherent h_surface
      else
        rec ne_nil h_coherent h_surface
          (diagonalRec (@base) (@rec)
            (by
              rw [← List.length_pos_iff_ne_nil] at ne_nil ⊢
              rwa [mountain_length_eq, diagonal_length_eq])
            (mountain_orphanless_isCoherent (diagonal_isOrphanless _ _))) :=
  by
  symm
  rw [dite_eq_iff']
  constructor <;> intro h_surface <;> symm
  · apply diagonal_rec_of_surface_eq_one
  · apply diagonal_rec_of_surface_ne_one

end DiagonalRec

end Diagonal

section Badroot

/-- `@badroot x _ _` contains (↓BadRoot(x),↓BadRootHeight(x)) -/
def badroot {x : Mountain} : x.values.val ≠ [] → x.IsCoherent → Option (Index₂ x.values.val) :=
  diagonalRec
    (by
      clear x
      intro x ne_nil h_coherent h_surface
      exact
        if h_last_length : (x.pairable.fst.transfer (index.last ne_nil)).val.length = 1 then none
        else
          haveI h_parent_is_coherent := h_coherent.to_is_cross_coherent.to_parent_is_coherent
          some
            (x.pairable.symm.transfer
              (h_parent_is_coherent.index_parent_of_is_some
                  (by
                    rw [h_parent_is_coherent.val_is_some_iff]
                    simp
                    apply ne_of_lt
                    rw [← Nat.sub_sub _ 1 1]
                    refine' Nat.sub_lt _ one_pos
                    rw [tsub_pos_iff_lt, ← Nat.succ_le_iff, Nat.two_le_iff]
                    exact
                      ⟨(ne_of_lt (List.length_pos_of_ne_nil (x.parents.index_val_ne_nil _))).symm,
                        h_last_length⟩ :
                    (index₂.val
                        ⟨x.pairable.fst.transfer (index.last ne_nil),
                          ⟨(x.pairable.fst.transfer (index.last ne_nil)).val.length - 2,
                            Nat.sub_lt (List.length_pos_of_ne_nil (x.parents.index_val_ne_nil _))
                              two_pos⟩⟩).isSome)).val))
    (by
      clear x
      intro x ne_nil h_coherent h_surface p
      exact
        p.map fun p =>
          let i : index x.values.val :=
            pairable.transfer (by rw [pairable, mountain_length_eq, diagonal_length_eq]) p.fst
          ⟨i, index.last (x.values.index_val_ne_nil _)⟩)

theorem badroot_of_last_height_eq_one {x : Mountain} (ne_nil : x.values.val ≠ [])
    (h_coherent : x.IsCoherent)
    (h_last_length : (x.Pairable.fst.transfer (Index.last ne_nil)).val.length = 1) :
    badroot ne_nil h_coherent = none :=
  by
  rw [badroot, diagonal_rec_eq_dite]
  split_ifs; · rfl
  exfalso
  apply h
  simp only [surface_at, index.last]
  convert
    mountain.base_value_eq_one_of_parents_is_coherent_of_is_orphanless_of_height_eq_one
      h_coherent.to_is_cross_coherent.to_parent_is_coherent h_coherent.to_is_orphanless
      ((x.pairable.snd _).def.trans h_last_length)
  erw [(x.pairable.snd _).def, h_last_length]

theorem badroot_of_last_height_ne_one_of_last_surface_eq_one {x : Mountain}
    (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent)
    (h_last_length : (x.Pairable.fst.transfer (Index.last ne_nil)).val.length ≠ 1)
    (h_surface : surfaceAt (Index.last ne_nil) = 1) :
    badroot ne_nil h_coherent =
      haveI h_parent_is_coherent := h_coherent.to_is_cross_coherent.to_parent_is_coherent
      some
        (x.pairable.symm.transfer
          (h_parent_is_coherent.index_parent_of_is_some
              (by
                rw [h_parent_is_coherent.val_is_some_iff]
                simp
                apply ne_of_lt
                rw [← Nat.sub_sub _ 1 1]
                refine' Nat.sub_lt _ one_pos
                rw [tsub_pos_iff_lt, ← Nat.succ_le_iff, Nat.two_le_iff]
                exact
                  ⟨(ne_of_lt (List.length_pos_of_ne_nil (x.parents.index_val_ne_nil _))).symm,
                    h_last_length⟩ :
                (index₂.val
                    ⟨x.pairable.fst.transfer (index.last ne_nil),
                      ⟨(x.pairable.fst.transfer (index.last ne_nil)).val.length - 2,
                        Nat.sub_lt (List.length_pos_of_ne_nil (x.parents.index_val_ne_nil _))
                          two_pos⟩⟩).isSome)).val) :=
  by rw [badroot, diagonal_rec_eq_dite]; split_ifs; rfl

theorem badroot_of_last_surface_ne_one {x : Mountain} (ne_nil : x.values.val ≠ [])
    (h_coherent : x.IsCoherent) (h_surface : surfaceAt (Index.last ne_nil) ≠ 1) :
    badroot ne_nil h_coherent =
      (@badroot
            (buildMountain
              (@diagonal x h_coherent.to_isCrossCoherent.to_parent_isCoherent
                h_coherent.to_isOrphanless))
            (by
              rw [← List.length_pos_iff_ne_nil] at ne_nil ⊢
              rwa [mountain_length_eq, diagonal_length_eq])
            (mountain_orphanless_isCoherent (diagonal_isOrphanless _ _))).map
        fun p =>
        let i : Index x.values.val :=
          Pairable.transfer (by rw [pairable, mountain_length_eq, diagonal_length_eq]) p.fst
        ⟨i, Index.last (x.values.index_val_ne_nil _)⟩ :=
  by rw [badroot, diagonal_rec_of_surface_ne_one]; rfl; exact h_surface

/-- 𝕄ᴸ = {x : mountain // x.is_limit} -/
def Mountain.IsLimit (x : Mountain) : Prop :=
  ∃ (ne_nil : x.values.val ≠ []) (h_coherent : x.IsCoherent), (badroot ne_nil h_coherent).isSome

theorem Mountain.IsLimit.badroot_isSome {x : Mountain} (h : x.IsLimit) :
    (badroot h.fst h.snd.fst).isSome :=
  h.snd.snd

theorem Mountain.IsLimit.iff_last_length_ne_one {x : Mountain} (ne_nil : x.values.val ≠ [])
    (h_coherent : x.IsCoherent) :
    x.IsLimit ↔ (x.Pairable.fst.transfer (Index.last ne_nil)).val.length ≠ 1 :=
  by
  constructor
  · intro h
    intro H
    exact
      absurd h.badroot_is_some
        (option.not_is_some_iff_eq_none.mpr (badroot_of_last_height_eq_one ne_nil h_coherent H))
  · have ne_nil' := ne_nil
    revert ne_nil
    refine' diagonal_rec _ _ ne_nil' h_coherent <;> clear! x <;> intro x _ h_coherent h_surface
    · intro ne_nil h_last_length
      exact
        ⟨ne_nil, h_coherent,
          option.is_some_iff_exists.mpr
            ⟨_,
              badroot_of_last_height_ne_one_of_last_surface_eq_one ne_nil h_coherent h_last_length
                h_surface⟩⟩
    · intro IH ne_nil h_last_length
      exact
        ⟨ne_nil, h_coherent,
          option.is_some_iff_exists.mpr
            (by
              rw [badroot_of_last_surface_ne_one ne_nil h_coherent h_surface]
              generalize_proofs _ _ _ digonal_ne_nil diagonal_is_coherent
              obtain ⟨p, hp⟩ :=
                option.is_some_iff_exists.mp
                  (IH digonal_ne_nil
                      (by
                        intro H
                        apply
                          absurd
                            (mountain.base_value_eq_one_of_parents_is_coherent_of_is_orphanless_of_height_eq_one
                              diagonal_is_coherent.to_is_cross_coherent.to_parent_is_coherent
                              diagonal_is_coherent.to_is_orphanless
                              (((mountain.pairable _).snd _).def.trans H))
                        simpa [mountain_value_at_index_eq_value,
                          pairable.transfer_last])).badroot_isSome
              rw [hp]
              exact ⟨_, rfl⟩)⟩

end Badroot

end Ysequence

