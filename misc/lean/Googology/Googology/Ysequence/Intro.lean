import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Pnat.Basic

namespace Ysequence

variable {α β γ : Type}

theorem iterate_bind_none (f : α → Option α) : ∀ n : ℕ, (flip bind f)^[n] none = none :=
  Nat.rec rfl fun n IH => (by rw [Function.iterate_succ_apply', IH]; rfl)

theorem iterate_bind_eq_none_ge {f : α → Option α} {m n : ℕ} (hmn : m ≤ n) {x : Option α}
    (h : (flip bind f)^[m] x = none) : (flip bind f)^[n] x = none :=
  by rw [← Nat.sub_add_cancel hmn, Function.iterate_add_apply, h, iterate_bind_none]

theorem isSome_of_iterate_bind_isSome {f : α → Option α} {n : ℕ} {x : Option α}
    (h : ((flip bind f)^[n] x).isSome) : x.isSome :=
  by
  rw [← Option.ne_none_iff_isSome] at h ⊢
  intro H
  apply h
  rw [H]
  apply iterate_bind_none

theorem iterate_bind_isSome_le {f : α → Option α} {m n : ℕ} (hmn : m ≤ n) {x : Option α}
    (h : ((flip bind f)^[n] x).isSome) : ((flip bind f)^[m] x).isSome :=
  by
  rw [← Nat.sub_add_cancel hmn, Function.iterate_add_apply] at h
  exact isSome_of_iterate_bind_isSome h

def IterateEventuallyNone (f : α → Option α) : Prop :=
  ∀ x : Option α, ∃ k : ℕ, (flip bind f)^[k] x = none

theorem iterateEventuallyNone_or_mem_of_iterateEventuallyNone {f : α → Option α}
    (hf : IterateEventuallyNone f) (p : Set α) (x : α) :
    ∃ k : ℕ, ∀ y ∈ (flip bind f)^[k] <| some x, p y :=
  by
  rcases hf (some x) with ⟨k, hk⟩
  use k
  rw [hk]
  intros
  contradiction

def findIndexIterateOfIterateEventuallyNone {f : α → Option α} (hf : IterateEventuallyNone f)
    {p : Set α} (_ : DecidablePred p) (x : α) : ℕ :=
  Nat.find (iterateEventuallyNone_or_mem_of_iterateEventuallyNone hf p x)

theorem findIndexIterate_spec {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) :
    ∀ y ∈ (flip bind f)^[findIndexIterateOfIterateEventuallyNone hf decidable_p x] <| some x, p y :=
  Nat.find_spec (iterateEventuallyNone_or_mem_of_iterateEventuallyNone hf p x)

theorem findIndexIterate_min {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) {k : ℕ} :
    k < findIndexIterateOfIterateEventuallyNone hf decidable_p x →
      ¬∀ y ∈ (flip bind f)^[k] <| some x, p y :=
  Nat.find_min (iterateEventuallyNone_or_mem_of_iterateEventuallyNone hf p x)

theorem findIndexIterate_eq_iff {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) (k : ℕ) :
    findIndexIterateOfIterateEventuallyNone hf decidable_p x = k ↔
      (∀ y ∈ (flip bind f)^[k] <| some x, p y) ∧
        ∀ l < k, ¬∀ y ∈ (flip bind f)^[l] <| some x, p y :=
  Nat.find_eq_iff (iterateEventuallyNone_or_mem_of_iterateEventuallyNone hf p x)

def findIterateOfIterateEventuallyNone {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) : Option α :=
  (flip bind f)^[findIndexIterateOfIterateEventuallyNone hf decidable_p x] <| some x

theorem findIterate_spec {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) :
    ∀ y ∈ findIterateOfIterateEventuallyNone hf decidable_p x, p y :=
  findIndexIterate_spec _ _ _

theorem iterate_bind_find_index_empty {f : α → Option α}
    (hf : IterateEventuallyNone f) (x : α) :
    ((flip bind f)^[findIndexIterateOfIterateEventuallyNone hf Set.decidableEmptyset x] <| some x)
      = none :=
  by
  rw [Option.eq_none_iff_forall_not_mem]
  intro _ H
  exact findIndexIterate_spec _ _ _ _ H

theorem iterate_bind_isSome_iff_lt_of_iterateEventuallyNone_empty {f : α → Option α}
    (hf : IterateEventuallyNone f) (x : α) (k : ℕ) :
    ((flip bind f)^[k] <| some x).isSome ↔
      k < findIndexIterateOfIterateEventuallyNone hf Set.decidableEmptyset x :=
  by
  constructor
  · rw [← Option.ne_none_iff_isSome, ← Nat.not_le]
    apply mt
    intro hk
    apply iterate_bind_eq_none_ge hk
    apply iterate_bind_find_index_empty
  · rw [← Option.ne_none_iff_isSome, Ne, Option.eq_none_iff_forall_not_mem]
    apply findIndexIterate_min

theorem findIterate_isSome_iff {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) :
    (findIterateOfIterateEventuallyNone hf decidable_p x).isSome ↔
      ∃ (k : ℕ) (h : ((flip bind f)^[k] <| some x).isSome), Option.get _ h ∈ p :=
  by
  constructor
  · intro h
    refine' ⟨_, h, _⟩
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
    conv in (_^[_] _) => change findIterateOfIterateEventuallyNone hf decidable_p x
    have := findIterate_spec hf decidable_p x
    simp [hy] at this ⊢
    exact this
  · intro h
    rcases h with ⟨k, hk₁, hk₂⟩
    by_contra H
    apply findIndexIterate_min hf decidable_p x (k := k)
    · clear hk₂
      apply lt_of_not_ge
      rw [← Option.ne_none_iff_isSome] at hk₁
      intro H'
      apply hk₁
      refine Nat.le_induction (Option.not_isSome_iff_eq_none.mp H) ?_ k H'
      intro k _ IH
      rw [Function.iterate_succ_apply', IH]
      rfl
    · intro y hy
      rw [Option.mem_def] at hy
      simp_rw [hy] at hk₂
      exact hk₂

theorem findIterate_eq_none_iff {f : α → Option α} (hf : IterateEventuallyNone f) {p : Set α}
    (decidable_p : DecidablePred p) (x : α) :
    findIterateOfIterateEventuallyNone hf decidable_p x = none ↔
      ∀ {k : ℕ} (h : ((flip bind f)^[k] <| some x).isSome), Option.get _ h ∉ p :=
  by
  trans
    ∀ (k : Fin _),
      Option.get _
          (iterate_bind_isSome_iff_lt_of_iterateEventuallyNone_empty hf x k.val |>.mpr k.isLt)
        ∉ p
  swap; · simp_all only [Fin.forall_iff, iterate_bind_isSome_iff_lt_of_iterateEventuallyNone_empty]
  have : DecidablePred (· ∈ p) := decidable_p
  rw [← Option.not_isSome_iff_eq_none, ← Decidable.not_exists_not, Decidable.not_iff_not,
    exists_congr <| fun _ => Decidable.not_not_iff, Fin.exists_iff]
  simp_all only [findIterate_isSome_iff, iterate_bind_isSome_iff_lt_of_iterateEventuallyNone_empty]

theorem findIndexIterate_pos_of_not_mem {f : α → Option α} (hf : IterateEventuallyNone f)
    {p : Set α} (decidable_p : DecidablePred p) {x : α} (hn : x ∉ p) :
    0 < findIndexIterateOfIterateEventuallyNone hf decidable_p x := by
  rw [pos_iff_ne_zero]
  intro H
  have := findIndexIterate_spec hf decidable_p x
  simp [H] at this
  contradiction

def ToNoneOrLtId [LT α] (f : α → Option α) : Prop :=
  ∀ x : α, WithBot.lt.lt (f x) ↑x

theorem iterateEventuallyNone_of_toNoneOrLtId {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) :
    IterateEventuallyNone f :=
  by
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

theorem iterate_iterate_dependent_apply (f : α → α) (g : α → ℕ) (n : ℕ) (x : α) :
    (fun x => f^[g x] x)^[n] x =
      f^[Nat.sum <| List.iterate (fun x => f^[g x] x) x n |>.map g] x :=
  n.recOn (fun _ => rfl) (fun n IH x => by
    rw [Function.iterate_succ_apply, IH, List.iterate, List.map_cons, Nat.sum_cons, Nat.add_comm,
      Function.iterate_add_apply]) x

theorem iterate_iterate_dependent (f : α → α) (g : α → ℕ) (n : ℕ) :
    (fun x => f^[g x] x)^[n] =
      fun x => f^[Nat.sum <| List.iterate (fun x => f^[g x] x) x n |>.map g] x :=
  funext fun _ => iterate_iterate_dependent_apply ..

theorem toNoneOrLtId_iterate_succ {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) (n k : ℕ) :
    WithBot.lt.lt ((flip bind f)^[k + 1] <| some n) ↑n := by
  induction' k with k IH
  · exact hf n
  · rw [Function.iterate_succ_apply']
    cases' hl : (flip bind f)^[k + 1] <| some n
    · exact WithBot.bot_lt_coe n
    · exact lt_trans (hf _) (lt_of_eq_of_lt hl.symm IH)

theorem toNoneOrLtId_iterate_pos {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) (n : ℕ) {k : ℕ}
    (hk : 0 < k) : WithBot.lt.lt ((flip bind f)^[k] <| some n) ↑n := by
  cases' k with k
  · exact absurd hk (by decide)
  · exact toNoneOrLtId_iterate_succ hf n k

theorem toNoneOrLtId_findIterate_of_not_mem {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) {p : Set ℕ}
    (decidable_p : DecidablePred p) {n : ℕ} (hn : n ∉ p) :
    WithBot.lt.lt (findIterateOfToNoneOrLtId hf decidable_p n) ↑n :=
  toNoneOrLtId_iterate_pos hf _ (findIndexIterate_pos_of_not_mem _ _ hn)

theorem toNoneOrLtId_findIterate_of_all_not_mem {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f)
    {g : ℕ → Set ℕ} (hg₁ : ∀ n, DecidablePred <| g n) (hg₂ : ∀ n, n ∉ g n) :
    ToNoneOrLtId fun n => findIterateOfToNoneOrLtId hf (hg₁ n) n :=
  fun n => toNoneOrLtId_findIterate_of_not_mem hf (hg₁ n) (hg₂ n)

@[simp]
theorem Option.seq_none_right {f : Option (α → β)} : f <*> none = none := by cases f <;> rfl

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

end Ysequence
