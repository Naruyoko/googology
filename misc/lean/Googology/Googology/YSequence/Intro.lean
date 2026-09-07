import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.PNat.Basic

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

theorem exists_iterate_bind_all_of_iterateEventuallyNone {f : α → Option α}
    (hf : IterateEventuallyNone f) (p : α → Bool) (x : α) :
    ∃ k : ℕ, ((flip bind f)^[k] <| some x).all p :=
  by
  rcases hf (some x) with ⟨k, hk⟩
  use k
  rw [hk, Option.all_none]

def findIndexIterateOfIterateEventuallyNone {f : α → Option α} (hf : IterateEventuallyNone f)
    (p : α → Bool) (x : α) : ℕ :=
  Nat.find (exists_iterate_bind_all_of_iterateEventuallyNone hf p x)

theorem findIndexIterate_spec {f : α → Option α} (hf : IterateEventuallyNone f)
    (p : α → Bool) (x : α) :
    ((flip bind f)^[findIndexIterateOfIterateEventuallyNone hf p x] <| some x).all p :=
  Nat.find_spec (exists_iterate_bind_all_of_iterateEventuallyNone hf p x)

theorem findIndexIterate_min {f : α → Option α} (hf : IterateEventuallyNone f) (p : α → Bool)
    (x : α) {k : ℕ} :
    k < findIndexIterateOfIterateEventuallyNone hf p x → ¬((flip bind f)^[k] <| some x).all p :=
  Nat.find_min (exists_iterate_bind_all_of_iterateEventuallyNone hf p x)

theorem findIndexIterate_eq_iff {f : α → Option α} (hf : IterateEventuallyNone f) (p : α → Bool)
    (x : α) (k : ℕ) :
    findIndexIterateOfIterateEventuallyNone hf p x = k ↔
      ((flip bind f)^[k] <| some x).all p ∧
        ∀ l < k, ¬((flip bind f)^[l] <| some x).all p :=
  Nat.find_eq_iff (exists_iterate_bind_all_of_iterateEventuallyNone hf p x)

def findIterateOfIterateEventuallyNone {f : α → Option α} (hf : IterateEventuallyNone f)
    (p : α → Bool) (x : α) : Option α :=
  (flip bind f)^[findIndexIterateOfIterateEventuallyNone hf p x] <| some x

theorem findIterate_spec {f : α → Option α} (hf : IterateEventuallyNone f) (p : α → Bool) (x : α) :
    (findIterateOfIterateEventuallyNone hf p x).all p :=
  findIndexIterate_spec ..

theorem findIterate_false {f : α → Option α}
    (hf : IterateEventuallyNone f) (x : α) :
    findIterateOfIterateEventuallyNone hf (fun _ => false) x = none :=
  by
  rw [Option.eq_none_iff_forall_ne_some]
  intro _ H
  have := H ▸ findIterate_spec hf (fun _ => false) x
  contradiction

theorem iterate_bind_isSome_iff_lt_of_iterateEventuallyNone_false {f : α → Option α}
    (hf : IterateEventuallyNone f) (x : α) (k : ℕ) :
    ((flip bind f)^[k] <| some x).isSome ↔
      k < findIndexIterateOfIterateEventuallyNone hf (fun _ => false) x :=
  by
  constructor
  · rw [← Option.ne_none_iff_isSome, ← Nat.not_le]
    apply mt
    intro hk
    apply iterate_bind_eq_none_ge hk
    apply findIterate_false
  · rw [← Option.ne_none_iff_isSome]
    intro hk H
    have := H ▸ findIndexIterate_min _ _ _ hk
    contradiction

theorem findIterate_isSome_iff {f : α → Option α} (hf : IterateEventuallyNone f) (p : α → Bool)
    (x : α) :
    (findIterateOfIterateEventuallyNone hf p x).isSome ↔
      ∃ (k : ℕ) (h : ((flip bind f)^[k] <| some x).isSome), p (Option.get _ h) :=
  by
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    apply Option.all_eq_true_iff_get .. |>.mp
    apply findIterate_spec
  · intro ⟨k, hk₁, hk₂⟩
    refine iterate_bind_isSome_le (le_of_not_gt (fun H => ?_)) hk₁
    apply findIndexIterate_min hf p x H
    rw [Option.all_eq_true_iff_get]
    exact fun _ => hk₂

theorem findIterate_eq_none_iff {f : α → Option α} (hf : IterateEventuallyNone f) (p : α → Bool)
    (x : α) :
    findIterateOfIterateEventuallyNone hf p x = none ↔
      ∀ {k : ℕ} (h : ((flip bind f)^[k] <| some x).isSome), ¬p (Option.get _ h) :=
  by
  trans
    ∀ (k : Fin _),
      ¬p (((flip bind f)^[k] <| some x).get
          (iterate_bind_isSome_iff_lt_of_iterateEventuallyNone_false hf x k.val |>.mpr k.isLt))
  · rw [← Option.not_isSome_iff_eq_none, ← Decidable.not_exists_not,
      exists_congr fun _ => Decidable.not_not, Fin.exists_iff, Decidable.not_iff_not,
      findIterate_isSome_iff]
    congr! 4
    apply iterate_bind_isSome_iff_lt_of_iterateEventuallyNone_false
  · simp_all only [Fin.forall_iff, iterate_bind_isSome_iff_lt_of_iterateEventuallyNone_false]

theorem findIndexIterate_pos_of_not {f : α → Option α} (hf : IterateEventuallyNone f)
    (p : α → Bool) {x : α} (hn : ¬p x) :
    0 < findIndexIterateOfIterateEventuallyNone hf p x :=
  by
  apply Nat.pos_of_ne_zero
  intro H
  have := findIndexIterate_spec hf p x
  simp_all

def ToNoneOrLtId [LT α] (f : α → Option α) : Prop :=
  ∀ x : α, WithBot.instLT.lt (f x) ↑x

theorem iterateEventuallyNone_of_toNoneOrLtId {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) :
    IterateEventuallyNone f :=
  by
  refine fun n => IsWellFounded.induction WithBot.instLT.lt
    (motive := fun n => ∃ k, (flip bind f)^[k] n = none) n ?_
  intro n IH
  cases n with
  | bot => exact ⟨0, rfl⟩
  | coe n =>
    choose! k h using IH
    exact ⟨k (f n) + 1, h _ (hf n)⟩

def findIterateOfToNoneOrLtId {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) (p : ℕ → Bool)
    : ℕ → Option ℕ :=
  findIterateOfIterateEventuallyNone (iterateEventuallyNone_of_toNoneOrLtId hf) p

theorem iterate_iterate_dependent_apply (f : α → α) (g : α → ℕ) (n : ℕ) (x : α) :
    (fun x => f^[g x] x)^[n] x =
      f^[List.sum <| List.iterate (fun x => f^[g x] x) x n |>.map g] x :=
  n.recOn
    (fun _ => rfl)
    (fun n IH x =>
      by rw [Function.iterate_succ_apply, IH, List.iterate, List.map_cons, List.sum_cons,
        Nat.add_comm, Function.iterate_add_apply])
    x

theorem iterate_iterate_dependent (f : α → α) (g : α → ℕ) (n : ℕ) :
    (fun x => f^[g x] x)^[n] =
      fun x => f^[List.sum <| List.iterate (fun x => f^[g x] x) x n |>.map g] x :=
  funext fun _ => iterate_iterate_dependent_apply ..

theorem toNoneOrLtId_iterate_succ {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) (n k : ℕ) :
    WithBot.instLT.lt ((flip bind f)^[k + 1] <| some n) ↑n :=
  by
  induction k with
  | zero => exact hf n
  | succ k IH =>
    rw [Function.iterate_succ_apply']
    cases hl : (flip bind f)^[k + 1] <| some n with
    | none => exact WithBot.bot_lt_coe n
    | some _ => exact lt_trans (hf _) (lt_of_eq_of_lt hl.symm IH)

theorem toNoneOrLtId_iterate_pos {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) (n : ℕ) {k : ℕ}
    (hk : 0 < k) : WithBot.instLT.lt ((flip bind f)^[k] <| some n) ↑n :=
  by
  cases k with
  | zero => contradiction
  | succ k => exact toNoneOrLtId_iterate_succ hf n k

theorem toNoneOrLtId_findIterate_of_not {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f) (p : ℕ → Bool)
    {n : ℕ} (hn : ¬p n) :
    WithBot.instLT.lt (findIterateOfToNoneOrLtId hf p n) ↑n :=
  toNoneOrLtId_iterate_pos hf _ (findIndexIterate_pos_of_not _ _ hn)

theorem toNoneOrLtId_findIterate_of_all_not_self {f : ℕ → Option ℕ} (hf : ToNoneOrLtId f)
    (g : ℕ → ℕ → Bool) (hg : ∀ n, ¬g n n) :
    ToNoneOrLtId fun n => findIterateOfToNoneOrLtId hf (g n) n :=
  fun n => toNoneOrLtId_findIterate_of_not hf (g n) (hg n)

@[simp]
theorem Option.seq_none_right {f : Option (α → β)} : f <*> none = none := by cases f <;> rfl

theorem Pnat.sub_val_eq_iff_eq_add {a b c : ℕ+} : a.val - b.val = c.val ↔ a = c + b :=
  by
  rcases a with ⟨a, a_pos⟩
  rcases b with ⟨b, b_pos⟩
  rcases c with ⟨c, c_pos⟩
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt c_pos)
  dsimp
  constructor <;> intro h
  · apply PNat.eq
    erw [PNat.add_coe]
    apply
      Nat.eq_add_of_sub_eq
        (Nat.le_of_lt <| Nat.lt_of_sub_pos <| Nat.lt_of_lt_of_eq c_pos h.symm)
        h
  · have h' := congr_arg Subtype.val h
    dsimp at h'
    exact tsub_eq_of_eq_add h'

end Ysequence
