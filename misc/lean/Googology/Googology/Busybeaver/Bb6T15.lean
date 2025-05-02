import Googology.Busybeaver.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Zmod.Basic

/-!
Formalization of ["BB(6,2) > 10↑↑15"](https://www.sligocki.com/2022/06/21/bb-6-2-t15.html) through "Pavel’s t15". For human-readable information, visit the website.

Thank you to Harold Cooper for ["Turing Machine Halting in Lean"](https://x.st/turing-machine-halting-in-lean/), which I refered throughout the definition.
-/


open Turing

open BB

inductive Γ
  | O
  | I

inductive Λ
  | A
  | B
  | C
  | D
  | E
  | F

open Γ Λ

instance Γ.inhabited : Inhabited Γ :=
  ⟨O⟩

instance Λ.inhabited : Inhabited Λ :=
  ⟨A⟩

def cfg₀ : Cfg Γ Λ :=
  init []

local notation "L" => Dir.left

local notation "R" => Dir.right

local notation "Z" => @none Λ

def t15 : Machine Γ Λ
  | A, O => (I, R, B)
  | A, I => (O, L, D)
  | B, O => (I, R, C)
  | B, I => (O, R, F)
  | C, O => (I, L, C)
  | C, I => (I, L, A)
  | D, O => (O, L, E)
  | D, I => (I, R, Z)
  | E, O => (I, L, F)
  | E, I => (O, R, B)
  | F, O => (O, R, C)
  | F, I => (O, R, E)

def collatzState (n : ℕ) : Cfg Γ Λ :=
  ⟨C, ⟨O, ListBlank.mk ([O, O, O, O, O, I, I] ++ List.replicate n O ++ [I]), ListBlank.mk []⟩⟩

def haltState (n : ℕ) : Cfg Γ Λ :=
  ⟨Z, ⟨O, ListBlank.mk ([O, O, O, O, O, I, I] ++ List.replicate n O ++ [I]), ListBlank.mk []⟩⟩
#exit
/-
...   S 1 0^n C>0 ...
... A>S 1 1^n   1 ...
in n+2 steps
-/
theorem c_sweep_zero (n S TL TR) :
    ⟨C,
        ⟨O, ListBlank.mk (List.replicate n O ++ [I, S] ++ TL),
          ListBlank.mk
            TR⟩⟩[t15]▸^[n +
        2]⟨A, ⟨S, ListBlank.mk TL, ListBlank.mk (List.replicate (n + 2) I ++ TR)⟩⟩ :=
  by
  induction' n with n IH generalizing TR
  · exact correct_multistep_correst_step_trans _ _ _ _ rfl rfl
  · refine' (correct_multistep_succ_iff _ _ _).mpr ⟨_, ⟨rfl, _⟩⟩
    dsimp [t15, step, tape.move, tape.write]
    rw [← List.cons_append]
    rw [← List.replicate_succ]
    rw [List.replicate_succ']
    rw [List.append_assoc _ [I] TR]
    exact IH _

/-
def collatz_rule1_time : ℕ → ℕ := sorry
def collatz_rule2_time : ℕ → ℕ := sorry
def collatz_rule3_time : ℕ → ℕ := sorry
def collatz_rule4_time : ℕ → ℕ := sorry

theorem collatz_rule1 (k) : (collatz_state (4 * k))[t15]▸^[collatz_rule1_time k](halt_state ((3 ^ (k + 3) - 11) / 2)) :=
sorry

theorem collatz_rule2 (k) : (collatz_state (4 * k + 1))[t15]▸^[collatz_rule2_time k](collatz_state ((3 ^ (k + 3) - 11) / 2)) :=
begin
  have : multistep t15 1 (collatz_state (4 * k + 1)) = sorry,
  simp [collatz_state, multistep, multistep', step', step, t15, tape.move, tape.write],
  all_goals { sorry }
end

theorem collatz_rule3 (k) : (collatz_state (4 * k + 2))[t15]▸^[collatz_rule3_time k](collatz_state ((3 ^ (k + 3) - 11) / 2)) :=
sorry

theorem collatz_rule4 (k) : (collatz_state (4 * k + 3))[t15]▸^[collatz_rule4_time k](collatz_state ((3 ^ (k + 3) + 1) / 2)) :=
sorry
-/
#reduce cfg₀

#reduce multistep t15 45 cfg₀

#reduce collatzState (4 * 1 + 1)

axiom resttime : ℕ

axiom finalstate : Cfg Γ Λ

/-
theorem t15_evaluation : cfg₀[t15]▸^[45+resttime](finalstate) :=
begin
  calc
  cfg₀[t15]▸^[45](collatz_state (4 * 1 + 1)) : by exact rfl
  ... [t15]▸^[resttime](finalstate) : sorry,
end
-/
