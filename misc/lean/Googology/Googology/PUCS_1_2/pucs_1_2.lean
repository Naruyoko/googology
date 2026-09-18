-- Formalization of PUCS-1's second conjecture

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

set_option maxHeartbeats 1000000

-- Tetration (iterated exponentiation)
-- We define it recursively: x ↑↑ 0 = 1, x ↑↑ (n+1) = x ^ (x ↑↑ n)
-- However, note that in the proof, they seem to use x ↑↑ n for n ≥ 1
-- and for the base case n=1, x ↑↑ 1 = x

noncomputable def tetration (x : ℝ) (n : ℕ) : ℝ :=
  match n with
  | 0 => 1
  | k + 1 => x ^ tetration x k

-- Iterated exponential with base 2: (2↑)^k b = 2^(2^(...^(2^b)...)) with k 2's
-- (2↑)^0 b = b
-- (2↑)^1 b = 2^b
-- (2↑)^2 b = 2^(2^b)
-- etc.
noncomputable def iter_exp_two (k : ℕ) (b : ℝ) : ℝ :=
  match k with
  | 0 => b
  | k + 1 => 2 ^ iter_exp_two k b

-- Helper lemma: log₂(x) = log(x) / log(2)
lemma log_two_div {x : ℝ} (_hx : 0 < x) : Real.log x / Real.log 2 = Real.logb 2 x := by
  rw [Real.logb]

-- Lemma: 9 < 8 * e * ln(2)
lemma nine_lt_eight_exp_one_log_two : (9 : ℝ) < 8 * Real.exp 1 * Real.log 2 := by
  have h₁ : Real.exp 1 > 2.7 := by linarith [Real.exp_one_gt_d9]
  have h₂ : Real.log 2 > 0.69 := by linarith [Real.log_two_gt_d9]
  have h₃ : 0 < Real.exp 1 := by apply Real.exp_pos
  have h₄ : 0 < Real.log 2 := by apply Real.log_pos; norm_num
  nlinarith [mul_pos h₃ h₄, mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂)]

-- Lemma: For any real number x > 1, (9/8) * log₂x < x
lemma lemma_log_bound {x : ℝ} (hx : 1 < x) : (9 / 8 : ℝ) * Real.log x / Real.log 2 < x := by
  have h₁ : 0 < Real.log 2 := by apply Real.log_pos; norm_num

  have h₂ : 0 < Real.log x := by exact Real.log_pos (by linarith)

  have h₃ : 0 < 8 * Real.log 2 := by positivity

  have h₄ : 0 < 8 * x * Real.log 2 := by positivity

  have h₅ : (9 : ℝ) < 8 * Real.exp 1 * Real.log 2 := nine_lt_eight_exp_one_log_two

  have h₆ : Real.log x ≤ x - 1 := by
    have h₆₂ : 0 < x := by linarith
    linarith [Real.log_le_sub_one_of_pos h₆₂]

  have h₇ : (9 / 8 : ℝ) * Real.log x / Real.log 2 < x := by
    have h₇₁ : 0 < Real.log 2 := h₁
    have h₇₂ : 0 < x := by linarith
    have h₇₃ : 0 < Real.log x := h₂
    have h₇₅ : Real.log x ≤ x * Real.exp (-1) := by
      have h₇₅₁ : 0 < x * Real.exp (-1) := by positivity
      have h₇₅₂ : Real.log (x * Real.exp (-1)) ≤ (x * Real.exp (-1)) - 1 := by
        linarith [Real.log_le_sub_one_of_pos h₇₅₁]
      have h₇₅₃ : Real.log (x * Real.exp (-1)) = Real.log x + Real.log (Real.exp (-1)) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      have h₇₅₄ : Real.log (Real.exp (-1)) = -1 := by
        rw [Real.log_exp]
      have h₇₅₅ : Real.log x + (-1 : ℝ) ≤ (x * Real.exp (-1)) - 1 := by
        linarith
      linarith
    -- Multiply by 9/8 > 0
    have h₇₆ : (9 / 8 : ℝ) * Real.log x ≤ (9 / 8 : ℝ) * (x * Real.exp (-1)) := by
      gcongr
    -- From h₅: 9 < 8 * Real.exp 1 * Real.log 2
    have h₇₇ : (9 / 8 : ℝ) * Real.exp (-1) < Real.log 2 := by
      have h₇₇₁ : (9 : ℝ) < 8 * Real.exp 1 * Real.log 2 := h₅
      have h₇₇₂ : 0 < 8 * Real.exp 1 := by positivity
      -- We'll prove this by showing that the opposite leads to a contradiction
      have h₇₇₃ : (9 / 8 : ℝ) * Real.exp (-1) < Real.log 2 := by
        by_contra h
        -- If (9/8) * exp(-1) ≥ log 2, then
        have h₇₇₄ : Real.log 2 ≤ (9 / 8 : ℝ) * Real.exp (-1) := by linarith
        have h₇₇₅ : 8 * Real.exp 1 * Real.log 2 ≤ 9 := by
          have h₇₇₆ : 0 < 8 * Real.exp 1 := by positivity
          have h₇₇₇ : 0 < Real.exp 1 := by positivity
          have h₇₇₈ : 8 * Real.exp 1 * Real.log 2 ≤ 8 * Real.exp 1 * ((9 / 8 : ℝ) * Real.exp (-1)) := by
            gcongr
          have h₇₇₉ : 8 * Real.exp 1 * ((9 / 8 : ℝ) * Real.exp (-1)) = 9 := by
            have h₁ : Real.exp 1 * Real.exp (-1) = 1 := by
              rw [← Real.exp_add]
              ; norm_num
            calc
              8 * Real.exp 1 * ((9 / 8 : ℝ) * Real.exp (-1)) = 8 * Real.exp 1 * (9 / 8 : ℝ) * Real.exp (-1) := by ring
              _ = (8 * (9 / 8 : ℝ)) * (Real.exp 1 * Real.exp (-1)) := by ring
              _ = (9 : ℝ) * (Real.exp 1 * Real.exp (-1)) := by norm_num
              _ = (9 : ℝ) * 1 := by rw [h₁]
              _ = 9 := by norm_num
          linarith
        linarith
      exact h₇₇₃
    -- Multiply by x > 0
    have h₇₈ : (9 / 8 : ℝ) * x * Real.exp (-1) < x * Real.log 2 := by
      have h₇₈₁ : 0 < x := by linarith
      have h₇₈₂ : 0 < (9 / 8 : ℝ) * Real.exp (-1) := by positivity
      nlinarith
    -- Chain the inequalities
    have h₇₉ : (9 / 8 : ℝ) * Real.log x < x * Real.log 2 := by
      linarith
    -- Divide by Real.log 2 > 0
    have h₇₁₀ : (9 / 8 : ℝ) * Real.log x / Real.log 2 < x := by
      have h₇₁₀₁ : 0 < Real.log 2 := h₁
      have h₇₁₀₂ : (9 / 8 : ℝ) * Real.log x < x * Real.log 2 := h₇₉
      -- We'll prove this by showing that the opposite leads to a contradiction
      have h₇₁₀₃ : (9 / 8 : ℝ) * Real.log x / Real.log 2 < x := by
        by_contra h
        have h₇₁₀₄ : x ≤ (9 / 8 : ℝ) * Real.log x / Real.log 2 := by linarith
        have h₇₁₀₅ : x * Real.log 2 ≤ (9 / 8 : ℝ) * Real.log x := by
          have h₇₁₀₆ : 0 < Real.log 2 := by positivity
          have h₇₁₀₇ : 0 < x := by linarith
          have h₇₁₀₈ : 0 < (9 / 8 : ℝ) := by positivity
          field_simp [h₇₁₀₆.ne'] at h₇₁₀₄ ⊢
          rw [← sub_pos] at *
          nlinarith
        linarith
      exact h₇₁₀₃
    exact h₇₁₀

  exact h₇

-- Basic properties of tetration
@[simp]
theorem tetration_zero {x : ℝ} : tetration x 0 = 1 := by
  rfl

@[simp]
theorem tetration_one {x : ℝ} : tetration x 1 = x := by
  simp [tetration]

@[simp]
theorem tetration_two {x : ℝ} : tetration x 2 = x ^ x := by
  simp [tetration]

-- Monotonicity lemmas for tetration

-- Common helper: positivity of tetration for positive base
lemma pos_tetration {x : ℝ} (hx : 0 < x) : ∀ n : ℕ, 0 < tetration x n := by
  intro n
  induction n with
  | zero => simp [tetration]
  | succ n ih =>
    rw [tetration]
    exact Real.rpow_pos_of_pos hx (tetration x n)

-- Common helper: non-negativity of tetration for positive base
lemma nonneg_tetration {x : ℝ} (hx : 0 < x) : ∀ n : ℕ, 0 ≤ tetration x n := by
  intro n
  exact le_of_lt (pos_tetration hx n)

-- Monotonicity in base: if 1 < x ≤ y then tetration x n ≤ tetration y n (for n ≥ 1)
lemma tetration_mono_base {x y : ℝ} {n : ℕ} (hxy : 1 < x) (hxy' : x ≤ y) (hn : 1 ≤ n) :
    tetration x n ≤ tetration y n := by
  have h₁ : 0 < x := by linarith
  have h₂ : 0 < y := by linarith
  have h₃ : ∀ n : ℕ, 0 ≤ tetration x n := nonneg_tetration h₁
  have h₄ : ∀ n : ℕ, 0 ≤ tetration y n := nonneg_tetration h₂
  have h₅ : ∀ n : ℕ, 1 ≤ n → tetration x n ≤ tetration y n := by
    intro n hn
    induction' hn with n hn IH
    · -- Base case: n = 1
      simp [tetration_one]
      ; linarith
    · -- Inductive step: assume true for n, prove for n + 1
      simp_all [tetration]
      -- Need to show x ^ tetration x n ≤ y ^ tetration y n
      -- We have: tetration x n ≤ tetration y n by IH
      -- Since x ≤ y and x > 1, we can use monotonicity of rpow
      have h₆ : 0 < x := by linarith
      have h₇ : 0 < y := by linarith
      have h₈ : 1 ≤ (x : ℝ) := by linarith
      have h₉ : 0 ≤ tetration x n := h₃ n
      have h₁₀ : 0 ≤ tetration y n := h₄ n
      -- Use the fact that if a ≤ b and c ≤ d, then a^c ≤ b^d for a,b > 1 and c,d ≥ 0
      have h₁₁ : x ^ tetration x n ≤ y ^ tetration y n := by
        have h₁₁₁ : (1 : ℝ) ≤ x := by linarith
        have h₁₁₂ : (tetration x n : ℝ) ≤ (tetration y n : ℝ) := by exact_mod_cast IH
        have h₁₁₃ : (x : ℝ) ^ (tetration x n : ℝ) ≤ (x : ℝ) ^ (tetration y n : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le h₁₁₁ h₁₁₂
        have h₁₁₄ : (x : ℝ) ^ (tetration y n : ℝ) ≤ (y : ℝ) ^ (tetration y n : ℝ) := by
          apply Real.rpow_le_rpow (by linarith) (by exact_mod_cast hxy') (by exact_mod_cast h₁₀)
        calc
          (x : ℝ) ^ (tetration x n : ℝ) ≤ (x : ℝ) ^ (tetration y n : ℝ) := h₁₁₃
          _ ≤ (y : ℝ) ^ (tetration y n : ℝ) := h₁₁₄
      exact_mod_cast h₁₁
  exact h₅ n hn

-- Strict monotonicity in base: if 1 < x < y then tetration x n < tetration y n (for n ≥ 1)
lemma tetration_strict_mono_base {x y : ℝ} {n : ℕ} (hxy : 1 < x) (hxy' : x < y) (hn : 1 ≤ n) :
    tetration x n < tetration y n := by
  have h₁ : 0 < x := by linarith
  have h₂ : 0 < y := by linarith
  have h₃ : ∀ n : ℕ, 0 ≤ tetration x n := by
    intro n
    induction n with
    | zero => simp [tetration]
    | succ n ih =>
      rw [tetration]
      exact Real.rpow_nonneg (by linarith) (tetration x n)
  have h₄ : ∀ n : ℕ, 0 ≤ tetration y n := by
    intro n
    induction n with
    | zero => simp [tetration]
    | succ n ih =>
      rw [tetration]
      exact Real.rpow_nonneg (by linarith) (tetration y n)
  have h₅ : ∀ n : ℕ, 1 ≤ n → tetration x n < tetration y n := by
    intro n hn
    induction' hn with n hn IH
    · -- Base case: n = 1
      simp [tetration_one]
      ; linarith
    · -- Inductive step: assume true for n, prove for n + 1
      simp_all [tetration]
      -- Need to show x ^ tetration x n < y ^ tetration y n
      -- We have: tetration x n < tetration y n by IH
      -- Since x < y and x > 1, we can use strict monotonicity of rpow
      have h₆ : 0 < x := by linarith
      have h₇ : 0 < y := by linarith
      have h₈ : 1 ≤ (x : ℝ) := by linarith
      have h₉ : 0 ≤ tetration x n := h₃ n
      have h₁₀ : 0 ≤ tetration y n := h₄ n
      -- Use the fact that if a < b and c < d, then a^c < b^d for a,b > 1 and c,d ≥ 0
      have h₁₁ : x ^ tetration x n < x ^ tetration y n := by
        have h₁₁₁ : (1 : ℝ) ≤ x := by linarith
        have h₁₁₂ : (tetration x n : ℝ) < (tetration y n : ℝ) := by exact_mod_cast IH
        -- Use Real.rpow_lt_rpow_of_exponent_lt: if 1 < x and y < z, then x^y < x^z
        have h₁₁₃ : (x : ℝ) ^ (tetration x n : ℝ) < (x : ℝ) ^ (tetration y n : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt (by linarith) h₁₁₂
        exact_mod_cast h₁₁₃
      have h₁₂ : x ^ tetration y n ≤ y ^ tetration y n := by
        have h₁₂₁ : 0 ≤ (x : ℝ) := by linarith
        have h₁₂₂ : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by linarith)
        have h₁₂₃ : 0 ≤ (tetration y n : ℝ) := by exact_mod_cast h₁₀
        -- Use Real.rpow_le_rpow: if 0 ≤ x ≤ y and 0 ≤ z, then x^z ≤ y^z
        have h₁₂₄ : (x : ℝ) ^ (tetration y n : ℝ) ≤ (y : ℝ) ^ (tetration y n : ℝ) := by
          apply Real.rpow_le_rpow h₁₂₁ h₁₂₂ h₁₂₃
        exact_mod_cast h₁₂₄
      -- Combine the two inequalities
      have h₁₃ : x ^ tetration x n < y ^ tetration y n := by
        linarith
      linarith
  exact h₅ n hn

-- Helper lemma: tetration x k < x ^ tetration x k for x > 1
lemma tetration_lt_self_pow {x : ℝ} (hx : 1 < x) : ∀ k : ℕ, tetration x k < x ^ tetration x k := by
  intro k
  induction k with
  | zero =>
    -- Base case: tetration x 0 = 1 < x = x ^ 1 = x ^ tetration x 0
    simp [tetration]
    ; linarith
  | succ k ih =>
    -- Inductive step: tetration x (k+1) = x ^ tetration x k
    -- Need to show: x ^ tetration x k < x ^ (x ^ tetration x k)
    simp [tetration] at ih ⊢
    -- Use the fact that if a < b then x^a < x^b for x > 1
    have h₃ : 1 < (x : ℝ) := by exact_mod_cast hx
    have h₄ : (tetration x k : ℝ) < (x : ℝ) ^ (tetration x k : ℝ) := by exact_mod_cast ih
    have h₅ : (x : ℝ) ^ (tetration x k : ℝ) < (x : ℝ) ^ ((x : ℝ) ^ (tetration x k : ℝ)) := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by linarith) h₄
    exact_mod_cast h₅

-- Helper lemma: tetration x k < tetration x (k + 1) for x > 1
lemma tetration_lt_next {x : ℝ} (hx : 1 < x) : ∀ k : ℕ, tetration x k < tetration x (k + 1) := by
  intro k
  have h₁ : tetration x (k + 1) = x ^ tetration x k := by
    simp [tetration]
  have h₂ : tetration x k < x ^ tetration x k := tetration_lt_self_pow hx k
  rw [h₁]
  exact h₂

-- Monotonicity in height: if x > 1 and n ≤ m then tetration x n ≤ tetration x m
lemma tetration_mono_height {x : ℝ} {n m : ℕ} (hx : 1 < x) (hnm : n ≤ m) :
    tetration x n ≤ tetration x m := by
  have h₁ : 0 < x := by linarith
  have h₂ : ∀ k : ℕ, tetration x k < tetration x (k + 1) := tetration_lt_next hx

  -- Now use the fact that m = n + k for some k, and chain the inequalities
  have h₃ : ∃ k : ℕ, m = n + k := by
    use m - n
    have h₄ : n ≤ m := hnm
    have h₅ : m = n + (m - n) := by
      have h₆ : n ≤ m := hnm
      omega
    exact h₅
  obtain ⟨k, rfl⟩ := h₃
  -- Chain the inequalities: tetration x n ≤ tetration x (n+1) ≤ ... ≤ tetration x (n+k)
  have h₄ : tetration x n ≤ tetration x (n + k) := by
    have h₅ : ∀ i : ℕ, i ≤ k → tetration x n ≤ tetration x (n + i) := by
      intro i hi
      induction' i with i ih
      · simp
      · have h₆ : i ≤ k := by omega
        have h₇ : tetration x n ≤ tetration x (n + i) := ih h₆
        have h₈ : tetration x (n + i) < tetration x (n + i + 1) := h₂ (n + i)
        have h₉ : tetration x (n + i + 1) = tetration x (n + (i + 1)) := by
          rfl
        have h₁₀ : tetration x (n + i) ≤ tetration x (n + (i + 1)) := by
          linarith
        linarith
    have h₆ : k ≤ k := by linarith
    exact h₅ k h₆
  exact h₄

-- Strict monotonicity in height: if x > 1 and n < m then tetration x n < tetration x m
lemma tetration_strict_mono_height {x : ℝ} {n m : ℕ} (hx : 1 < x) (hnm : n < m) :
    tetration x n < tetration x m := by
  have h₁ : n ≤ m := by linarith
  have h₂ : ∀ k : ℕ, tetration x k < tetration x (k + 1) := tetration_lt_next hx
  -- Since n < m, there exists k such that m = n + k + 1
  have h₃ : ∃ k : ℕ, m = n + k + 1 := by
    use m - n - 1
    have h₄ : n < m := hnm
    have h₅ : m = n + (m - n) := by
      have h₆ : n ≤ m := by linarith
      omega
    have h₆ : m - n ≥ 1 := by
      omega
    have h₇ : m = n + (m - n - 1) + 1 := by
      have h₈ : m - n ≥ 1 := by omega
      have h₉ : m = n + (m - n) := by omega
      omega
    omega
  obtain ⟨k, rfl⟩ := h₃
  -- Chain the inequalities: tetration x n < tetration x (n+1) < ... < tetration x (n+k+1)
  have h₄ : tetration x n < tetration x (n + k + 1) := by
    have h₅ : ∀ i : ℕ, i ≤ k → tetration x n < tetration x (n + i + 1) := by
      intro i hi
      induction' i with i ih
      · -- Base case: i = 0
        have h₆ : tetration x n < tetration x (n + 1) := h₂ n
        simpa [add_assoc] using h₆
      · -- Inductive step
        have h₆ : i ≤ k := by omega
        have h₇ : tetration x n < tetration x (n + i + 1) := ih h₆
        have h₈ : tetration x (n + i + 1) < tetration x (n + i + 1 + 1) := h₂ (n + i + 1)
        have h₉ : tetration x (n + i + 1 + 1) = tetration x (n + (i + 1) + 1) := by
          rfl
        linarith
    have h₆ : k ≤ k := by linarith
    exact h₅ k h₆
  exact h₄

-- Helper lemma: log₂x ≤ √x for x ≥ 16
lemma log_two_le_sqrt {x : ℝ} (hx : (16 : ℝ) ≤ x) : Real.log x / Real.log 2 ≤ Real.sqrt x := by
  have h₁ : 0 < x := by linarith
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₃ : Real.log x / Real.log 2 ≤ Real.sqrt x := by
    have h₄ : Real.log x ≤ Real.log 2 * Real.sqrt x := by
      -- Use the substitution t = √x ≥ 4, then we need 2 * log t ≤ log 2 * t
      have h₅ : Real.sqrt x ≥ 4 := by
        apply Real.le_sqrt_of_sq_le
        norm_num at hx ⊢
        ; nlinarith
      have h₆ : Real.log x = 2 * Real.log (Real.sqrt x) := by
        have h₆₁ : Real.log x = Real.log ((Real.sqrt x) ^ 2) := by
          rw [Real.sq_sqrt (by linarith)]
        rw [h₆₁]
        have h₆₂ : Real.log ((Real.sqrt x) ^ 2) = 2 * Real.log (Real.sqrt x) := by
          rw [Real.log_pow]; norm_num
        rw [h₆₂]
      rw [h₆]
      -- Prove that for t ≥ 4, 2 * Real.log t ≤ Real.log 2 * t
      have h₇ : ∀ (t : ℝ), t ≥ 4 → 2 * Real.log t ≤ Real.log 2 * t := by
        intro t ht
        have h₈ : Real.log t ≤ (Real.log 2 / 2) * t := by
          -- Use the concavity of log: log t ≤ log 4 + (t - 4) / 4 for t ≥ 4
          have h₉ : Real.log t ≤ Real.log 4 + (t - 4) / 4 := by
            have h₁₀ : Real.log (t / 4) ≤ (t / 4) - 1 := by
              have h₁₁ : 0 < (t : ℝ) / 4 := by positivity
              have h₁₂ : Real.log (t / 4) ≤ (t / 4) - 1 := Real.log_le_sub_one_of_pos h₁₁
              exact h₁₂
            have h₁₂ : Real.log (t / 4) = Real.log t - Real.log 4 := by
              rw [Real.log_div (by positivity) (by positivity)]
            rw [h₁₂] at h₁₀
            have h₁₃ : Real.log 4 = 2 * Real.log 2 := by
              have h₁₄ : Real.log 4 = Real.log (2 ^ 2) := by norm_num
              rw [h₁₄]
              have h₁₅ : Real.log (2 ^ 2) = 2 * Real.log 2 := by
                rw [Real.log_pow]; norm_num
              rw [h₁₅]
            have h₁₄ : Real.log t - Real.log 4 ≤ (t / 4) - 1 := by linarith
            have h₁₅ : Real.log t ≤ Real.log 4 + (t / 4) - 1 := by linarith
            have h₁₆ : Real.log 4 + (t / 4) - 1 = Real.log 4 + (t - 4) / 4 := by ring
            linarith
          have h₁₀ : Real.log 4 + (t - 4) / 4 ≤ (Real.log 2 / 2) * t := by
            have h₁₁ : Real.log 4 = 2 * Real.log 2 := by
              have h₁₂ : Real.log 4 = Real.log (2 ^ 2) := by norm_num
              rw [h₁₂]
              have h₁₃ : Real.log (2 ^ 2) = 2 * Real.log 2 := by
                rw [Real.log_pow]; norm_num
              rw [h₁₃]
            rw [h₁₁]
            have h₁₂ : (2 : ℝ) * Real.log 2 + (t - 4) / 4 ≤ (Real.log 2 / 2) * t := by
              have h₁₃ : (2 : ℝ) * Real.log 2 - 1 > 0 := by
                have := Real.log_two_gt_d9
                norm_num at this ⊢
                ; nlinarith
              have h₁₄ : (t : ℝ) ≥ 4 := by exact_mod_cast ht
              nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
            linarith
          linarith
        have h₉ : 0 < t := by linarith
        have h₁₀ : 2 * Real.log t ≤ Real.log 2 * t := by
          have h₁₁ : Real.log t ≤ (Real.log 2 / 2) * t := h₈
          have h₁₂ : 2 * Real.log t ≤ 2 * ((Real.log 2 / 2) * t) := by
            nlinarith
          have h₁₃ : 2 * ((Real.log 2 / 2) * t) = Real.log 2 * t := by ring
          linarith
        exact h₁₀
      have h₈ : 2 * Real.log (Real.sqrt x) ≤ Real.log 2 * Real.sqrt x := by
        have h₉ : Real.sqrt x ≥ 4 := h₅
        have h₁₀ : 2 * Real.log (Real.sqrt x) ≤ Real.log 2 * Real.sqrt x := h₇ (Real.sqrt x) h₉
        exact h₁₀
      linarith
    have h₅ : 0 < Real.log 2 := by positivity
    have h₆ : Real.log x / Real.log 2 ≤ Real.sqrt x := by
      have h₇ : Real.log x ≤ Real.log 2 * Real.sqrt x := h₄
      have h₈ : 0 < Real.log 2 := by positivity
      have h₉ : Real.log x / Real.log 2 ≤ Real.sqrt x := by
        calc
          Real.log x / Real.log 2 ≤ (Real.log 2 * Real.sqrt x) / Real.log 2 := by gcongr
          _ = Real.sqrt x := by
            field_simp [h₈.ne']
      exact h₉
    exact h₆
  exact h₃

-- Helper lemma: 1 + 1/x^x < log₂x for x ≥ 16
lemma one_plus_inv_pow_lt_log_two {x : ℝ} (hx : (16 : ℝ) ≤ x) : (1 : ℝ) + 1 / (x ^ x) < Real.log x / Real.log 2 := by
  have h₁ : 0 < x := by linarith
  have h₂ : 1 < x := by linarith
  have h₃ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₄ : 0 < Real.log x := Real.log_pos (by linarith)
  have h₅ : 0 < x ^ x := Real.rpow_pos_of_pos h₁ x
  have h₆ : (1 : ℝ) + 1 / (x ^ x) < Real.log x / Real.log 2 := by
    have h₇ : 1 / (x ^ x) > 0 := by positivity
    have h₈ : Real.log x / Real.log 2 ≥ 1 := by
      -- log₂x ≥ 1 for x ≥ 2
      have h₈₁ : Real.log x ≥ Real.log 2 := by
        apply Real.log_le_log
        · linarith
        · linarith
      have h₈₂ : Real.log x / Real.log 2 ≥ 1 := by
        have h₈₃ : 0 < Real.log 2 := by positivity
        have h₈₄ : Real.log x / Real.log 2 ≥ 1 := by
          calc
            Real.log x / Real.log 2 ≥ Real.log 2 / Real.log 2 := by gcongr
            _ = 1 := by
              field_simp [h₈₃.ne']
        exact h₈₄
      exact h₈₂
    have h₉ : (1 : ℝ) + 1 / (x ^ x) < 2 := by
      have h₉₁ : 1 / (x ^ x) < 1 := by
        have h₉₂ : (x : ℝ) ^ x > 1 := by
          apply Real.one_lt_rpow
          · linarith
          · linarith
        have h₉₃ : 1 / (x ^ x) < 1 := by
          rw [div_lt_one (by positivity)]
          ; linarith
        exact h₉₃
      linarith
    -- For x ≥ 16, log₂x ≥ 4, so 1 + 1/x^x < 2 ≤ log₂x
    have h₁₀ : Real.log x / Real.log 2 ≥ 4 := by
      have h₁₀₁ : Real.log x ≥ 4 * Real.log 2 := by
        have h₁₀₂ : Real.log x ≥ Real.log (16 : ℝ) := by
          apply Real.log_le_log
          · linarith
          · linarith
        have h₁₀₃ : Real.log (16 : ℝ) = 4 * Real.log 2 := by
          have h₁₀₄ : Real.log (16 : ℝ) = Real.log (2 ^ 4 : ℝ) := by norm_num
          rw [h₁₀₄]
          have h₁₀₅ : Real.log (2 ^ 4 : ℝ) = 4 * Real.log 2 := by
            rw [Real.log_pow]; norm_num
          rw [h₁₀₅]
        linarith
      have h₁₀₄ : Real.log x / Real.log 2 ≥ 4 := by
        have h₁₀₅ : 0 < Real.log 2 := by positivity
        have h₁₀₆ : Real.log x / Real.log 2 ≥ 4 := by
          calc
            Real.log x / Real.log 2 ≥ (4 * Real.log 2) / Real.log 2 := by gcongr
            _ = 4 := by
              field_simp [h₁₀₅.ne']
        exact h₁₀₆
      exact h₁₀₄
    linarith
  exact h₆

-- Helper lemma: 3/2 ≤ 2^(2/3)
lemma three_half_le_two_pow_two_thirds : (3 / 2 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) / 3) := by
  have h₁ : (3 / 2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ 2 := by norm_num
  have h₂ : 0 < (3 / 2 : ℝ) := by norm_num
  have h₃ : 0 < (2 : ℝ) ^ ((2 : ℝ) / 3) := by positivity
  have h₄ : 0 < (2 : ℝ) := by norm_num
  -- Use the fact that if a^3 ≤ b^3 then a ≤ b for positive a, b
  have h₅ : (3 / 2 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) / 3) := by
    by_contra h
    have h₆ : (2 : ℝ) ^ ((2 : ℝ) / 3) < (3 / 2 : ℝ) := by linarith
    have h₇ : ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 < (3 / 2 : ℝ) ^ 3 := by
      gcongr
    have h₈ : ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 = (2 : ℝ) ^ 2 := by
      have h₈₁ : ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 = (2 : ℝ) ^ (((2 : ℝ) / 3) * 3) := by
        calc
          ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 = ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℝ) := by norm_cast
          _ = (2 : ℝ) ^ (((2 : ℝ) / 3) * 3) := by
            rw [← Real.rpow_mul (by positivity)]
      rw [h₈₁]
      have h₈₂ : ((2 : ℝ) / 3 : ℝ) * 3 = (2 : ℝ) := by norm_num
      rw [h₈₂]
      ; norm_num
    rw [h₈] at h₇
    norm_num at h₇
  exact h₅

-- Helper lemma: 17/16 < 16^(2^(2/3) - 3/2)
-- Proof using the fact that 2^(2/3) > 19/12 and 16^(1/12) = 2^(1/3) > 17/16
lemma seventeen_sixteenth_lt_sixteen_pow : (17 / 16 : ℝ) < (16 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2) := by
  have h₁ : (19 / 12 : ℝ) ^ 3 < (4 : ℝ) := by norm_num
  have h₂ : 0 < (19 / 12 : ℝ) := by norm_num
  have h₃ : 0 < (4 : ℝ) := by norm_num
  have h₄ : (19 / 12 : ℝ) < (4 : ℝ) ^ (1 / 3 : ℝ) := by
    by_contra h
    have h₅ : (4 : ℝ) ^ (1 / 3 : ℝ) ≤ (19 / 12 : ℝ) := by linarith
    have h₆ : ((4 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 ≤ (19 / 12 : ℝ) ^ 3 := by
      gcongr
    have h₇ : ((4 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (4 : ℝ) := by
      have h₇₁ : ((4 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (4 : ℝ) ^ ((1 / 3 : ℝ) * 3) := by
        calc
          ((4 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = ((4 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℝ) := by norm_cast
          _ = (4 : ℝ) ^ ((1 / 3 : ℝ) * 3) := by
            rw [← Real.rpow_mul (by positivity)]
      rw [h₇₁]
      have h₇₂ : ((1 / 3 : ℝ) * 3 : ℝ) = (1 : ℝ) := by norm_num
      rw [h₇₂]
      ; norm_num
    rw [h₇] at h₆
    norm_num [h₁] at h₆
  have h₅ : (4 : ℝ) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
    have h₅₁ : (4 : ℝ) ^ (1 / 3 : ℝ) = ((2 : ℝ) ^ (2 : ℝ)) ^ (1 / 3 : ℝ) := by
      norm_num [Real.rpow_two]
    rw [h₅₁]
    have h₅₂ : ((2 : ℝ) ^ (2 : ℝ)) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ ((2 : ℝ) * (1 / 3 : ℝ)) := by
      rw [← Real.rpow_mul (by positivity)]
    rw [h₅₂]
    ; norm_num
  have h₆ : (19 / 12 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) / 3) := by
    linarith
  have h₇ : (2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 > (1 / 12 : ℝ) := by
    have h₇₁ : (19 / 12 : ℝ) - 3 / 2 = (1 / 12 : ℝ) := by norm_num
    linarith
  have h₈ : (16 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2) > (16 : ℝ) ^ (1 / 12 : ℝ) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 16) (by linarith)
  have h₉ : (16 : ℝ) ^ (1 / 12 : ℝ) = (2 : ℝ) ^ (1 / 3 : ℝ) := by
    have h₉₁ : (16 : ℝ) ^ (1 / 12 : ℝ) = (2 ^ (4 : ℕ) : ℝ) ^ (1 / 12 : ℝ) := by norm_num
    rw [h₉₁]
    have h₉₂ : (2 ^ (4 : ℕ) : ℝ) ^ (1 / 12 : ℝ) = (2 : ℝ) ^ ((4 : ℝ) * (1 / 12 : ℝ)) := by
      have h₉₃ : (2 : ℝ) > 0 := by norm_num
      have h₉₄ : ((2 : ℝ) ^ (4 : ℕ) : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_cast
      rw [h₉₄]
      have h₉₅ : ((2 : ℝ) ^ (4 : ℝ)) ^ (1 / 12 : ℝ) = (2 : ℝ) ^ ((4 : ℝ) * (1 / 12 : ℝ)) := by
        rw [← Real.rpow_mul (by positivity)]
      rw [h₉₅]
    rw [h₉₂]
    have h₉₃ : ((4 : ℝ) * (1 / 12 : ℝ) : ℝ) = (1 / 3 : ℝ) := by norm_num
    rw [h₉₃]
  have h₁₀ : (16 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2) > (2 : ℝ) ^ (1 / 3 : ℝ) := by
    linarith
  have h₁₁ : (17 / 16 : ℝ) ^ 3 < (2 : ℝ) := by norm_num
  have h₁₂ : 0 < (17 / 16 : ℝ) := by norm_num
  have h₁₃ : 0 < (2 : ℝ) := by norm_num
  have h₁₄ : (17 / 16 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := by
    by_contra h
    have h₁₅ : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ (17 / 16 : ℝ) := by linarith
    have h₁₆ : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 ≤ (17 / 16 : ℝ) ^ 3 := by
      gcongr
    have h₁₇ : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (2 : ℝ) := by
      have h₁₇₁ : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (2 : ℝ) ^ ((1 / 3 : ℝ) * 3) := by
        calc
          ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℝ) := by norm_cast
          _ = (2 : ℝ) ^ ((1 / 3 : ℝ) * 3) := by
            rw [← Real.rpow_mul (by positivity)]
      rw [h₁₇₁]
      have h₁₇₂ : ((1 / 3 : ℝ) * 3 : ℝ) = (1 : ℝ) := by norm_num
      rw [h₁₇₂]
      ; norm_num
    rw [h₁₇] at h₁₆
    norm_num at h₁₆
  have h₁₅ : (17 / 16 : ℝ) < (16 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2) := by
    linarith
  exact h₁₅

-- Helper lemma: tetration x (n+1) ≥ 16 for x > 2 and n ≥ 2
lemma tetration_lower_bound {x : ℝ} {n : ℕ} (hx : 2 < x) (hn : 2 ≤ n) : (16 : ℝ) ≤ tetration x (n + 1) := by
  have h₁ : (2 : ℝ) < x := hx
  have h₂ : 1 < (x : ℝ) := by linarith
  have h₃ : (2 : ℕ) ≤ n := hn
  -- Prove by induction on m = n + 1 where m ≥ 3
  have h₄ : ∀ m : ℕ, 3 ≤ m → (16 : ℝ) ≤ tetration x m := by
    intro m hm
    induction' hm with m hm IH
    · -- Base case: m = 3
      have h₅ : tetration x 3 = x ^ (x ^ x) := by
        simp [tetration]
      rw [h₅]
      have h₆ : (x : ℝ) ^ (x ^ x) ≥ (16 : ℝ) := by
        have h₇ : (x : ℝ) ≥ (2 : ℝ) := by linarith
        have h₈ : (x : ℝ) ^ x ≥ (4 : ℝ) := by
          -- Prove x^x ≥ 4 for x ≥ 2
          have h₈₁ : (x : ℝ) ^ x ≥ (2 : ℝ) ^ (2 : ℝ) := by
            -- Use the fact that x^x is increasing for x ≥ 1
            have h₈₂ : (2 : ℝ) ≤ x := by linarith
            have h₈₃ : (2 : ℝ) ≤ x := by linarith
            -- Use rpow_le_rpow with same exponent
            have h₈₄ : (x : ℝ) ^ x ≥ (2 : ℝ) ^ x := by
              have h₈₅ : 0 ≤ (x : ℝ) := by linarith
              have h₈₆ : 0 ≤ (2 : ℝ) := by norm_num
              have h₈₇ : 0 ≤ (x : ℝ) := by linarith
              exact Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
            have h₈₅ : (2 : ℝ) ^ x ≥ (2 : ℝ) ^ (2 : ℝ) := by
              apply Real.rpow_le_rpow_of_exponent_le
              · norm_num
              · linarith
            linarith
          norm_num at h₈₁ ⊢
          ; linarith
        have h₉ : (x : ℝ) ^ (x ^ x) ≥ (x : ℝ) ^ (4 : ℝ) := by
          -- Since x ≥ 1 and x^x ≥ 4, we have x^(x^x) ≥ x^4
          have h₉₁ : (1 : ℝ) ≤ (x : ℝ) := by linarith
          have h₉₂ : (4 : ℝ) ≤ (x : ℝ) ^ x := by exact_mod_cast h₈
          have h₉₃ : (x : ℝ) ^ (x ^ x) ≥ (x : ℝ) ^ (4 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le
            · linarith
            · exact_mod_cast h₈
          exact h₉₃
        have h₁₀ : (x : ℝ) ^ (4 : ℝ) ≥ (16 : ℝ) := by
          -- Since x ≥ 2, x^4 ≥ 2^4 = 16
          have h₁₀₁ : (x : ℝ) ≥ (2 : ℝ) := by linarith
          have h₁₀₂ : (x : ℝ) ^ (4 : ℝ) ≥ (2 : ℝ) ^ (4 : ℝ) := by
            -- Use the fact that for a ≥ b ≥ 0, a^c ≥ b^c for c ≥ 0
            have h₁₀₃ : 0 ≤ (x : ℝ) := by linarith
            have h₁₀₄ : 0 ≤ (2 : ℝ) := by norm_num
            have h₁₀₅ : (x : ℝ) ≥ (2 : ℝ) := by linarith
            -- The exponent 4 is positive
            have h₁₀₆ : (0 : ℝ) ≤ (4 : ℝ) := by norm_num
            exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
          norm_num at h₁₀₂ ⊢
          ; linarith
        linarith
      linarith
    · -- Inductive step: assume true for m, prove for m + 1
      have h₅ : tetration x (m + 1) = x ^ tetration x m := by
        simp [tetration]
      rw [h₅]
      have h₆ : (x : ℝ) ^ tetration x m ≥ (16 : ℝ) := by
        have h₇ : (16 : ℝ) ≤ tetration x m := IH
        have h₈ : (x : ℝ) ≥ 2 := by linarith
        have h₉ : (x : ℝ) ^ tetration x m ≥ (x : ℝ) ^ (16 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          · linarith
          · exact_mod_cast (by linarith)
        have h₁₀ : (x : ℝ) ^ (16 : ℝ) ≥ (16 : ℝ) := by
          have h₁₁ : (x : ℝ) ^ (16 : ℝ) ≥ (2 : ℝ) ^ (16 : ℝ) := by
            have h₁₂ : 0 ≤ (x : ℝ) := by linarith
            have h₁₃ : 0 ≤ (2 : ℝ) := by norm_num
            have h₁₄ : (x : ℝ) ≥ (2 : ℝ) := by linarith
            have h₁₅ : (0 : ℝ) ≤ (16 : ℝ) := by norm_num
            exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
          norm_num at h₁₁ ⊢
          ; linarith
        linarith
      linarith
  have h₅ : (16 : ℝ) ≤ tetration x (n + 1) := h₄ (n + 1) (by linarith)
  exact h₅

-- Case 1: 0 < x ≤ 1 (then n > 1 by condition)
lemma case_x_le_one {x : ℝ} {n : ℕ} (hx : 0 < x) (hxle : x ≤ 1) (hnlt : 1 < n) :
    tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
  have h₁ : 0 < x := hx
  have h₂ : x ≤ 1 := hxle
  have h₃ : n ≥ 2 := by omega
  have h₄_pos : 0 < tetration x n := by
    have h : ∀ n : ℕ, 1 ≤ n → 0 < tetration x n := by
      intro n hn
      induction' hn with n hn IH
      · simp [tetration]
        ; assumption
      · simp [tetration]
        ; exact Real.rpow_pos_of_pos hx (tetration x n)
    exact h n (by omega)
  have h₄ : tetration x n ≤ 1 := by
    have h₄₁ : ∀ n : ℕ, tetration x n ≤ 1 := by
      intro n
      induction n with
      | zero => simp [tetration]
      | succ n ih =>
        rw [tetration]
        have h₄₂ : 0 ≤ tetration x n := by
          have h₄₃ : ∀ n : ℕ, 0 ≤ tetration x n := by
            intro n
            induction n with
            | zero => simp [tetration]
            | succ n ih =>
              rw [tetration]
              exact Real.rpow_nonneg (by linarith) (tetration x n)
          exact h₄₃ n
        have h₄₄ : 0 ≤ x := by linarith
        exact Real.rpow_le_one (by linarith) (by linarith) (by linarith)
    exact h₄₁ n

  have h₅ : 0 < (x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) ∧ (x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) ≤ 1 := by
    constructor
    · -- Prove 0 < y
      have h₅₁ : 0 < (x : ℝ) := by exact_mod_cast hx
      have h₅₂ : 0 < (2 : ℝ) := by norm_num
      have h₅₃ : 0 < (2 : ℝ) / 3 := by norm_num
      have h₅₄ : 0 < (2 : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) ((2 : ℝ) / 3)
      have h₅₅ : 0 < (x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) := by
        -- Use the fact that if a > 0, then a^b > 0 for any real b
        have h₅₆ : 0 < (2 : ℝ) ^ ((2 : ℝ) / 3) := by
          apply Real.rpow_pos_of_pos
          norm_num
        exact Real.rpow_pos_of_pos h₅₁ ((2 : ℝ) ^ ((2 : ℝ) / 3))
      exact h₅₅
    · -- Prove y ≤ 1
      have h₅₃ : (x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) ≤ 1 := by
        apply Real.rpow_le_one
        · -- Prove 0 ≤ x
          linarith
        · -- Prove x ≤ 1
          linarith
        · -- Prove 0 ≤ (2 : ℝ) ^ ((2 : ℝ) / 3)
          positivity
      exact h₅₃
  have h₆ : ∀ m : ℕ, m ≥ 1 → 0 < (x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) → 1 < iter_exp_two m ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
    intro m hm hy_pos
    have h₆₁ : 0 < (x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) := hy_pos
    -- Prove that for m ≥ 1 and y > 0, iter_exp_two m y > 1 (simplified proof)
    have h₆₂ : 1 < iter_exp_two m ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
      have h₆₃ : ∀ k : ℕ, k ≥ 1 → 0 < (x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) → 1 < iter_exp_two k ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
        intro k hk hz
        induction k with
        | zero =>
          exfalso
          linarith
        | succ k ih =>
          -- Inductive step
          cases k with
          | zero =>
            have h₆₄ : 0 < (x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) := hz
            have h₆₅ : (1 : ℝ) < 2 ^ ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
              apply Real.one_lt_rpow (by norm_num) h₆₄
            exact h₆₅
          | succ k =>
            -- We're proving P(k+1) where P(m) := (m ≥ 1 → 0 < y → 1 < iter_exp_two m y)
            -- IH : P(k) = (k ≥ 1 → 0 < y → 1 < iter_exp_two k y)
            -- We need to prove: (k+1 ≥ 1 → 0 < y → 1 < iter_exp_two (k+1) y)
            -- Since k+1 ≥ 1 is always true, we need: 0 < y → 1 < iter_exp_two (k+1) y
            -- Note that iter_exp_two (k+1) y = 2^(iter_exp_two k y)
            -- So we need: 0 < y → 1 < 2^(iter_exp_two k y)
            -- This follows from: 0 < y → 0 < iter_exp_two k y
            cases k with
            | zero =>
              have h₆₄ : 1 < iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := ih (by norm_num)
              have h₆₅ : 1 < iter_exp_two 2 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
                have h₆₆ : 1 < iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := h₆₄
                have h₆₇ : 1 < iter_exp_two 2 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
                  have h₆₇₁ : (1 : ℝ) < (2 : ℝ) := by norm_num
                  have h₆₇₂ : (1 : ℝ) < iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := h₆₆
                  have h₆₇₃ : (2 : ℝ) ^ (iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)))) > (2 : ℝ) ^ (1 : ℝ) := by
                    have h₆₇₄ : (1 : ℝ) < iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := h₆₆
                    have h₆₇₅ : (0 : ℝ) < iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) - (1 : ℝ) := by linarith
                    have h₆₇₆ : (1 : ℝ) < (2 : ℝ) := by norm_num
                    have h₆₇₇ : (1 : ℝ) < (2 : ℝ) ^ (iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) - (1 : ℝ)) := by
                      apply Real.one_lt_rpow
                      ; norm_num
                      linarith
                    have h₆₇₈ : (2 : ℝ) ^ (iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)))) = (2 : ℝ) ^ ((1 : ℝ) + (iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) - (1 : ℝ))) := by
                      ring_nf
                    have h₆₇₉ : (2 : ℝ) ^ ((1 : ℝ) + (iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) - (1 : ℝ))) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) - (1 : ℝ)) := by
                      rw [Real.rpow_add (by positivity)]
                    have h₆₈₀ : (2 : ℝ) ^ (iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)))) > (2 : ℝ) ^ (1 : ℝ) := by
                      calc
                        (2 : ℝ) ^ (iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)))) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) - (1 : ℝ)) := by
                          rw [h₆₇₈]
                          rw [h₆₇₉]
                        _ > (2 : ℝ) ^ (1 : ℝ) * 1 := by
                          gcongr
                        _ = (2 : ℝ) ^ (1 : ℝ) := by ring
                    exact h₆₈₀
                  have h₆₈₁ : iter_exp_two 2 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) = (2 : ℝ) ^ (iter_exp_two 1 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)))) := by
                    simp [iter_exp_two]
                  have h₆₈₂ : (2 : ℝ) ^ (1 : ℝ) < iter_exp_two 2 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
                    linarith
                  have h₆₈₃ : (1 : ℝ) < iter_exp_two 2 ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
                    linarith
                  exact h₆₈₃
                exact h₆₇
              exact h₆₅
            | succ k' =>
              -- Case k ≥ 1: we have ih : (k' + 1 + 1 ≥ 1) → 1 < iter_exp_two (k' + 1 + 1) y
              -- We need to prove: 1 < iter_exp_two (k' + 1 + 1 + 1) y
              -- Note that iter_exp_two ((k' + 1) + 1 + 1) y = 2^(iter_exp_two (k' + 1 + 1) y)
              -- So we need: 1 < 2^(iter_exp_two (k' + 1 + 1) y)
              -- This follows from: 0 < iter_exp_two (k' + 1 + 1) y
              have h₆₄ : 0 < (x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) := hz
              have h₆₅ : (1 : ℝ) < iter_exp_two (k' + 1 + 1) ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
                -- Apply the induction hypothesis
                have h₆₅₁ : (k' + 1 + 1 : ℕ) ≥ 1 := by
                  -- Since k' is a natural number, k' + 1 + 1 ≥ 1
                  have h : (k' : ℕ) ≥ 0 := Nat.zero_le k'
                  omega
                have h₆₅₂ : 1 < iter_exp_two (k' + 1 + 1) ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := ih h₆₅₁
                exact h₆₅₂
              have h₆₆ : 0 < iter_exp_two (k' + 1 + 1) ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
                -- Since 1 < iter_exp_two (k' + 1 + 1) y, we have 0 < iter_exp_two (k' + 1 + 1) y
                linarith
              have h₆₇ : iter_exp_two ((k' + 1) + 1 + 1) ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) = 2 ^ iter_exp_two (k' + 1 + 1) ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
                simp [iter_exp_two]
              rw [h₆₇]
              have h₆₈ : (1 : ℝ) < 2 ^ iter_exp_two (k' + 1 + 1) ((x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
                apply Real.one_lt_rpow (by norm_num) h₆₆
              exact h₆₈
      exact h₆₃ m hm hy_pos
    exact h₆₂
  have h₇ : 1 < iter_exp_two (n - 1) (x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) :=
    h₆ (n - 1) (by omega) h₅.1


  have h₉ : tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
    have h₉₁ : tetration x n ≤ 1 := h₄
    have h₉₂ : 1 < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := h₇
    have h₉₃ : tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
      linarith
    exact h₉₃

  exact h₉

-- Helper lemma: x < x^(2^(2/3)) for x > 1
lemma x_lt_x_pow_two_pow_two_thirds {x : ℝ} (hx : 1 < x) :
    x < x ^ (2 : ℝ) ^ ((2 : ℝ) / 3) := by
  have h₁ : (1 : ℝ) < 2 := by norm_num
  have h₂ : (0 : ℝ) < 2 := by norm_num
  have h₃ : (0 : ℝ) < (2 : ℝ) / 3 := by norm_num
  have h₄ : (1 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) / 3) := by
    apply Real.one_lt_rpow
    · norm_num
    · linarith
  have h₅ : Real.log x > 0 := Real.log_pos hx
  have h₆ : Real.log (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) = (2 : ℝ) ^ ((2 : ℝ) / 3) * Real.log x := by
    rw [Real.log_rpow (by positivity)]
  have h₇ : Real.log x < Real.log (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
    rw [h₆]
    have h₇₁ : (1 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) / 3) := h₄
    have h₇₂ : (0 : ℝ) < Real.log x := by linarith
    have h₇₃ : (1 : ℝ) * Real.log x < (2 : ℝ) ^ ((2 : ℝ) / 3) * Real.log x := by
      nlinarith
    linarith
  -- Since log is monotonic, we can conclude
  by_contra h
  have h₈ : x ^ (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ x := by linarith
  have h₉ : Real.log (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) ≤ Real.log x := by
    apply Real.log_le_log
    · positivity
    · linarith
  linarith

-- Local definitions for the base case proof (x < 16)
-- f(x) = log₂x * (x^x + 1)
noncomputable def f_base (x : ℝ) : ℝ :=
  (Real.log x / Real.log 2) * (x ^ x + 1)

-- g(x) = 2^(x^(2^(2/3)))
noncomputable def g_base (x : ℝ) : ℝ :=
  (2 : ℝ) ^ (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3))

-- f is monotonically increasing on [2, ∞)
lemma f_base_mono {x y : ℝ} (hx : 2 ≤ x) (hy : x ≤ y) : f_base x ≤ f_base y := by
  have h₁ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₂ : 0 < x := by linarith
  have h₃ : 0 < y := by linarith
  have h₄ : Real.log x / Real.log 2 ≤ Real.log y / Real.log 2 := by
    have h₄₁ : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hy
    have h₄₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
    -- Since denominator is the same and positive, we can just multiply both sides
    have h₄₃ : Real.log x / Real.log 2 ≤ Real.log y / Real.log 2 := by
      rw [div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
    exact h₄₃
  have h₅ : x ^ x + 1 ≤ y ^ y + 1 := by
    have h₅₁ : x ^ x ≤ y ^ y := by
      -- Prove that x^x is increasing for x ≥ 1
      have h₅₂ : 1 ≤ (x : ℝ) := by linarith
      have h₅₃ : 1 ≤ (y : ℝ) := by linarith
      have h₅₄ : (x : ℝ) ^ x ≤ (y : ℝ) ^ y := by
        -- Use the fact that f(t) = t^t is increasing for t ≥ 1/e
        have h₅₅ : Real.log (x ^ x) = x * Real.log x := by
          rw [Real.log_rpow (by linarith)]
        have h₅₆ : Real.log (y ^ y) = y * Real.log y := by
          rw [Real.log_rpow (by linarith)]
        have h₅₇ : x * Real.log x ≤ y * Real.log y := by
          -- Use the fact that t * log t is increasing for t ≥ 1
          have h₅₈ : ∀ (t : ℝ), 1 ≤ t → 0 < t := by
            intro t ht
            linarith
          have h₅₉ : 1 ≤ (x : ℝ) := by linarith
          have h₅₁₀ : 1 ≤ (y : ℝ) := by linarith
          -- Use the derivative approach or known inequality
          have h₅₁₁ : x * Real.log x ≤ y * Real.log y := by
            -- Prove using the fact that t ↦ t log t is increasing on [1, ∞)
            have h₅₁₂ : x ≤ y := hy
            have h₅₁₃ : 0 < x := by linarith
            have h₅₁₄ : 0 < y := by linarith
            -- Use the fact that the function f(t) = t log t has derivative 1 + log t ≥ 1 > 0 for t ≥ 1
            have h₅₁₅ : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hy
            have h₅₁₆ : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
            have h₅₁₇ : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
            nlinarith [mul_nonneg (sub_nonneg.mpr h₅₁₂) h₅₁₆, mul_nonneg (sub_nonneg.mpr h₅₁₂) h₅₁₇]
          exact h₅₁₁
        have h₅₁₂ : Real.log (x ^ x) ≤ Real.log (y ^ y) := by
          linarith
        have h₅₁₃ : 0 < x ^ x := Real.rpow_pos_of_pos (by linarith) x
        have h₅₁₄ : 0 < y ^ y := Real.rpow_pos_of_pos (by linarith) y
        have h₅₁₅ : Real.log (x ^ x) ≤ Real.log (y ^ y) := h₅₁₂
        have h₅₁₆ : x ^ x ≤ y ^ y := by
          by_contra h
          have h₅₁₇ : y ^ y < x ^ x := by linarith
          have h₅₁₈ : Real.log (y ^ y) < Real.log (x ^ x) := Real.log_lt_log (by positivity) h₅₁₇
          linarith
        exact h₅₁₆
      exact_mod_cast h₅₄
    linarith
  have h₆ : 0 ≤ Real.log x / Real.log 2 := by
    have h₆₁ : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h₆₂ : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    positivity
  have h₇ : 0 ≤ Real.log y / Real.log 2 := by
    have h₇₁ : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h₇₂ : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    positivity
  have h₈ : 0 ≤ x ^ x + 1 := by positivity
  have h₉ : 0 ≤ y ^ y + 1 := by positivity
  -- Now we need to show (log x / log 2) * (x^x + 1) ≤ (log y / log 2) * (y^y + 1)
  -- Since both factors are positive and increasing, their product is increasing
  have h₁₀ : f_base x = (Real.log x / Real.log 2) * (x ^ x + 1) := rfl
  have h₁₁ : f_base y = (Real.log y / Real.log 2) * (y ^ y + 1) := rfl
  rw [h₁₀, h₁₁]
  -- Use the fact that if 0 ≤ a ≤ b and 0 ≤ c ≤ d, then ac ≤ bd
  have h₁₂ : 0 ≤ Real.log x / Real.log 2 := h₆
  have h₁₃ : 0 ≤ Real.log y / Real.log 2 := h₇
  have h₁₄ : 0 ≤ x ^ x + 1 := by positivity
  have h₁₅ : 0 ≤ y ^ y + 1 := by positivity
  nlinarith [mul_nonneg h₁₂ h₁₄, mul_nonneg h₁₃ h₁₅,
    mul_nonneg (sub_nonneg.mpr h₄) h₁₄,
    mul_nonneg (sub_nonneg.mpr h₅) h₁₂]

-- g is monotonically increasing on [2, ∞)
lemma g_base_mono {x y : ℝ} (hx : 2 ≤ x) (hy : x ≤ y) : g_base x ≤ g_base y := by
  have h₁ : (2 : ℝ) ^ ((2 : ℝ) / 3) > 0 := by positivity
  have h₂ : (2 : ℝ) ^ ((2 : ℝ) / 3) > 1 := by
    have h₂₁ : (1 : ℝ) < (2 : ℝ) := by norm_num
    have h₂₂ : (0 : ℝ) < (2 : ℝ) / 3 := by norm_num
    have h₂₃ : (1 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) / 3) := Real.one_lt_rpow (by norm_num) (by norm_num)
    linarith
  have h₃ : 0 < x := by linarith
  have h₄ : 0 < y := by linarith
  have h₅ : x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) ≤ y ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) := by
    -- Since x ≤ y and the exponent is positive, x^e ≤ y^e
    have h₅₁ : 0 ≤ (x : ℝ) := by linarith
    have h₅₂ : 0 ≤ (y : ℝ) := by linarith
    have h₅₃ : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    have h₅₄ : 0 ≤ ((2 : ℝ) ^ ((2 : ℝ) / 3) : ℝ) := by positivity
    exact Real.rpow_le_rpow (by linarith) h₅₃ (by positivity)
  have h₆ : (2 : ℝ) ^ (x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) ≤ (2 : ℝ) ^ (y ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
    -- Since 2 > 1 and the exponent is increasing, 2^a ≤ 2^b
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact h₅
  have h₇ : g_base x = (2 : ℝ) ^ (x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := rfl
  have h₈ : g_base y = (2 : ℝ) ^ (y ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := rfl
  rw [h₇, h₈]
  exact h₆

-- General interval lemma: if f and g are increasing on [a, b] and f(b) < g(a), then f(x) < g(x) for all x ∈ [a, b]
lemma interval_bound {f g : ℝ → ℝ} {a b : ℝ} (_ : a ≤ b)
    (hf : ∀ x y, a ≤ x → x ≤ y → y ≤ b → f x ≤ f y)
    (hg : ∀ x y, a ≤ x → x ≤ y → y ≤ b → g x ≤ g y)
    (hfg : f b < g a) :
    ∀ (x : ℝ), a ≤ x → x ≤ b → f x < g x := by
  intro x hxa hxb
  have h₁ : f x ≤ f b := hf x b hxa hxb (by linarith)
  have h₂ : g a ≤ g x := hg a x (by linarith) hxa hxb
  have h₃ : f x < g x := by linarith
  exact h₃

-- Lemma: if an interval [a, b] is covered by subintervals [a_i, b_i] where f < g holds on each,
-- and x ∈ [a, b], then f(x) < g(x)
lemma interval_union {f g : ℝ → ℝ} {a b : ℝ} (_ : a ≤ b)
    (subintervals : List (ℝ × ℝ))
    (hcover : ∀ (x : ℝ), a ≤ x → x ≤ b → ∃ (ab : ℝ × ℝ), ab ∈ subintervals ∧ ab.1 ≤ x ∧ x ≤ ab.2)
    (hsub : ∀ (ab : ℝ × ℝ), ab ∈ subintervals → ∀ (x : ℝ), ab.1 ≤ x → x ≤ ab.2 → f x < g x) :
    ∀ (x : ℝ), a ≤ x → x ≤ b → f x < g x := by
  intro x hxa hxb
  obtain ⟨ab, hab_sub, hx1, hx2⟩ := hcover x hxa hxb
  have h₁ : f x < g x := hsub ab hab_sub x hx1 hx2
  exact h₁

-- Case 2: 1 < x ≤ 2
lemma case_one_lt_x_le_two {x : ℝ} {n : ℕ} (hx : 1 < x) (hxle : x ≤ 2) (hn : 1 ≤ n) :
    tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
  have h_main : ∀ (n : ℕ), 1 ≤ n → tetration x n ≤ iter_exp_two (n - 1) x := by
    intro n hn
    induction' hn with n hn IH
    · -- Base case: n = 1
      norm_num [tetration, iter_exp_two]
    · -- Inductive step: assume true for n, prove for n+1
        have h₁ : tetration x n ≤ iter_exp_two (n - 1) x := IH
        have h₂ : tetration x (n + 1) = x ^ tetration x n := by
          simp [tetration]
        have h₃ : 0 ≤ (iter_exp_two (n - 1) x : ℝ) := by
          have h₄ : ∀ (m : ℕ), 0 ≤ (iter_exp_two m x : ℝ) := by
            intro m
            induction m with
            | zero =>
              -- Base case: iter_exp_two 0 x = x > 1 > 0
              have h₅ : 1 < x := hx
              have h₆ : (0 : ℝ) < x := by linarith
              exact le_of_lt h₆
            | succ m ih =>
              -- Inductive step: iter_exp_two (m+1) x = 2^(iter_exp_two m x) > 0
              have h₆ : (iter_exp_two m x : ℝ) ≥ 0 := ih
              have h₇ : (iter_exp_two (m + 1) x : ℝ) = 2 ^ (iter_exp_two m x : ℝ) := by
                simp [iter_exp_two]
              rw [h₇]
              -- 2^y > 0 for any real y
              have h₈ : (2 : ℝ) > 0 := by norm_num
              have h₉ : (2 : ℝ) ^ (iter_exp_two m x : ℝ) > 0 := by
                apply Real.rpow_pos_of_pos
                norm_num
              linarith
          exact h₄ (n - 1)
        have h₄ : x ^ tetration x n ≤ x ^ (iter_exp_two (n - 1) x) := by
          -- Since x > 1, the function f(y) = x^y is strictly increasing
          have h₅ : 1 < x := hx
          have h₆ : tetration x n ≤ iter_exp_two (n - 1) x := h₁
          have h₇ : x ^ tetration x n ≤ x ^ (iter_exp_two (n - 1) x) := by
            -- Use the fact that if 1 < x and y ≤ z, then x^y ≤ x^z
            have h₈ : 0 ≤ (iter_exp_two (n - 1) x : ℝ) := h₃
            -- Use the property of real power functions via logarithms
            have h₉ : Real.log (x ^ tetration x n) = tetration x n * Real.log x := by
              rw [Real.log_rpow (by linarith)]
            have h₁₀ : Real.log (x ^ (iter_exp_two (n - 1) x)) = (iter_exp_two (n - 1) x) * Real.log x := by
              rw [Real.log_rpow (by linarith)]
            have h₁₁ : tetration x n * Real.log x ≤ (iter_exp_two (n - 1) x) * Real.log x := by
              -- Since 1 < x, we have Real.log x > 0
              have h₁₁₁ : Real.log x > 0 := Real.log_pos h₅
              nlinarith
            have h₁₂ : Real.log (x ^ tetration x n) ≤ Real.log (x ^ (iter_exp_two (n - 1) x)) := by
              linarith
            have h₁₃ : x ^ tetration x n ≤ x ^ (iter_exp_two (n - 1) x) := by
              by_contra h
              -- If x ^ tetration x n > x ^ (iter_exp_two (n - 1) x), then
              -- log(x ^ tetration x n) > log(x ^ (iter_exp_two (n - 1) x))
              have h₁₄ : x ^ (iter_exp_two (n - 1) x) < x ^ tetration x n := by linarith
              have h₁₅ : Real.log (x ^ (iter_exp_two (n - 1) x)) < Real.log (x ^ tetration x n) := by
                apply Real.log_lt_log (by positivity)
                linarith
              linarith
            exact h₁₃
          exact h₇
        have h₅ : x ^ (iter_exp_two (n - 1) x) ≤ 2 ^ (iter_exp_two (n - 1) x) := by
          -- Since 1 < x ≤ 2, we have x^y ≤ 2^y for any y ≥ 0
          have h₆ : 0 ≤ x := by linarith
          have h₇ : x ≤ 2 := hxle
          have h₈ : 0 ≤ (iter_exp_two (n - 1) x : ℝ) := h₃
          have h₉ : x ^ (iter_exp_two (n - 1) x) ≤ 2 ^ (iter_exp_two (n - 1) x) := by
            exact Real.rpow_le_rpow h₆ h₇ h₈
          exact h₉
        have h₆ : 2 ^ (iter_exp_two (n - 1) x) = iter_exp_two n x := by
          have h₇ : n ≥ 1 := by exact hn
          have h₈ : iter_exp_two n x = 2 ^ (iter_exp_two (n - 1) x) := by
            have h₉ : n = (n - 1) + 1 := by
              omega
            rw [h₉]
            simp [iter_exp_two]
          linarith
        calc
          tetration x (n + 1) = x ^ tetration x n := h₂
          _ ≤ x ^ (iter_exp_two (n - 1) x) := h₄
          _ ≤ 2 ^ (iter_exp_two (n - 1) x) := h₅
          _ = iter_exp_two n x := h₆

  have h₁ : tetration x n ≤ iter_exp_two (n - 1) x := h_main n hn
  have h₂ : iter_exp_two (n - 1) x < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
    -- Prove that x < x^(2^(2/3)) when 1 < x ≤ 2
    have h₃ : (1 : ℝ) < x := hx
    have h₄ : x < x ^ (2 : ℝ) ^ ((2 : ℝ) / 3) := x_lt_x_pow_two_pow_two_thirds h₃
    -- Since iter_exp_two (n-1) is monotonic in its second argument
    have h₅ : ∀ (k : ℕ) (y z : ℝ), y < z → iter_exp_two k y < iter_exp_two k z := by
      intro k
      induction k with
      | zero =>
        intro y z hyz
        -- Base case: iter_exp_two 0 y = y, iter_exp_two 0 z = z
        exact hyz
      | succ k ih =>
        intro y z hyz
        -- Inductive step: iter_exp_two (k+1) y = 2^(iter_exp_two k y)
        simp_all [iter_exp_two]
    have h₆ : iter_exp_two (n - 1) x < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := h₅ (n - 1) x (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) h₄
    exact h₆

  have h₃ : tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
    linarith

  exact h₃

-- Case 3: n = 1 (then x > 1 by condition)
lemma case_n_eq_one {x : ℝ} {n : ℕ} (hn : n = 1) (hxgt : 1 < x) :
    tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
  have h₁ : tetration x n = x := by
    rw [hn]
    simp [tetration]
  have h₂ : iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) = x ^ (2 : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [hn]
    simp [iter_exp_two]
  rw [h₁, h₂]
  -- Prove that x < x^(2^(2/3)) when x > 1
  have h₃ : x < x ^ (2 : ℝ) ^ ((2 : ℝ) / 3) := x_lt_x_pow_two_pow_two_thirds hxgt
  exact h₃

-- Base case for x < 16
lemma case_x_gt_two_base_x_lt_16 {x : ℝ} (hx : 2 < x) (hx16 : x < 16) :
    (Real.log x / Real.log 2) * (tetration x 2 + 1) < iter_exp_two (2 - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
  sorry

-- Base case for x ≥ 16
lemma case_x_gt_two_base_x_ge_16 {x : ℝ} (hx : 2 < x) (hx16 : 16 ≤ x) :
    (Real.log x / Real.log 2) * (tetration x 2 + 1) < iter_exp_two (2 - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
  have h₂ : tetration x 2 = x ^ x := by
    norm_num [tetration]
  have h₃ : iter_exp_two (2 - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) = (2 : ℝ) ^ (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
    norm_num [iter_exp_two]
  rw [h₂, h₃]
  have h₅ : 1 < x := by linarith
  have h₆ : 0 < x := by linarith
  have h₇ : Real.log x / Real.log 2 ≤ Real.sqrt x := log_two_le_sqrt hx16
  have h₈ : (1 : ℝ) + 1 / (x ^ x) < Real.log x / Real.log 2 := one_plus_inv_pow_lt_log_two hx16
  have h₉ : 0 < x ^ x := Real.rpow_pos_of_pos h₆ x
  have h₁₀ : 0 < Real.log x := Real.log_pos (by linarith)
  have h₁₁ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₁₂ : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have h₁₃ : 0 < x ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos h₆ _
  have h₁₄ : 0 < x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) := Real.rpow_pos_of_pos h₆ _
  have h₁₅ : 0 < (2 : ℝ) ^ (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by positivity
  -- Use the chain of inequalities from the Japanese proof
  have h_nonzero : (x ^ x : ℝ) ≠ 0 := by positivity
  have h₁₆₁ : (Real.log x / Real.log 2) * (x ^ x + 1) = (Real.log x / Real.log 2) * (1 + 1 / (x ^ x)) * (x ^ x) := by
    have h₁₆₄ : (1 : ℝ) + 1 / (x ^ x) = (x ^ x + 1) / (x ^ x) := by
      field_simp [h_nonzero]
    calc
      (Real.log x / Real.log 2) * (x ^ x + 1) = (Real.log x / Real.log 2) * ((x ^ x + 1) / (x ^ x) * (x ^ x)) := by
        field_simp [h_nonzero]
      _ = (Real.log x / Real.log 2) * ((1 + 1 / (x ^ x)) * (x ^ x)) := by
        rw [h₁₆₄]
      _ = (Real.log x / Real.log 2) * (1 + 1 / (x ^ x)) * (x ^ x) := by ring
  have h₁₆₂ : (Real.log x / Real.log 2) * (1 + 1 / (x ^ x)) * (x ^ x) < (Real.sqrt x) ^ 2 * (x ^ x) := by
    have h₁₆₄ : (Real.log x / Real.log 2) * (1 + 1 / (x ^ x)) < (Real.sqrt x) ^ 2 := by
      have h₁₆₄ : (1 : ℝ) + 1 / (x ^ x) < Real.log x / Real.log 2 := h₈
      have h₁₆₅ : Real.log x / Real.log 2 ≤ Real.sqrt x := h₇
      have h₁₆₆ : 0 < Real.log x / Real.log 2 := by positivity
      have h₁₆₇ : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
      have h₁₆₈ : 0 < (Real.sqrt x) ^ 2 := by positivity
      have h₁₆₉ : (Real.log x / Real.log 2) * (1 + 1 / (x ^ x)) < (Real.log x / Real.log 2) * (Real.log x / Real.log 2) := by
        gcongr
      have h₁₇₀ : (Real.log x / Real.log 2) * (Real.log x / Real.log 2) ≤ Real.sqrt x * Real.sqrt x := by
        gcongr
      have h₁₇₁ : Real.sqrt x * Real.sqrt x = (Real.sqrt x) ^ 2 := by ring
      nlinarith
    have h₁₇₂ : 0 < (x ^ x : ℝ) := by positivity
    have h₁₇₃ : 0 < (Real.sqrt x) ^ 2 := by positivity
    nlinarith
  have h₁₆₃ : (Real.sqrt x) ^ 2 * (x ^ x) = x ^ (x + 1) := by
    have h₁₆₆ : (Real.sqrt x) ^ 2 = x := by
      rw [Real.sq_sqrt (by linarith)]
    rw [h₁₆₆]
    have h₁₆₇ : (x : ℝ) * (x ^ x : ℝ) = x ^ (x + 1) := by
      have h₁₆₈ : (x : ℝ) > 0 := by positivity
      have h₁₆₉ : (x : ℝ) * (x ^ x : ℝ) = x ^ (1 + x) := by
        have h₁₇₀ : (x : ℝ) * (x ^ x : ℝ) = x ^ 1 * x ^ x := by norm_num
        rw [h₁₇₀]
        have h₁₇₁ : (x : ℝ) ^ (1 + x) = x ^ 1 * x ^ x := by
          rw [Real.rpow_add (by positivity)]
          ; norm_num
        linarith
      have h₁₇₂ : (x : ℝ) ^ (1 + x) = x ^ (x + 1) := by
        congr 1
        ; ring_nf
      rw [h₁₆₉, h₁₇₂]
    rw [h₁₆₇]
  have h₁₆₄ : (x : ℝ) ^ (x + 1) = (2 : ℝ) ^ ((Real.log x / Real.log 2) * (x + 1)) := by
    have h₁₆₇ : 0 < (x : ℝ) := by linarith
    have h₁₆₈ : 0 < (2 : ℝ) := by norm_num
    have h₁₆₉ : 0 < Real.log x := Real.log_pos (by linarith)
    have h₁₇₀ : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h₁₇₁ : 0 < (x : ℝ) ^ (x + 1) := by positivity
    have h₁₇₂ : 0 < (2 : ℝ) ^ ((Real.log x / Real.log 2) * (x + 1)) := by positivity
    have h₁₇₃ : Real.log ((x : ℝ) ^ (x + 1)) = Real.log ((2 : ℝ) ^ ((Real.log x / Real.log 2) * (x + 1))) := by
      have h₁₇₄ : Real.log ((x : ℝ) ^ (x + 1)) = (x + 1) * Real.log x := by
        rw [Real.log_rpow (by positivity)]
      have h₁₇₅ : Real.log ((2 : ℝ) ^ ((Real.log x / Real.log 2) * (x + 1))) = ((Real.log x / Real.log 2) * (x + 1)) * Real.log 2 := by
        rw [Real.log_rpow (by positivity)]
      have h₁₇₆ : (x + 1 : ℝ) * Real.log x = ((Real.log x / Real.log 2) * (x + 1)) * Real.log 2 := by
        have h₁₇₇ : Real.log x / Real.log 2 * Real.log 2 = Real.log x := by
          field_simp [h₁₇₀.ne']
        calc
          (x + 1 : ℝ) * Real.log x = (x + 1 : ℝ) * (Real.log x / Real.log 2 * Real.log 2) := by rw [h₁₇₇]
          _ = ((Real.log x / Real.log 2) * (x + 1)) * Real.log 2 := by ring
      calc
        Real.log ((x : ℝ) ^ (x + 1)) = (x + 1) * Real.log x := by rw [h₁₇₄]
        _ = ((Real.log x / Real.log 2) * (x + 1)) * Real.log 2 := by rw [h₁₇₆]
        _ = Real.log ((2 : ℝ) ^ ((Real.log x / Real.log 2) * (x + 1))) := by rw [h₁₇₅]
    have h₁₇₄ : (x : ℝ) ^ (x + 1) = (2 : ℝ) ^ ((Real.log x / Real.log 2) * (x + 1)) := by
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr h₁₇₁) (Set.mem_Ioi.mpr h₁₇₂)
      rw [h₁₇₃]
    exact h₁₇₄
  have h₁₆₅ : (2 : ℝ) ^ ((Real.log x / Real.log 2) * (x + 1)) ≤ (2 : ℝ) ^ (Real.sqrt x * (x + 1)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h₁₆₆ : (Real.log x / Real.log 2) * (x + 1) ≤ Real.sqrt x * (x + 1) := by
      have h₁₆₇ : Real.log x / Real.log 2 ≤ Real.sqrt x := h₇
      have h₁₆₈ : 0 ≤ x + 1 := by linarith
      nlinarith
    linarith
  have h₁₆₆ : (2 : ℝ) ^ (Real.sqrt x * (x + 1)) = (2 : ℝ) ^ (x ^ (3 / 2 : ℝ) * (1 + 1 / x)) := by
    have h₁₆₇ : Real.sqrt x * (x + 1 : ℝ) = x ^ (3 / 2 : ℝ) * (1 + 1 / x) := by
      have h₁₆₈ : Real.sqrt x = x ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      rw [h₁₆₈]
      have h₁₆₉ : (x : ℝ) ^ (1 / 2 : ℝ) * (x + 1 : ℝ) = x ^ (3 / 2 : ℝ) * (1 + 1 / x) := by
        have h₁₇₀ : 0 < x := by linarith
        have h₁₇₁ : (x : ℝ) ^ (1 / 2 : ℝ) * (x + 1 : ℝ) = (x : ℝ) ^ (1 / 2 : ℝ) * x * (1 + 1 / x) := by
          field_simp [h₁₇₀.ne']
        rw [h₁₇₁]
        have h₁₇₂ : (x : ℝ) ^ (1 / 2 : ℝ) * x = x ^ (3 / 2 : ℝ) := by
          have h₁₇₃ : (x : ℝ) ^ (1 / 2 : ℝ) * x = (x : ℝ) ^ (1 / 2 : ℝ) * (x : ℝ) ^ (1 : ℝ) := by norm_num
          rw [h₁₇₃]
          have h₁₇₄ : (x : ℝ) ^ (1 / 2 : ℝ) * (x : ℝ) ^ (1 : ℝ) = (x : ℝ) ^ ((1 / 2 : ℝ) + (1 : ℝ)) := by
            rw [← Real.rpow_add (by positivity)]
          rw [h₁₇₄]
          have h₁₇₅ : ((1 / 2 : ℝ) + (1 : ℝ) : ℝ) = (3 / 2 : ℝ) := by norm_num
          rw [h₁₇₅]
        rw [h₁₇₂]
      rw [h₁₆₉]
    rw [h₁₆₇]
  have h₁₆₇ : (2 : ℝ) ^ (x ^ (3 / 2 : ℝ) * (1 + 1 / x)) ≤ (2 : ℝ) ^ ((1 + 1 / (16 : ℝ)) * x ^ (3 / 2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h₁₆₈ : (x : ℝ) ^ (3 / 2 : ℝ) * (1 + 1 / x) ≤ (1 + 1 / (16 : ℝ)) * x ^ (3 / 2 : ℝ) := by
      have h₁₆₉ : (1 : ℝ) + 1 / x ≤ (1 : ℝ) + 1 / (16 : ℝ) := by
        have h₁₇₀ : (1 : ℝ) / x ≤ (1 : ℝ) / (16 : ℝ) := by
          -- Prove 1/x ≤ 1/16 for x ≥ 16 using the fact that reciprocal is decreasing
          have h₁₇₁ : 0 < (x : ℝ) := by positivity
          have h₁₇₂ : (x : ℝ) ≥ 16 := by exact_mod_cast hx16
          have h₁₇₃ : (1 : ℝ) / x ≤ (1 : ℝ) / (16 : ℝ) := by
            apply one_div_le_one_div_of_le
            · positivity
            · linarith
          exact h₁₇₃
        linarith
      have h₁₇₀ : 0 ≤ (x : ℝ) ^ (3 / 2 : ℝ) := by positivity
      nlinarith
    linarith
  have h₁₆₈ : (2 : ℝ) ^ ((1 + 1 / (16 : ℝ)) * x ^ (3 / 2 : ℝ)) < (2 : ℝ) ^ ((16 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    have h₁₆₉ : ((1 + 1 / (16 : ℝ)) : ℝ) * x ^ (3 / 2 : ℝ) < ((16 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) := by
      have h₁₇₀ : (1 + 1 / (16 : ℝ) : ℝ) < (16 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) := by
        -- Use the helper lemma seventeen_sixteenth_lt_sixteen_pow
        have h₁₇₁ : (1 + 1 / (16 : ℝ) : ℝ) = (17 / 16 : ℝ) := by norm_num
        rw [h₁₇₁]
        have h₁₇₂ : (17 / 16 : ℝ) < (16 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) := by
          exact seventeen_sixteenth_lt_sixteen_pow
        linarith
      have h₁₇₁ : 0 < (x : ℝ) ^ (3 / 2 : ℝ) := by positivity
      nlinarith
    linarith
  have h₁₆₉ : (2 : ℝ) ^ ((16 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) ≤ (2 : ℝ) ^ (x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h₁₇₀ : ((16 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) ≤ (x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) := by
      have h₁₇₁ : (16 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) ≤ x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) := by
        -- Use the fact that the exponent is non-negative (3/2 ≤ 2^(2/3))
        have h₁₇₂ : (3 / 2 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) / 3) := three_half_le_two_pow_two_thirds
        have h₁₇₃ : 0 ≤ (2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 := by linarith
        apply Real.rpow_le_rpow (by norm_num) (by linarith)
        (try norm_num); (try linarith)
      have h₁₇₂ : 0 ≤ (x : ℝ) ^ (3 / 2 : ℝ) := by positivity
      nlinarith
    linarith
  have h₁₇₀ : (2 : ℝ) ^ (x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) = (2 : ℝ) ^ (x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
    have h₁₇₁ : (x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) * x ^ (3 / 2 : ℝ) = x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) := by
      have h₁₇₂ : 0 < (x : ℝ) := by linarith
      have h₁₇₃ : (x : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) * x ^ (3 / 2 : ℝ) = x ^ (((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) + 3 / 2 : ℝ) := by
        rw [← Real.rpow_add (by positivity)]
      rw [h₁₇₃]
      have h₁₇₄ : (((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) + 3 / 2 : ℝ) = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
        ring_nf
      rw [h₁₇₄]
    rw [h₁₇₁]
  have h₁₇₀' : (2 : ℝ) ^ (x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) = (2 : ℝ) ^ (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by rfl
  have h_main : (Real.log x / Real.log 2) * (x ^ x + 1) < (2 : ℝ) ^ (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
    calc
      (Real.log x / Real.log 2) * (x ^ x + 1) = (Real.log x / Real.log 2) * (1 + 1 / (x ^ x)) * (x ^ x) := by rw [h₁₆₁]
      _ < (Real.sqrt x) ^ 2 * (x ^ x) := h₁₆₂
      _ = x ^ (x + 1) := by rw [h₁₆₃]
      _ = (2 : ℝ) ^ ((Real.log x / Real.log 2) * (x + 1)) := by rw [h₁₆₄]
      _ ≤ (2 : ℝ) ^ (Real.sqrt x * (x + 1)) := h₁₆₅
      _ = (2 : ℝ) ^ (x ^ (3 / 2 : ℝ) * (1 + 1 / x)) := by rw [h₁₆₆]
      _ ≤ (2 : ℝ) ^ ((1 + 1 / (16 : ℝ)) * x ^ (3 / 2 : ℝ)) := h₁₆₇
      _ < (2 : ℝ) ^ ((16 : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := h₁₆₈
      _ ≤ (2 : ℝ) ^ (x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3) - 3 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := h₁₆₉
      _ = (2 : ℝ) ^ (x ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by rw [h₁₇₀]
      _ = (2 : ℝ) ^ (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by rw [h₁₇₀']
  exact h_main

-- Inductive step for the main proof
lemma case_x_gt_two_inductive_step {x : ℝ} {n : ℕ} (hx : 2 < x) (hn : 2 ≤ n) (hIH : (Real.log x / Real.log 2) * (tetration x n + 1) < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3))) :
    (Real.log x / Real.log 2) * (tetration x (n + 1) + 1) < iter_exp_two (n + 1 - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
  have h₁ : 1 < (x : ℝ) := by linarith
  have h₂ : 0 < (x : ℝ) := by linarith
  have h₃ : (Real.log x / Real.log 2) > 0 := by
    have h₃₁ : Real.log x > 0 := Real.log_pos (by linarith)
    have h₃₂ : Real.log 2 > 0 := Real.log_pos (by norm_num)
    positivity
  have h₄ : tetration x (n + 1) = x ^ tetration x n := by
    simp [tetration]
  have h₅ : (16 : ℝ) ≤ tetration x (n + 1) := tetration_lower_bound hx hn
  have h₆ : 0 < tetration x (n + 1) := by
    have h₆₁ : ∀ n : ℕ, 0 < tetration x n := by
      intro n
      induction n with
      | zero => simp [tetration]
      | succ n ih =>
        rw [tetration]
        exact Real.rpow_pos_of_pos h₂ (tetration x n)
    exact h₆₁ (n + 1)
  have h₇ : (1 : ℝ) + 1 / (tetration x (n + 1)) ≤ (17 / 16 : ℝ) := by
    have h₇₁ : (1 : ℝ) / (tetration x (n + 1)) ≤ 1 / 16 := by
      have h₇₂ : (tetration x (n + 1) : ℝ) ≥ 16 := by exact_mod_cast h₅
      have h₇₃ : 0 < (tetration x (n + 1) : ℝ) := by positivity
      have h₇₄ : (1 : ℝ) / (tetration x (n + 1)) ≤ 1 / 16 := by
        apply one_div_le_one_div_of_le
        · positivity
        · exact_mod_cast h₅
      exact h₇₄
    norm_num at h₇₁ ⊢
    ; linarith
  have h₈ : (17 / 16 : ℝ) < (9 / 8 : ℝ) := by norm_num
  have h₉ : (1 : ℝ) + 1 / (tetration x (n + 1)) < (9 / 8 : ℝ) := by linarith
  have h₁₀ : (Real.log x / Real.log 2) * (tetration x (n + 1) + 1) = (Real.log x / Real.log 2) * tetration x (n + 1) * (1 + 1 / tetration x (n + 1)) := by
    have h₁₀₂ : 0 < tetration x (n + 1) := h₆
    have h₁₀₁ : (Real.log x / Real.log 2) * (tetration x (n + 1) + 1) = (Real.log x / Real.log 2) * (tetration x (n + 1) * (1 + 1 / tetration x (n + 1))) := by
      field_simp [h₁₀₂.ne']
    calc
      (Real.log x / Real.log 2) * (tetration x (n + 1) + 1) = (Real.log x / Real.log 2) * (tetration x (n + 1) * (1 + 1 / tetration x (n + 1))) := by rw [h₁₀₁]
      _ = (Real.log x / Real.log 2) * tetration x (n + 1) * (1 + 1 / tetration x (n + 1)) := by ring
  have h₁₁ : (Real.log x / Real.log 2) * (tetration x (n + 1) + 1) < (Real.log x / Real.log 2) * tetration x (n + 1) * (9 / 8 : ℝ) := by
    have h₁₁₁ : 0 < (Real.log x / Real.log 2) := h₃
    have h₁₁₂ : 0 < tetration x (n + 1) := h₆
    have h₁₁₃ : 0 < (Real.log x / Real.log 2) * tetration x (n + 1) := by positivity
    have h₁₁₄ : (1 : ℝ) + 1 / (tetration x (n + 1)) < (9 / 8 : ℝ) := h₉
    calc
      (Real.log x / Real.log 2) * (tetration x (n + 1) + 1) = (Real.log x / Real.log 2) * tetration x (n + 1) * (1 + 1 / tetration x (n + 1)) := by rw [h₁₀]
      _ < (Real.log x / Real.log 2) * tetration x (n + 1) * (9 / 8 : ℝ) := by
        gcongr
  have h₁₂ : (Real.log x / Real.log 2) * tetration x (n + 1) * (9 / 8 : ℝ) = (9 / 8 : ℝ) * (Real.log x / Real.log 2) * tetration x (n + 1) := by ring
  have h₁₃ : (9 / 8 : ℝ) * (Real.log x / Real.log 2) * tetration x (n + 1) < x * tetration x (n + 1) := by
    have h₁₃₁ : (9 / 8 : ℝ) * (Real.log x / Real.log 2) < x := by
      have h₁₃₂ : (9 / 8 : ℝ) * Real.log x / Real.log 2 < x := lemma_log_bound (by linarith)
      have h₁₃₃ : (9 / 8 : ℝ) * (Real.log x / Real.log 2) = (9 / 8 : ℝ) * Real.log x / Real.log 2 := by ring
      rw [h₁₃₃] at *
      exact h₁₃₂
    have h₁₃₄ : 0 < tetration x (n + 1) := h₆
    have h₁₃₅ : 0 < (9 / 8 : ℝ) * (Real.log x / Real.log 2) := by positivity
    nlinarith
  have h₁₄ : x * tetration x (n + 1) = x ^ (tetration x n + 1) := by
    have h₁₄₁ : tetration x (n + 1) = x ^ tetration x n := h₄
    rw [h₁₄₁]
    have h₁₄₂ : x * (x ^ tetration x n) = x ^ (tetration x n + 1) := by
      have h₁₄₃ : 0 < (x : ℝ) := by linarith
      have h₁₄₄ : (x : ℝ) * (x : ℝ) ^ (tetration x n : ℝ) = (x : ℝ) ^ ((tetration x n : ℝ) + 1) := by
        have h₁₄₅ : (x : ℝ) * (x : ℝ) ^ (tetration x n : ℝ) = (x : ℝ) ^ (1 : ℝ) * (x : ℝ) ^ (tetration x n : ℝ) := by
          norm_num [Real.rpow_one]
        rw [h₁₄₅]
        have h₁₄₆ : (x : ℝ) ^ (1 : ℝ) * (x : ℝ) ^ (tetration x n : ℝ) = (x : ℝ) ^ ((1 : ℝ) + (tetration x n : ℝ)) := by
          rw [← Real.rpow_add (by positivity)]
        rw [h₁₄₆]
        ; ring_nf
      exact h₁₄₄
    rw [h₁₄₂]
  have h₁₅ : (Real.log x / Real.log 2) * (tetration x (n + 1) + 1) < x ^ (tetration x n + 1) := by
    calc
      (Real.log x / Real.log 2) * (tetration x (n + 1) + 1) < (Real.log x / Real.log 2) * tetration x (n + 1) * (9 / 8 : ℝ) := h₁₁
      _ = (9 / 8 : ℝ) * (Real.log x / Real.log 2) * tetration x (n + 1) := by rw [h₁₂]
      _ < x * tetration x (n + 1) := h₁₃
      _ = x ^ (tetration x n + 1) := by rw [h₁₄]
  have h₁₆ : x ^ (tetration x n + 1) = (2 : ℝ) ^ ((Real.log x / Real.log 2) * (tetration x n + 1)) := by
    have h₁₆₁ : 0 < (x : ℝ) := by linarith
    have h₁₆₂ : 0 < (2 : ℝ) := by norm_num
    have h₁₆₃ : Real.log (x ^ (tetration x n + 1)) = (tetration x n + 1) * Real.log x := by
      rw [Real.log_rpow (by positivity)]
    have h₁₆₄ : Real.log ((2 : ℝ) ^ ((Real.log x / Real.log 2) * (tetration x n + 1))) = ((Real.log x / Real.log 2) * (tetration x n + 1)) * Real.log 2 := by
      rw [Real.log_rpow (by positivity)]
    have h₁₆₅ : Real.log (x ^ (tetration x n + 1)) = Real.log ((2 : ℝ) ^ ((Real.log x / Real.log 2) * (tetration x n + 1))) := by
      calc
        Real.log (x ^ (tetration x n + 1)) = (tetration x n + 1) * Real.log x := by rw [h₁₆₃]
        _ = (Real.log x / Real.log 2) * (tetration x n + 1) * Real.log 2 := by
          have h₁₆₆ : Real.log 2 > 0 := Real.log_pos (by norm_num)
          field_simp [h₁₆₆.ne']
        _ = ((Real.log x / Real.log 2) * (tetration x n + 1)) * Real.log 2 := by rfl
        _ = Real.log ((2 : ℝ) ^ ((Real.log x / Real.log 2) * (tetration x n + 1))) := by
          rw [h₁₆₄]
    have h₁₆₆ : x ^ (tetration x n + 1) > 0 := by positivity
    have h₁₆₇ : (2 : ℝ) ^ ((Real.log x / Real.log 2) * (tetration x n + 1)) > 0 := by positivity
    have h₁₆₈ : x ^ (tetration x n + 1) = (2 : ℝ) ^ ((Real.log x / Real.log 2) * (tetration x n + 1)) := by
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr h₁₆₆) (Set.mem_Ioi.mpr h₁₆₇)
      linarith
    exact h₁₆₈
  have h₁₇ : (Real.log x / Real.log 2) * (tetration x (n + 1) + 1) < (2 : ℝ) ^ ((Real.log x / Real.log 2) * (tetration x n + 1)) := by
    calc
      (Real.log x / Real.log 2) * (tetration x (n + 1) + 1) < x ^ (tetration x n + 1) := h₁₅
      _ = (2 : ℝ) ^ ((Real.log x / Real.log 2) * (tetration x n + 1)) := by rw [h₁₆]
  have h₁₈ : (2 : ℝ) ^ ((Real.log x / Real.log 2) * (tetration x n + 1)) < (2 : ℝ) ^ (iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3))) := by
    have h₁₈₁ : (Real.log x / Real.log 2) * (tetration x n + 1) < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := hIH
    have h₁₈₂ : (2 : ℝ) ^ ((Real.log x / Real.log 2) * (tetration x n + 1)) < (2 : ℝ) ^ (iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3))) := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h₁₈₁
    exact h₁₈₂
  have h₁₉ : (2 : ℝ) ^ (iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3))) = iter_exp_two (n + 1 - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
    have h₁₉₁ : n ≥ 2 := hn
    have h₁₉₂ : n + 1 - 1 = n := by
      have h₁₉₃ : n ≥ 2 := hn
      omega
    have h₁₉₃ : iter_exp_two (n + 1 - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) = iter_exp_two n (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
      rw [h₁₉₂]
    have h₁₉₄ : iter_exp_two n (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) = (2 : ℝ) ^ (iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3))) := by
      have h₁₉₅ : n ≥ 1 := by linarith
      have h₁₉₆ : iter_exp_two n (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) = (2 : ℝ) ^ (iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3))) := by
        cases n with
        | zero => contradiction
        | succ n =>
          cases n with
          | zero => contradiction
          | succ n =>
            simp_all [iter_exp_two]
      exact h₁₉₆
    rw [h₁₉₃, h₁₉₄]
  have h₂₀ : (Real.log x / Real.log 2) * (tetration x (n + 1) + 1) < iter_exp_two (n + 1 - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
    calc
      (Real.log x / Real.log 2) * (tetration x (n + 1) + 1) < (2 : ℝ) ^ ((Real.log x / Real.log 2) * (tetration x n + 1)) := h₁₇
      _ < (2 : ℝ) ^ (iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3))) := h₁₈
      _ = iter_exp_two (n + 1 - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by rw [h₁₉]
  exact h₂₀

-- Case 4: x > 2 and n ≥ 2 (the main case)
lemma case_x_gt_two_n_ge_two {x : ℝ} {n : ℕ} (hx : 2 < x) (hnge : 2 ≤ n) :
    tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
  have h₁ : n ≥ 2 := by linarith
  have h₂ : ∀ (k : ℕ), 2 ≤ k → (Real.log x / Real.log 2) * (tetration x k + 1) < iter_exp_two (k - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
    intro k hk
    induction' hk with k hk IH
    · -- Base case: k = 2
      by_cases h : x < 16
      · -- Case: x < 16
        have h₃ : (Real.log x / Real.log 2) * (tetration x 2 + 1) < iter_exp_two (2 - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
          apply case_x_gt_two_base_x_lt_16
          · linarith
          · linarith
        simpa using h₃
      · -- Case: x ≥ 16
        have h₃ : (Real.log x / Real.log 2) * (tetration x 2 + 1) < iter_exp_two (2 - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
          apply case_x_gt_two_base_x_ge_16
          · linarith
          · linarith
        simpa using h₃
    · -- Inductive step: assume P(k), prove P(k+1)
      have h₃ : (Real.log x / Real.log 2) * (tetration x (k + 1) + 1) < iter_exp_two (k + 1 - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
        apply case_x_gt_two_inductive_step hx (by exact_mod_cast hk) IH
      simpa [Nat.succ_eq_add_one] using h₃
  have h₃ : (Real.log x / Real.log 2) * (tetration x n + 1) < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
    exact h₂ n h₁



  have h₄ : tetration x n < (Real.log x / Real.log 2) * (tetration x n + 1) := by
    have h₄₁ : 0 < tetration x n := by
      have h : ∀ n : ℕ, 0 < tetration x n := by
        intro n
        induction n with
        | zero =>
          -- Base case: tetration x 0 = 1 > 0
          norm_num [tetration]
        | succ n ih =>
          -- Inductive step: tetration x (n+1) = x ^ tetration x n > 0
          rw [tetration]
          apply Real.rpow_pos_of_pos
          linarith
      -- Since n ≥ 2 (from hnge), we certainly have tetration x n > 0
      exact h n
    have h₄₂ : 1 < Real.log x / Real.log 2 := by
      have h₄₂₁ : Real.log x > Real.log 2 := Real.log_lt_log (by linarith) (by linarith)
      have h₄₂₂ : Real.log 2 > 0 := Real.log_pos (by norm_num)
      have h₄₂₃ : Real.log x / Real.log 2 > 1 := by
        have h₄₂₄ : 0 < Real.log 2 := by positivity
        have h₄₂₅ : Real.log x > Real.log 2 := h₄₂₁
        have h₄₂₆ : Real.log x / Real.log 2 > Real.log 2 / Real.log 2 := by
          gcongr
        have h₄₂₇ : Real.log 2 / Real.log 2 = 1 := by
          field_simp [h₄₂₄.ne']
        linarith
      linarith
    have h₄₃ : 0 < Real.log x / Real.log 2 := by linarith
    have h₄₄ : 0 < (Real.log x / Real.log 2 - 1) * tetration x n + Real.log x / Real.log 2 := by
      have h₄₄₁ : 0 < Real.log x / Real.log 2 - 1 := by linarith
      have h₄₄₂ : 0 < tetration x n := h₄₁
      have h₄₄₃ : 0 < (Real.log x / Real.log 2 - 1) * tetration x n := by positivity
      have h₄₄₄ : 0 < Real.log x / Real.log 2 := by linarith
      linarith
    -- Use nlinarith to verify the main inequality
    have h₄₅ : tetration x n < (Real.log x / Real.log 2) * (tetration x n + 1) := by
      nlinarith [h₄₁, h₄₂, h₄₃]
    exact h₄₅

  exact lt_trans h₄ h₃

-- Main theorem: For any positive real x and positive integer n, if x > 1 or n > 1, then x↑↑n < (2↑)^{n-1} x^{2/3}
theorem pucs_1_2_conjecture {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 0 < n) (h : x > 1 ∨ n > 1) :
    tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) := by
  have h₁ : n ≥ 1 := by linarith
  have h₂ : n = 1 ∨ n ≥ 2 := by
    by_cases hn1 : n = 1
    · exact Or.inl hn1
    · have hn2 : n ≥ 2 := by
        have hn2₁ : n ≥ 1 := by linarith
        have hn2₂ : n ≠ 1 := by
          intro h
          have hn2₃ : n = 1 := h
          exact hn1 hn2₃
        have hn2₃ : n ≥ 2 := by
          by_contra h
          have hn2₄ : n ≤ 1 := by linarith
          have hn2₅ : n ≥ 1 := by linarith
          have hn2₆ : n = 1 := by linarith
          exact hn2₂ hn2₆
        exact hn2₃
      exact Or.inr hn2

  cases h with
  | inl hxgt1 =>
    -- Case: x > 1
    have h₃ : x > 1 := hxgt1
    cases h₂ with
    | inl hn_eq1 =>
      -- Subcase: n = 1
      have h₄ : n = 1 := hn_eq1
      have h₅ : 0 ≤ x := by linarith
      have h₆ : 1 < x := h₃
      have h₇ : tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) :=
        case_n_eq_one h₄ h₆
      exact h₇
    | inr hn_ge2 =>
      -- Subcase: n ≥ 2
      have h₄ : n ≥ 2 := hn_ge2
      -- Now consider x ≤ 2 or x > 2
      have h₅ : x ≤ 2 ∨ x > 2 := by
        by_cases hx_le2 : x ≤ 2
        · exact Or.inl hx_le2
        · exact Or.inr (by linarith)
      cases h₅ with
      | inl hx_le2 =>
        -- Subsubcase: 1 < x ≤ 2
        have h₆ : 1 < x := h₃
        have h₇ : x ≤ 2 := hx_le2
        have h₈ : 1 ≤ n := by linarith
        have h₉ : tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) :=
          case_one_lt_x_le_two h₆ h₇ h₈
        exact h₉
      | inr hx_gt2 =>
        -- Subsubcase: x > 2
        have h₆ : x > 2 := hx_gt2
        have h₇ : 2 ≤ n := by linarith
        have h₈ : tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) :=
          case_x_gt_two_n_ge_two h₆ h₇
        exact h₈

  | inr hn_gt1 =>
    -- Case: n > 1
    have h₃ : n > 1 := hn_gt1
    -- Now consider x ≤ 1 or x > 1
    have h₅ : x ≤ 1 ∨ x > 1 := by
      by_cases hx_le1 : x ≤ 1
      · exact Or.inl hx_le1
      · exact Or.inr (by linarith)
    cases h₅ with
    | inl hx_le1 =>
      -- Subcase: 0 < x ≤ 1
      have h₆ : 0 < x := hx
      have h₇ : x ≤ 1 := hx_le1
      have h₈ : 1 ≤ n := by linarith
      have h₉ : 1 < n := by linarith
      have h₁₀ : tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) :=
        case_x_le_one h₆ h₇ h₉
      exact h₁₀
    | inr hx_gt1 =>
      -- Subcase: x > 1 (and n > 1)
      have h₆ : x > 1 := hx_gt1
      -- Now consider x ≤ 2 or x > 2
      have h₈ : x ≤ 2 ∨ x > 2 := by
        by_cases hx_le2 : x ≤ 2
        · exact Or.inl hx_le2
        · exact Or.inr (by linarith)
      cases h₈ with
      | inl hx_le2 =>
        -- Subsubcase: 1 < x ≤ 2
        have h₉ : 1 < x := h₆
        have h₁₀ : x ≤ 2 := hx_le2
        have h₁₁ : 1 ≤ n := by linarith
        have h₁₂ : tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) :=
          case_one_lt_x_le_two h₉ h₁₀ h₁₁
        exact h₁₂
      | inr hx_gt2 =>
        -- Subsubcase: x > 2
        have h₉ : x > 2 := hx_gt2
        have h₁₀ : 2 ≤ n := by linarith
        have h₁₁ : tetration x n < iter_exp_two (n - 1) (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3)) :=
          case_x_gt_two_n_ge_two h₉ h₁₀
        exact h₁₁