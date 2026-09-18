-- Template: Taylor Polynomial Bounds for Rational Verification
-- This file shows the key lemmas and worked examples for verifying
-- transcendental function bounds using Taylor series in Lean.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open Real
open Finset

-- ============================================================
-- KEY LEMMAS (prove once, use for all 150+ intervals)
-- ============================================================

-- 1. Taylor lower bound for exp(x) when x > 0
-- exp(x) = 1 + x + x²/2! + x³/3! + ...
-- For x > 0, all terms are positive, so partial sums are lower bounds
lemma exp_taylor_lower (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Real.exp x ≥ ∑ k in Finset.range (n + 1), x ^ k / (k.factorial : ℝ) := by
  have h₁ : ∑ k in Finset.range (n + 1), x ^ k / (k.factorial : ℝ) ≤ Real.exp x := by
    have h₂ : ∀ n : ℕ, ∑ k in Finset.range n, x ^ k / (k.factorial : ℝ) ≤ Real.exp x := by
      intro n
      have h₃ : ∑ k in Finset.range n, x ^ k / (k.factorial : ℝ) ≤ ∑' k : ℕ, x ^ k / (k.factorial : ℝ) := by
        exact Finset.sum_le_tsum (fun k _ => by positivity) (by
          -- The series is absolutely convergent
          have h₄ : Summable (fun k : ℕ => (x : ℝ) ^ k / (k.factorial : ℝ)) := by
            -- exp(x) is defined as this sum, so it's summable
            have h₅ : Summable (fun k : ℕ => (x : ℝ) ^ k / (k.factorial : ℝ)) := by
              simpa [Real.exp_eq_tsum_div_factorial] using Real.summable_pow_div_factorial x
            exact h₅
          exact h₄) (Finset.range_subset_univ n)
      have h₄ : ∑' k : ℕ, x ^ k / (k.factorial : ℝ) = Real.exp x := by
        rw [Real.exp_eq_tsum_div_factorial]
      linarith
    have h₃ : ∑ k in Finset.range (n + 1), x ^ k / (k.factorial : ℝ) ≤ Real.exp x := h₂ (n + 1)
    exact h₃
  linarith

-- 2. Taylor upper bound for exp(x) using Lagrange remainder
-- exp(x) ≤ ∑_{k=0}^n x^k/k! + x^{n+1}/(n+1)! * exp(x) for x > 0
-- If we have an upper bound M ≥ exp(x), we get a concrete upper bound
lemma exp_taylor_upper (x : ℝ) (hx : 0 < x) (n : ℕ) (M : ℝ) (hM : Real.exp x ≤ M) :
    Real.exp x ≤ (∑ k in Finset.range (n + 1), x ^ k / (k.factorial : ℝ)) + x ^ (n + 1) / ((n + 1).factorial : ℝ) * M := by
  have h₁ : Real.exp x = ∑' k : ℕ, x ^ k / (k.factorial : ℝ) := by
    rw [Real.exp_eq_tsum_div_factorial]
  rw [h₁]
  have h₂ : ∑' k : ℕ, x ^ k / (k.factorial : ℝ) = ∑ k in Finset.range (n + 1), x ^ k / (k.factorial : ℝ) + ∑' k : ℕ, x ^ (k + n + 1) / ((k + n + 1).factorial : ℝ) := by
    have h₃ : ∑' k : ℕ, x ^ k / (k.factorial : ℝ) = ∑' k : ℕ, x ^ k / (k.factorial : ℝ) := rfl
    rw [h₃]
    have h₄ : ∑' k : ℕ, x ^ k / (k.factorial : ℝ) = ∑ k in Finset.range (n + 1), x ^ k / (k.factorial : ℝ) + ∑' k : ℕ, x ^ (k + n + 1) / ((k + n + 1).factorial : ℝ) := by
      have h₅ : Summable (fun k : ℕ => x ^ k / (k.factorial : ℝ)) := by
        simpa [Real.exp_eq_tsum_div_factorial] using Real.summable_pow_div_factorial x
      have h₆ : ∑' k : ℕ, x ^ k / (k.factorial : ℝ) = ∑ k in Finset.range (n + 1), x ^ k / (k.factorial : ℝ) + ∑' k : ℕ, x ^ (k + n + 1) / ((k + n + 1).factorial : ℝ) := by
        rw [← tsum_eq_sum_add_tsum_nat_add (h₅) (n + 1)]
        <;> simp [Finset.sum_range_succ, add_assoc]
        <;> congr 1 <;> ext k <;> ring_nf
        <;> simp [Nat.cast_add, Nat.cast_one, add_assoc]
        <;> field_simp [Nat.factorial_succ]
        <;> ring_nf
      exact h₆
    exact h₄
  rw [h₂]
  have h₃ : ∑' k : ℕ, x ^ (k + n + 1) / ((k + n + 1).factorial : ℝ) ≤ x ^ (n + 1) / ((n + 1).factorial : ℝ) * M := by
    have h₄ : ∑' k : ℕ, x ^ (k + n + 1) / ((k + n + 1).factorial : ℝ) ≤ ∑' k : ℕ, x ^ (k + n + 1) / ((k + n + 1).factorial : ℝ) := le_refl _
    have h₅ : ∑' k : ℕ, x ^ (k + n + 1) / ((k + n + 1).factorial : ℝ) = ∑' k : ℕ, (x ^ (n + 1) / ((n + 1).factorial : ℝ)) * (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) := by
      have h₅₁ : ∀ k : ℕ, (x : ℝ) ^ (k + n + 1) / ((k + n + 1).factorial : ℝ) = (x ^ (n + 1) / ((n + 1).factorial : ℝ)) * (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) := by
        intro k
        have h₅₂ : (x : ℝ) ^ (k + n + 1) = (x : ℝ) ^ (n + 1) * (x : ℝ) ^ k := by
          rw [← pow_add]
          <;> ring_nf
        rw [h₅₂]
        have h₅₃ : ((k + n + 1).factorial : ℝ) = ((n + 1).factorial : ℝ) * ∏ i in Finset.Icc (n + 2) (k + n + 1), (i : ℝ) := by
          have h₅₄ : ((k + n + 1).factorial : ℝ) = ∏ i in Finset.Icc 1 (k + n + 1), (i : ℝ) := by
            norm_cast
            <;> simp [Nat.factorial, Finset.prod_Icc_succ_top]
            <;> ring_nf
          rw [h₅₄]
          have h₅₅ : ∏ i in Finset.Icc 1 (k + n + 1), (i : ℝ) = (∏ i in Finset.Icc 1 (n + 1), (i : ℝ)) * ∏ i in Finset.Icc (n + 2) (k + n + 1), (i : ℝ) := by
            have h₅₆ : Finset.Icc 1 (k + n + 1) = Finset.Icc 1 (n + 1) ∪ Finset.Icc (n + 2) (k + n + 1) := by
              apply Finset.ext
              intro x
              simp [Finset.mem_Icc]
              <;>
              (try omega) <;>
              (try
                {
                  by_cases h : x ≤ n + 1 <;>
                  by_cases h' : x ≤ k + n + 1 <;>
                  simp_all [Nat.lt_succ_iff]
                  <;> omega
                })
            rw [h₅₆]
            rw [Finset.prod_union] <;>
            (try
              {
                simp [Finset.disjoint_left, Finset.mem_Icc]
                <;> omega
              }) <;>
            (try
              {
                simp_all [Finset.prod_Icc_succ_top]
                <;> ring_nf
                <;> norm_num
                <;> omega
              })
          rw [h₅₅]
          have h₅₆ : (∏ i in Finset.Icc 1 (n + 1), (i : ℝ)) = ((n + 1).factorial : ℝ) := by
            norm_cast
            <;> simp [Nat.factorial, Finset.prod_Icc_succ_top]
            <;> ring_nf
          rw [h₅₆]
          <;> field_simp [Nat.cast_add_one_ne_zero]
          <;> ring_nf
        rw [h₅₃]
        have h₅₄ : 0 < ((n + 1).factorial : ℝ) := by positivity
        have h₅₅ : 0 < (x : ℝ) := by positivity
        field_simp [h₅₄.ne', h₅₅.ne']
        <;> ring_nf
        <;> field_simp [h₅₄.ne', h₅₅.ne']
        <;> ring_nf
      calc
        ∑' k : ℕ, (x : ℝ) ^ (k + n + 1) / ((k + n + 1).factorial : ℝ) = ∑' k : ℕ, (x ^ (n + 1) / ((n + 1).factorial : ℝ)) * (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) := by
          apply tsum_congr
          intro k
          rw [h₅₁ k]
        _ = ∑' k : ℕ, (x ^ (n + 1) / ((n + 1).factorial : ℝ)) * (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) := by rfl
    rw [h₅]
    have h₆ : ∑' k : ℕ, (x ^ (n + 1) / ((n + 1).factorial : ℝ)) * (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) ≤ x ^ (n + 1) / ((n + 1).factorial : ℝ) * M := by
      have h₇ : 0 < x := hx
      have h₈ : 0 < (x : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) := by positivity
      have h₉ : ∑' k : ℕ, (x ^ (n + 1) / ((n + 1).factorial : ℝ)) * (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) = (x ^ (n + 1) / ((n + 1).factorial : ℝ)) * ∑' k : ℕ, (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) := by
        have h₉₁ : Summable (fun k : ℕ => (x : ℝ) ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) := by
          -- The series is summable because it's bounded by the exp series
          have h₉₂ : ∀ k : ℕ, (x : ℝ) ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ) ≤ (x : ℝ) ^ k / (k.factorial : ℝ) := by
            intro k
            have h₉₃ : ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ) ≤ 1 := by
              have h₉₄ : ((n + 1).factorial : ℝ) ≤ ((k + n + 1).factorial : ℝ) := by
                exact_mod_cast Nat.factorial_le (by omega)
              have h₉₅ : 0 < ((k + n + 1).factorial : ℝ) := by positivity
              have h₉₆ : 0 < ((n + 1).factorial : ℝ) := by positivity
              rw [div_le_one (by positivity)]
              <;> nlinarith
            have h₉₇ : 0 ≤ (x : ℝ) ^ k / (k.factorial : ℝ) := by positivity
            nlinarith
          have h₉₃ : Summable (fun k : ℕ => (x : ℝ) ^ k / (k.factorial : ℝ)) := by
            simpa [Real.exp_eq_tsum_div_factorial] using Real.summable_pow_div_factorial x
          refine' Summable.of_nonneg_of_le (fun k => by positivity) h₉₃ _
          intro k
          exact h₉₂ k
        -- Use the fact that we can factor out the constant
        have h₉₂ : HasSum (fun k : ℕ => (x ^ (n + 1) / ((n + 1).factorial : ℝ)) * (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ))) ((x ^ (n + 1) / ((n + 1).factorial : ℝ)) * ∑' k : ℕ, (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ))) := by
          have h₉₃ : HasSum (fun k : ℕ => (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ))) (∑' k : ℕ, (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ))) := by
            exact h₉₁.hasSum
          have h₉₄ : HasSum (fun k : ℕ => (x ^ (n + 1) / ((n + 1).factorial : ℝ)) * (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ))) ((x ^ (n + 1) / ((n + 1).factorial : ℝ)) * ∑' k : ℕ, (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ))) := by
            convert HasSum.mul_left (x ^ (n + 1) / ((n + 1).factorial : ℝ)) h₉₃ using 1
            <;> simp [mul_assoc]
          exact h₉₄
        have h₉₃ : ∑' k : ℕ, (x ^ (n + 1) / ((n + 1).factorial : ℝ)) * (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) = (x ^ (n + 1) / ((n + 1).factorial : ℝ)) * ∑' k : ℕ, (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) := by
          rw [h₉₂.tsum_eq]
        rw [h₉₃]
      rw [h₉]
      have h₁₀ : ∑' k : ℕ, (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) ≤ M := by
        have h₁₀₁ : ∑' k : ℕ, (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) ≤ ∑' k : ℕ, (x : ℝ) ^ k / (k.factorial : ℝ) := by
          have h₁₀₂ : ∀ k : ℕ, (x : ℝ) ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ) ≤ (x : ℝ) ^ k / (k.factorial : ℝ) := by
            intro k
            have h₁₀₃ : ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ) ≤ 1 := by
              have h₁₀₄ : ((n + 1).factorial : ℝ) ≤ ((k + n + 1).factorial : ℝ) := by
                exact_mod_cast Nat.factorial_le (by omega)
              have h₁₀₅ : 0 < ((k + n + 1).factorial : ℝ) := by positivity
              have h₁₀₆ : 0 < ((n + 1).factorial : ℝ) := by positivity
              rw [div_le_one (by positivity)]
              <;> nlinarith
            have h₁₀₇ : 0 ≤ (x : ℝ) ^ k / (k.factorial : ℝ) := by positivity
            nlinarith
          have h₁₀₃ : Summable (fun k : ℕ => (x : ℝ) ^ k / (k.factorial : ℝ)) := by
            simpa [Real.exp_eq_tsum_div_factorial] using Real.summable_pow_div_factorial x
          have h₁₀₄ : Summable (fun k : ℕ => (x : ℝ) ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) := by
            refine' Summable.of_nonneg_of_le (fun k => by positivity) h₁₀₃ _
            intro k
            exact h₁₀₂ k
          exact tsum_le_tsum h₁₀₂ h₁₀₄ h₁₀₃
        have h₁₀₂ : ∑' k : ℕ, (x : ℝ) ^ k / (k.factorial : ℝ) = Real.exp x := by
          rw [Real.exp_eq_tsum_div_factorial]
        have h₁₀₃ : Real.exp x ≤ M := hM
        calc
          ∑' k : ℕ, (x ^ k / (k.factorial : ℝ) * ((n + 1).factorial : ℝ) / ((k + n + 1).factorial : ℝ)) ≤ ∑' k : ℕ, (x : ℝ) ^ k / (k.factorial : ℝ) := h₁₀₁
          _ = Real.exp x := by rw [h₁₀₂]
          _ ≤ M := h₁₀₃
      have h₁₁ : 0 ≤ x ^ (n + 1) / ((n + 1).factorial : ℝ) := by positivity
      have h₁₂ : 0 ≤ M := by
        have h₁₃ : Real.exp x ≤ M := hM
        have h₁₄ : 0 < Real.exp x := Real.exp_pos x
        linarith
      nlinarith
    linarith
  linarith

-- 3. Alternating series bounds for log(1+x) when 0 < x ≤ 1
-- Using the Mathlib series: log(1+x) = ∑ 2/(2k+1) * (x/(x+2))^(2k+1)
-- All terms are positive, so partial sums are lower bounds.
-- For upper bounds, we use the remainder estimate from log_div_le_sum_range_add.
lemma log_one_add_taylor_bounds (x : ℝ) (hx : 0 < x) (hx' : x ≤ 1) (n : ℕ) :
    (∑ k in Finset.range n, (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ)) ≤ Real.log (1 + x) ∧
    Real.log (1 + x) ≤ (∑ k in Finset.range n, (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ)) + (x / (x + 2)) ^ (2 * n + 1 : ℕ) / (1 - (x / (x + 2)) ^ 2) := by
  have h₁ : 0 ≤ (x : ℝ) := by linarith
  have h₂ : (x : ℝ) / (x + 2) < 1 := by
    have h₃ : 0 < (x : ℝ) + 2 := by linarith
    have h₄ : (x : ℝ) < (x : ℝ) + 2 := by linarith
    rw [div_lt_one (by positivity)]
    <;> nlinarith
  have h₃ : 0 ≤ (x : ℝ) / (x + 2) := by positivity
  -- Use the Mathlib series expansion for log(1+x)
  have h₄ : HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ)) (Real.log (1 + x)) := by
    have h₅ : HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ)) (Real.log (1 + x)) := by
      -- Use the lemma hasSum_log_one_add
      have h₆ : HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ)) (Real.log (1 + x)) := by
        have h₇ : HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ)) (Real.log (1 + x)) := by
          -- Use the Mathlib lemma
          have h₈ : HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ)) (Real.log (1 + x)) :=
            Real.hasSum_log_one_add (by linarith)
          exact h₈
        exact h₇
      exact h₆
    exact h₅
  -- Lower bound: partial sums are lower bounds since all terms are positive
  have h₅ : (∑ k in Finset.range n, (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ)) ≤ Real.log (1 + x) := by
    have h₅₁ : ∀ k : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ) := by
      intro k
      have h₅₂ : 0 ≤ (x : ℝ) / (x + 2) := by positivity
      have h₅₃ : 0 ≤ (x : ℝ) / (x + 2) ^ (2 * k + 1 : ℕ) := by positivity
      have h₅₄ : 0 ≤ (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) := by positivity
      positivity
    -- Use the fact that partial sums of a series with non-negative terms are bounded above by the sum
    have h₅₂ : Summable (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ)) := by
      exact h₄.summable
    have h₅₃ : ∑ k in Finset.range n, (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ) ≤ ∑' k : ℕ, (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ) := by
      exact Finset.sum_le_tsum h₅₁ h₅₂ (Finset.range_subset_univ n)
    have h₅₄ : ∑' k : ℕ, (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ) = Real.log (1 + x) := by
      exact h₄.tsum_eq
    linarith
  -- Upper bound: use the remainder estimate from log_div_le_sum_range_add
  have h₆ : Real.log (1 + x) ≤ (∑ k in Finset.range n, (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ)) + (x / (x + 2)) ^ (2 * n + 1 : ℕ) / (1 - (x / (x + 2)) ^ 2) := by
    have h₆₁ : 1 / 2 * Real.log ((1 + (x / (x + 2))) / (1 - (x / (x + 2)))) = Real.log (1 + x) := by
      have h₆₂ : (1 + (x / (x + 2)) : ℝ) / (1 - (x / (x + 2)) : ℝ) = (1 + x : ℝ) ^ 2 := by
        have h₆₃ : 0 < (x : ℝ) + 2 := by linarith
        field_simp [h₆₃.ne']
        <;> ring_nf
        <;> field_simp [h₆₃.ne']
        <;> ring_nf
        <;> nlinarith
      rw [h₆₂]
      have h₆₃ : 1 / 2 * Real.log ((1 + x : ℝ) ^ 2) = Real.log (1 + x) := by
        have h₆₄ : Real.log ((1 + x : ℝ) ^ 2) = 2 * Real.log (1 + x) := by
          rw [Real.log_pow] <;> norm_num
        rw [h₆₄]
        <;> ring_nf
        <;> field_simp
        <;> linarith
      rw [h₆₃]
    have h₆₂ : 1 / 2 * Real.log ((1 + (x / (x + 2))) / (1 - (x / (x + 2)))) ≤ (∑ k in Finset.range n, (x / (x + 2)) ^ (2 * k + 1 : ℕ) / (2 * k + 1 : ℝ)) + (x / (x + 2)) ^ (2 * n + 1 : ℕ) / (1 - (x / (x + 2)) ^ 2) := by
      have h₆₃ : 0 ≤ (x / (x + 2) : ℝ) := by positivity
      have h₆₄ : (x / (x + 2) : ℝ) < 1 := by
        have h₆₅ : 0 < (x : ℝ) + 2 := by linarith
        have h₆₆ : (x : ℝ) < (x : ℝ) + 2 := by linarith
        rw [div_lt_one (by positivity)]
        <;> nlinarith
      have h₆₅ : 1 / 2 * Real.log ((1 + (x / (x + 2))) / (1 - (x / (x + 2)))) ≤ (∑ k in Finset.range n, (x / (x + 2)) ^ (2 * k + 1 : ℕ) / (2 * k + 1 : ℝ)) + (x / (x + 2)) ^ (2 * n + 1 : ℕ) / (1 - (x / (x + 2)) ^ 2) := by
        -- Use the Mathlib lemma log_div_le_sum_range_add
        have h₆₆ := Real.log_div_le_sum_range_add (x / (x + 2)) (by positivity) h₆₄ n
        simpa [Finset.sum_range_succ, add_assoc] using h₆₆
      exact h₆₅
    have h₆₃ : (∑ k in Finset.range n, (x / (x + 2)) ^ (2 * k + 1 : ℕ) / (2 * k + 1 : ℝ)) = (∑ k in Finset.range n, (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro k _
      have h₆₄ : (x / (x + 2) : ℝ) ^ (2 * k + 1 : ℕ) / (2 * k + 1 : ℝ) = (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * (x / (x + 2)) ^ (2 * k + 1 : ℕ) := by
        field_simp [Nat.cast_add_one_ne_zero]
        <;> ring_nf
        <;> field_simp [Nat.cast_add_one_ne_zero]
        <;> ring_nf
      rw [h₆₄]
    rw [h₆₁] at h₆₂
    linarith
  exact ⟨h₅, h₆⟩

-- 4. log 2 bounds from Mathlib (already available)
-- Real.log_two_gt_d9 : (0.6931471803 : ℝ) < Real.log 2
-- Real.log_two_lt_d9 : Real.log 2 < (0.6931471808 : ℝ)

-- ============================================================
-- WORKED EXAMPLE 1: log(35/16) bounds
-- ============================================================

-- 35/16 = 2 * 35/32 = 2 * (1 + 3/32)
-- log(35/16) = log 2 + log(1 + 3/32)
-- 3/32 = 0.09375 < 1, so alternating series works

-- Lower bound using the Mathlib series for log(1+x):
-- log(35/16) = log 2 + log(1 + 3/32)
-- log(1 + 3/32) = ∑ 2/(2k+1) * (3/35)^(2k+1)
lemma log_35_16_lower : Real.log (35 / 16 : ℝ) > 771146353 / 10^9 := by
  have h₁ : Real.log (35 / 16 : ℝ) = Real.log 2 + Real.log (1 + (3 / 32 : ℝ)) := by
    have h₂ : (35 / 16 : ℝ) = 2 * (1 + (3 / 32 : ℝ)) := by norm_num
    rw [h₂]
    have h₃ : Real.log (2 * (1 + (3 / 32 : ℝ))) = Real.log 2 + Real.log (1 + (3 / 32 : ℝ)) := by
      rw [Real.log_mul (by norm_num) (by norm_num)]
    rw [h₃]
  rw [h₁]
  have h₂ : Real.log 2 > 6931471803 / 10^10 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    <;> linarith
  have h₃ : Real.log (1 + (3 / 32 : ℝ)) ≥ (∑ k in Finset.range 5, (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * ((3 / 32 : ℝ) / ((3 / 32 : ℝ) + 2)) ^ (2 * k + 1 : ℕ)) := by
    have h₄ := log_one_add_taylor_bounds (3 / 32 : ℝ) (by norm_num) (by norm_num) 5
    linarith
  have h₄ : (∑ k in Finset.range 5, (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * ((3 / 32 : ℝ) / ((3 / 32 : ℝ) + 2)) ^ (2 * k + 1 : ℕ)) ≥ 78000000 / 10^9 := by
    norm_num [Finset.sum_range_succ, pow_succ]
  have h₅ : Real.log (1 + (3 / 32 : ℝ)) ≥ 78000000 / 10^9 := by linarith
  norm_num at h₂ h₅ ⊢
  <;> linarith

-- Upper bound using the Mathlib series for log(1+x):
lemma log_35_16_upper : Real.log (35 / 16 : ℝ) < 771146354 / 10^9 := by
  have h₁ : Real.log (35 / 16 : ℝ) = Real.log 2 + Real.log (1 + (3 / 32 : ℝ)) := by
    have h₂ : (35 / 16 : ℝ) = 2 * (1 + (3 / 32 : ℝ)) := by norm_num
    rw [h₂]
    have h₃ : Real.log (2 * (1 + (3 / 32 : ℝ))) = Real.log 2 + Real.log (1 + (3 / 32 : ℝ)) := by
      rw [Real.log_mul (by norm_num) (by norm_num)]
    rw [h₃]
  rw [h₁]
  have h₂ : Real.log 2 < 6931471808 / 10^10 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    <;> linarith
  have h₃ : Real.log (1 + (3 / 32 : ℝ)) ≤ (∑ k in Finset.range 5, (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * ((3 / 32 : ℝ) / ((3 / 32 : ℝ) + 2)) ^ (2 * k + 1 : ℕ)) + ((3 / 32 : ℝ) / ((3 / 32 : ℝ) + 2)) ^ (2 * 5 + 1 : ℕ) / (1 - ((3 / 32 : ℝ) / ((3 / 32 : ℝ) + 2)) ^ 2) := by
    have h₄ := log_one_add_taylor_bounds (3 / 32 : ℝ) (by norm_num) (by norm_num) 5
    linarith
  have h₄ : (∑ k in Finset.range 5, (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * ((3 / 32 : ℝ) / ((3 / 32 : ℝ) + 2)) ^ (2 * k + 1 : ℕ)) + ((3 / 32 : ℝ) / ((3 / 32 : ℝ) + 2)) ^ (2 * 5 + 1 : ℕ) / (1 - ((3 / 32 : ℝ) / ((3 / 32 : ℝ) + 2)) ^ 2) ≤ 78000001 / 10^9 := by
    norm_num [Finset.sum_range_succ, pow_succ]
  have h₅ : Real.log (1 + (3 / 32 : ℝ)) ≤ 78000001 / 10^9 := by linarith
  norm_num at h₂ h₅ ⊢
  <;> linarith

-- ============================================================
-- WORKED EXAMPLE 2: 2^(2/3) bounds
-- ============================================================

-- 2^(2/3) = exp((2/3) * log 2)
-- We have: 0.6931471803 < log 2 < 0.6931471808
-- So: 0.4620981202 < (2/3) * log 2 < 0.462098120533...

-- Lower bound: exp(0.4620981202) ≥ Taylor polynomial at n=10
lemma pow23_lower : (2 : ℝ) ^ (2 / 3 : ℝ) > 15874010519 / 10^10 := by
  have h₁ : (2 : ℝ) ^ (2 / 3 : ℝ) = Real.exp ((2 / 3 : ℝ) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
    <;> ring_nf
    <;> norm_num
  rw [h₁]
  have h₂ : Real.log 2 > 6931471803 / 10^10 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    <;> linarith
  have h₃ : (2 / 3 : ℝ) * Real.log 2 > (2 / 3 : ℝ) * (6931471803 / 10^10 : ℝ) := by gcongr
  have h₄ : (2 / 3 : ℝ) * (6931471803 / 10^10 : ℝ) = 4620981202 / 10^10 := by norm_num
  have h₅ : (2 / 3 : ℝ) * Real.log 2 > 4620981202 / 10^10 := by linarith
  have h₆ : Real.exp ((2 / 3 : ℝ) * Real.log 2) > Real.exp (4620981202 / 10^10 : ℝ) := Real.exp_lt_exp.mpr h₅
  have h₇ : Real.exp (4620981202 / 10^10 : ℝ) ≥ ∑ k in Finset.range 11, ((4620981202 / 10^10 : ℝ) : ℝ) ^ k / (k.factorial : ℝ) := by
    have h₇₁ : Real.exp (4620981202 / 10^10 : ℝ) ≥ ∑ k in Finset.range 11, ((4620981202 / 10^10 : ℝ) : ℝ) ^ k / (k.factorial : ℝ) := by
      apply exp_taylor_lower
      <;> norm_num
    exact h₇₁
  have h₈ : (∑ k in Finset.range 11, ((4620981202 / 10^10 : ℝ) : ℝ) ^ k / (k.factorial : ℝ)) ≥ 15874010519 / 10^10 := by
    norm_num [Finset.sum_range_succ, pow_succ, Nat.factorial_succ]
    <;>
    (try norm_num) <;>
    (try linarith)
  have h₉ : Real.exp (4620981202 / 10^10 : ℝ) ≥ 15874010519 / 10^10 := by linarith
  have h₁₀ : Real.exp ((2 / 3 : ℝ) * Real.log 2) > 15874010519 / 10^10 := by linarith
  linarith

-- Upper bound: exp(0.462098120533...) ≤ Taylor polynomial + remainder at n=10
lemma pow23_upper : (2 : ℝ) ^ (2 / 3 : ℝ) < 1587401052 / 10^9 := by
  have h₁ : (2 : ℝ) ^ (2 / 3 : ℝ) = Real.exp ((2 / 3 : ℝ) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
    <;> ring_nf
    <;> norm_num
  rw [h₁]
  have h₂ : Real.log 2 < 6931471808 / 10^10 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    <;> linarith
  have h₃ : (2 / 3 : ℝ) * Real.log 2 < (2 / 3 : ℝ) * (6931471808 / 10^10 : ℝ) := by gcongr
  have h₄ : (2 / 3 : ℝ) * (6931471808 / 10^10 : ℝ) = 4620981205 / 10^10 + 1/30000000000 := by norm_num
  have h₅ : (2 / 3 : ℝ) * Real.log 2 < 4620981206 / 10^10 := by
    norm_num at h₃ h₄ ⊢
    <;> linarith
  have h₆ : Real.exp ((2 / 3 : ℝ) * Real.log 2) < Real.exp (4620981206 / 10^10 : ℝ) := Real.exp_lt_exp.mpr h₅
  have h₇ : Real.exp (4620981206 / 10^10 : ℝ) ≤ (∑ k in Finset.range 11, ((4620981206 / 10^10 : ℝ) : ℝ) ^ k / (k.factorial : ℝ)) + ((4620981206 / 10^10 : ℝ) : ℝ) ^ 11 / (11.factorial : ℝ) * Real.exp (4620981206 / 10^10 : ℝ) := by
    have h₇₁ : Real.exp (4620981206 / 10^10 : ℝ) ≤ (∑ k in Finset.range 11, ((4620981206 / 10^10 : ℝ) : ℝ) ^ k / (k.factorial : ℝ)) + ((4620981206 / 10^10 : ℝ) : ℝ) ^ 11 / (11.factorial : ℝ) * Real.exp (4620981206 / 10^10 : ℝ) := by
      apply exp_taylor_upper
      <;> norm_num
      <;>
      (try linarith [Real.exp_pos (4620981206 / 10^10 : ℝ)])
      <;>
      (try
        {
          have := Real.exp_one_gt_d9
          have := Real.exp_one_lt_d9
          norm_num at *
          <;> linarith [Real.exp_pos (4620981206 / 10^10 : ℝ)]
        })
    exact h₇₁
  have h₈ : (∑ k in Finset.range 11, ((4620981206 / 10^10 : ℝ) : ℝ) ^ k / (k.factorial : ℝ)) + ((4620981206 / 10^10 : ℝ) : ℝ) ^ 11 / (11.factorial : ℝ) * Real.exp (4620981206 / 10^10 : ℝ) < 1587401052 / 10^9 := by
    have h₈₁ : Real.exp (4620981206 / 10^10 : ℝ) < 2 := by
      have h₈₂ : Real.exp (4620981206 / 10^10 : ℝ) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
      have h₈₃ : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        norm_num at this ⊢
        <;> linarith
      linarith
    have h₈₂ : (∑ k in Finset.range 11, ((4620981206 / 10^10 : ℝ) : ℝ) ^ k / (k.factorial : ℝ)) + ((4620981206 / 10^10 : ℝ) : ℝ) ^ 11 / (11.factorial : ℝ) * Real.exp (4620981206 / 10^10 : ℝ) < 1587401052 / 10^9 := by
      have h₈₃ : 0 < Real.exp (4620981206 / 10^10 : ℝ) := Real.exp_pos _
      have h₈₄ : ((4620981206 / 10^10 : ℝ) : ℝ) ^ 11 / (11.factorial : ℝ) * Real.exp (4620981206 / 10^10 : ℝ) ≤ ((4620981206 / 10^10 : ℝ) : ℝ) ^ 11 / (11.factorial : ℝ) * 2 := by
        gcongr
        <;> linarith
      have h₈₅ : (∑ k in Finset.range 11, ((4620981206 / 10^10 : ℝ) : ℝ) ^ k / (k.factorial : ℝ)) + ((4620981206 / 10^10 : ℝ) : ℝ) ^ 11 / (11.factorial : ℝ) * 2 < 1587401052 / 10^9 := by
        norm_num [Finset.sum_range_succ, pow_succ, Nat.factorial_succ]
        <;>
        (try norm_num) <;>
        (try linarith)
      linarith
    exact h₈₂
  have h₉ : Real.exp (4620981206 / 10^10 : ℝ) < 1587401052 / 10^9 := by linarith
  linarith

-- ============================================================
-- WORKED EXAMPLE 3: (35/16)^(35/16) bounds
-- ============================================================

-- (35/16)^(35/16) = exp((35/16) * log(35/16))
-- We have bounds on log(35/16), multiply by 35/16, then use exp bounds

lemma pow_35_16_lower : ((35 / 16 : ℝ) : ℝ) ^ ((35 / 16 : ℝ) : ℝ) > 4994755849 / 10^9 := by
  have h₁ : ((35 / 16 : ℝ) : ℝ) ^ ((35 / 16 : ℝ) : ℝ) = Real.exp ((35 / 16 : ℝ) * Real.log (35 / 16 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < (35 / 16 : ℝ))]
    <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
    <;> ring_nf
    <;> norm_num
  rw [h₁]
  have h₂ : Real.log (35 / 16 : ℝ) > 771146353 / 10^9 := by
    exact log_35_16_lower
  have h₃ : (35 / 16 : ℝ) * Real.log (35 / 16 : ℝ) > (35 / 16 : ℝ) * (771146353 / 10^9 : ℝ) := by gcongr
  have h₄ : (35 / 16 : ℝ) * (771146353 / 10^9 : ℝ) = 1687122371 / 10^9 + 1175 / 10^9 := by norm_num
  have h₅ : (35 / 16 : ℝ) * Real.log (35 / 16 : ℝ) > 1687122371 / 10^9 := by
    norm_num at h₃ h₄ ⊢
    <;> linarith
  have h₆ : Real.exp ((35 / 16 : ℝ) * Real.log (35 / 16 : ℝ)) > Real.exp (1687122371 / 10^9 : ℝ) := Real.exp_lt_exp.mpr h₅
  have h₇ : Real.exp (1687122371 / 10^9 : ℝ) ≥ ∑ k in Finset.range 13, ((1687122371 / 10^9 : ℝ) : ℝ) ^ k / (k.factorial : ℝ) := by
    have h₇₁ : Real.exp (1687122371 / 10^9 : ℝ) ≥ ∑ k in Finset.range 13, ((1687122371 / 10^9 : ℝ) : ℝ) ^ k / (k.factorial : ℝ) := by
      apply exp_taylor_lower
      <;> norm_num
    exact h₇₁
  have h₈ : (∑ k in Finset.range 13, ((1687122371 / 10^9 : ℝ) : ℝ) ^ k / (k.factorial : ℝ)) ≥ 4994755849 / 10^9 := by
    norm_num [Finset.sum_range_succ, pow_succ, Nat.factorial_succ]
    <;>
    (try norm_num) <;>
    (try linarith)
  have h₉ : Real.exp (1687122371 / 10^9 : ℝ) ≥ 4994755849 / 10^9 := by linarith
  have h₁₀ : Real.exp ((35 / 16 : ℝ) * Real.log (35 / 16 : ℝ)) > 4994755849 / 10^9 := by linarith
  linarith

-- Upper bound for (35/16)^(35/16)
lemma pow_35_16_upper : ((35 / 16 : ℝ) : ℝ) ^ ((35 / 16 : ℝ) : ℝ) < 499475585 / 10^8 := by
  have h₁ : ((35 / 16 : ℝ) : ℝ) ^ ((35 / 16 : ℝ) : ℝ) = Real.exp ((35 / 16 : ℝ) * Real.log (35 / 16 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < (35 / 16 : ℝ))]
    <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
    <;> ring_nf
    <;> norm_num
  rw [h₁]
  have h₂ : Real.log (35 / 16 : ℝ) < 771146354 / 10^9 := by
    exact log_35_16_upper
  have h₃ : (35 / 16 : ℝ) * Real.log (35 / 16 : ℝ) < (35 / 16 : ℝ) * (771146354 / 10^9 : ℝ) := by gcongr
  have h₄ : (35 / 16 : ℝ) * (771146354 / 10^9 : ℝ) = 1687122371 / 10^9 + 1175 / 10^9 + 35 / (16 * 10^9) := by norm_num
  have h₅ : (35 / 16 : ℝ) * Real.log (35 / 16 : ℝ) < 1687122372 / 10^9 := by
    norm_num at h₃ h₄ ⊢
    <;> linarith
  have h₆ : Real.exp ((35 / 16 : ℝ) * Real.log (35 / 16 : ℝ)) < Real.exp (1687122372 / 10^9 : ℝ) := Real.exp_lt_exp.mpr h₅
  have h₇ : Real.exp (1687122372 / 10^9 : ℝ) ≤ (∑ k in Finset.range 13, ((1687122372 / 10^9 : ℝ) : ℝ) ^ k / (k.factorial : ℝ)) + ((1687122372 / 10^9 : ℝ) : ℝ) ^ 13 / (13.factorial : ℝ) * Real.exp (1687122372 / 10^9 : ℝ) := by
    have h₇₁ : Real.exp (1687122372 / 10^9 : ℝ) ≤ (∑ k in Finset.range 13, ((1687122372 / 10^9 : ℝ) : ℝ) ^ k / (k.factorial : ℝ)) + ((1687122372 / 10^9 : ℝ) : ℝ) ^ 13 / (13.factorial : ℝ) * Real.exp (1687122372 / 10^9 : ℝ) := by
      apply exp_taylor_upper
      <;> norm_num
      <;>
      (try linarith [Real.exp_pos (1687122372 / 10^9 : ℝ)])
      <;>
      (try
        {
          have := Real.exp_one_gt_d9
          have := Real.exp_one_lt_d9
          norm_num at *
          <;> linarith [Real.exp_pos (1687122372 / 10^9 : ℝ)]
        })
    exact h₇₁
  have h₈ : (∑ k in Finset.range 13, ((1687122372 / 10^9 : ℝ) : ℝ) ^ k / (k.factorial : ℝ)) + ((1687122372 / 10^9 : ℝ) : ℝ) ^ 13 / (13.factorial : ℝ) * Real.exp (1687122372 / 10^9 : ℝ) < 499475585 / 10^8 := by
    have h₈₁ : Real.exp (1687122372 / 10^9 : ℝ) < 6 := by
      have h₈₂ : Real.exp (1687122372 / 10^9 : ℝ) < Real.exp 2 := Real.exp_lt_exp.mpr (by norm_num)
      have h₈₃ : Real.exp 2 < 8 := by
        have := Real.exp_one_lt_d9
        have h₈₄ : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add] <;> ring_nf <;> norm_num
        rw [h₈₄]
        have h₈₅ : Real.exp 1 < 3 := by
          have := Real.exp_one_lt_d9
          norm_num at this ⊢
          <;> linarith
        nlinarith
      linarith
    have h₈₂ : (∑ k in Finset.range 13, ((1687122372 / 10^9 : ℝ) : ℝ) ^ k / (k.factorial : ℝ)) + ((1687122372 / 10^9 : ℝ) : ℝ) ^ 13 / (13.factorial : ℝ) * Real.exp (1687122372 / 10^9 : ℝ) < 499475585 / 10^8 := by
      have h₈₃ : 0 < Real.exp (1687122372 / 10^9 : ℝ) := Real.exp_pos _
      have h₈₄ : ((1687122372 / 10^9 : ℝ) : ℝ) ^ 13 / (13.factorial : ℝ) * Real.exp (1687122372 / 10^9 : ℝ) ≤ ((1687122372 / 10^9 : ℝ) : ℝ) ^ 13 / (13.factorial : ℝ) * 6 := by
        gcongr
        <;> linarith
      have h₈₅ : (∑ k in Finset.range 13, ((1687122372 / 10^9 : ℝ) : ℝ) ^ k / (k.factorial : ℝ)) + ((1687122372 / 10^9 : ℝ) : ℝ) ^ 13 / (13.factorial : ℝ) * 6 < 499475585 / 10^8 := by
        norm_num [Finset.sum_range_succ, pow_succ, Nat.factorial_succ]
        <;>
        (try norm_num) <;>
        (try linarith)
      linarith
    exact h₈₂
  have h₉ : Real.exp (1687122372 / 10^9 : ℝ) < 499475585 / 10^8 := by linarith
  linarith

-- ============================================================
-- COMPOSITION PATTERN FOR x^y BOUNDS
-- ============================================================

-- General pattern for proving bounds on x^y = exp(y * log x):
-- 1. Get bounds on log x (using log_one_add_taylor_bounds or known bounds)
-- 2. Multiply by y to get bounds on y * log x
-- 3. Use exp_taylor_lower / exp_taylor_upper to get bounds on exp(y * log x)
-- 4. Use norm_num to compute polynomial sums and compare with target rationals

-- Example: To prove (a/b)^(c/d) > p/q
-- 1. log(a/b) = log a - log b (use bounds on each)
-- 2. (c/d) * log(a/b) = (c/d) * (log a - log b)
-- 3. exp((c/d) * log(a/b)) ≥ Taylor polynomial at appropriate n
-- 4. Compare polynomial value (computed by norm_num) with p/q

-- ============================================================
-- USAGE IN INTERVAL METHOD
-- ============================================================

-- For each subinterval [a, b] in the 150-interval partition:
-- 1. Compute f(b) = (log b / log 2) * (b^b + 1)
--    - Need bounds on log b (use log_one_add_taylor_bounds if b near rational)
--    - Need bounds on b^b = exp(b * log b) (use composition pattern)
-- 2. Compute g(a) = 2^(a^(2^(2/3)))
--    - Need bounds on 2^(2/3) (use exp_taylor with (2/3)*log 2)
--    - Need bounds on a^(2^(2/3)) = exp(2^(2/3) * log a)
--    - Need bounds on 2^(that) = exp(that * log 2)
-- 3. Prove f(b) < g(a) using norm_num with the rational bounds
-- 4. Use interval_union lemma to combine all 150 intervals

-- The key insight: All bounds reduce to rational arithmetic on Taylor polynomials,
-- which norm_num can verify completely automatically once the lemmas are in place.