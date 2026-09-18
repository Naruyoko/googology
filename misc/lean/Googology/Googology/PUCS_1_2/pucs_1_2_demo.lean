-- Demo: General Interval Verification Using Externally Computed Rational Bounds
-- This demonstrates the approach for the x < 16 case using ~150 subintervals

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Basic

open Real
open Finset

-- The functions from the main proof
noncomputable def f_base (x : ℝ) : ℝ :=
  (Real.log x / Real.log 2) * (x ^ x + 1)

noncomputable def g_base (x : ℝ) : ℝ :=
  (2 : ℝ) ^ (x ^ (2 : ℝ) ^ ((2 : ℝ) / 3))

-- ============================================================
-- MAIN INTERVAL VERIFICATION LEMMA
-- ============================================================

/-
This lemma takes ALL pre-computed rational bounds as parameters.
The bounds are computed externally (e.g., by Python/MPFR) and passed in.
Lean only verifies the rational arithmetic chain with norm_num.

Parameters:
  a, b : ℚ          -- interval endpoints (a ≤ b, a > 1)
  ha : (a : ℝ) ≤ (b : ℝ)
  ha_pos : (1 : ℝ) < (a : ℝ)

For each transcendental value, we provide:
  - Rational lower/upper bounds
  - The actual real value
  - Proofs that the bounds are valid (computed using Taylor lemmas)

Final hypothesis h_final is a pure rational arithmetic check:
  ((log_b_upper) / (log2_lower)) * (b_pow_b_upper + 1) < g_a_lower

This is verified entirely by norm_num at the meta-level.
-/
theorem verify_interval
  (a b : ℚ)
  (ha : (a : ℝ) ≤ (b : ℝ))
  (ha_pos : (1 : ℝ) < (a : ℝ))
  -- Bounds on log 2 (from Mathlib)
  (h_log2_lower : ℚ)
  (h_log2_upper : ℚ)
  (h_log2_lower_pos : (0 : ℝ) < (h_log2_lower : ℝ))
  (h_log2_lower_proof : (h_log2_lower : ℝ) < Real.log 2)
  (h_log2_upper_proof : Real.log 2 < (h_log2_upper : ℝ))
  -- Bounds on log a
  (h_log_a_lower : ℚ)
  (h_log_a_upper : ℚ)
  (h_log_a_lower_pos : (0 : ℝ) < (h_log_a_lower : ℝ))
  (h_log_a_lower_proof : (h_log_a_lower : ℝ) < Real.log (a : ℝ))
  (h_log_a_upper_proof : Real.log (a : ℝ) < (h_log_a_upper : ℝ))
  -- Bounds on log b
  (h_log_b_lower : ℚ)
  (h_log_b_upper : ℚ)
  (h_log_b_lower_pos : (0 : ℝ) < (h_log_b_lower : ℝ))
  (h_log_b_lower_proof : (h_log_b_lower : ℝ) < Real.log (b : ℝ))
  (h_log_b_upper_proof : Real.log (b : ℝ) < (h_log_b_upper : ℝ))
  -- Bounds on a^(2^(2/3))
  (h_a_pow_c_lower : ℚ)
  (h_a_pow_c_upper : ℚ)
  (h_a_pow_c_lower_pos : (0 : ℝ) < (h_a_pow_c_lower : ℝ))
  (h_a_pow_c_lower_proof : (h_a_pow_c_lower : ℝ) < (a : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)))
  (h_a_pow_c_upper_proof : (a : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3)) < (h_a_pow_c_upper : ℝ))
  -- Bounds on 2^(a^(2^(2/3))) = g(a)
  (h_g_a_lower : ℚ)
  (h_g_a_upper : ℚ)
  (h_g_a_lower_pos : (0 : ℝ) < (h_g_a_lower : ℝ))
  (h_g_a_lower_proof : (h_g_a_lower : ℝ) < (2 : ℝ) ^ ((a : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))))
  (h_g_a_upper_proof : (2 : ℝ) ^ ((a : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) < (h_g_a_upper : ℝ))
  -- Bounds on b^b
  (h_b_pow_b_lower : ℚ)
  (h_b_pow_b_upper : ℚ)
  (h_b_pow_b_lower_pos : (0 : ℝ) < (h_b_pow_b_lower : ℝ))
  (h_b_pow_b_lower_proof : (h_b_pow_b_lower : ℝ) < (b : ℝ) ^ (b : ℝ))
  (h_b_pow_b_upper_proof : (b : ℝ) ^ (b : ℝ) < (h_b_pow_b_upper : ℝ))
  -- Final check: f(b) < g(a) using the bounds
  (h_final : ((h_log_b_upper : ℝ) / (h_log2_lower : ℝ)) * ((h_b_pow_b_upper : ℝ) + 1) < (h_g_a_lower : ℝ)) :
  f_base (b : ℝ) < g_base (a : ℝ) := by
  have h₁ : f_base (b : ℝ) = (Real.log (b : ℝ) / Real.log 2) * ((b : ℝ) ^ (b : ℝ) + 1) := by
    simp [f_base]
    <;> ring_nf
  have h₂ : g_base (a : ℝ) = (2 : ℝ) ^ ((a : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
    simp [g_base]
    <;> ring_nf
  rw [h₁, h₂]
  have h₃ : (Real.log (b : ℝ) / Real.log 2) * ((b : ℝ) ^ (b : ℝ) + 1) < (h_g_a_lower : ℝ) := by
    have h₄ : Real.log (b : ℝ) < (h_log_b_upper : ℝ) := h_log_b_upper_proof
    have h₅ : (h_log2_lower : ℝ) < Real.log 2 := h_log2_lower_proof
    have h₆ : 0 < Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this ⊢
      <;> linarith
    have h₇ : 0 < (h_log2_lower : ℝ) := by
      by_contra h
      have h₈ : (h_log2_lower : ℝ) ≤ 0 := by linarith
      have h₉ : Real.log 2 ≤ 0 := by linarith [h_log2_lower_proof]
      have h₁₀ : Real.log 2 > 0 := by
        have := Real.log_two_gt_d9
        norm_num at this ⊢
        <;> linarith
      linarith
    have h₈ : 0 < Real.log (b : ℝ) := by
      have h₈₁ : (1 : ℝ) < (b : ℝ) := by
        have h₈₂ : (1 : ℝ) < (a : ℝ) := ha_pos
        have h₈₃ : (a : ℝ) ≤ (b : ℝ) := ha
        linarith
      exact Real.log_pos (by linarith)
    have h₉ : (b : ℝ) ^ (b : ℝ) < (h_b_pow_b_upper : ℝ) := h_b_pow_b_upper_proof
    have h₁₀ : 0 < (b : ℝ) ^ (b : ℝ) := by positivity
    have h₁₁ : 0 < (h_b_pow_b_upper : ℝ) := by linarith
    have h₁₂ : 0 < (h_log_b_upper : ℝ) := by
      have h₁₃ : (h_log_b_lower : ℝ) < Real.log (b : ℝ) := h_log_b_lower_proof
      have h₁₄ : 0 < Real.log (b : ℝ) := h₈
      -- Since log b > 0 and h_log_b_lower < log b, if h_log_b_lower ≤ 0 we get contradiction
      by_contra h
      have h₁₅ : (h_log_b_lower : ℝ) ≤ 0 := by linarith
      have h₁₆ : Real.log (b : ℝ) ≤ 0 := by linarith [h_log_b_lower_proof]
      linarith
    -- Use the bounds to prove the inequality
    have h₁₃ : (Real.log (b : ℝ) / Real.log 2) * ((b : ℝ) ^ (b : ℝ) + 1) < ((h_log_b_upper : ℝ) / (h_log2_lower : ℝ)) * ((h_b_pow_b_upper : ℝ) + 1) := by
      have h₁₄ : Real.log (b : ℝ) / Real.log 2 < (h_log_b_upper : ℝ) / (h_log2_lower : ℝ) := by
        -- Use the fact that a/b < c/d iff a*d < c*b for positive denominators
        have h₁₅ : 0 < Real.log 2 := by positivity
        have h₁₆ : 0 < (h_log2_lower : ℝ) := by positivity
        have h₁₇ : 0 < Real.log (b : ℝ) := by positivity
        have h₁₈ : 0 < (h_log_b_upper : ℝ) := by positivity
        -- Use div_lt_div_iff for real numbers with positive denominators
        rw [div_lt_div_iff (by positivity) (by positivity)]
        norm_cast at h₄ h₅ ⊢
        <;>
        (try norm_num at h₄ h₅ ⊢) <;>
        nlinarith
      have h₁₅ : (b : ℝ) ^ (b : ℝ) + 1 < (h_b_pow_b_upper : ℝ) + 1 := by linarith
      have h₁₆ : 0 < Real.log (b : ℝ) / Real.log 2 := by positivity
      have h₁₇ : 0 < (h_log_b_upper : ℝ) / (h_log2_lower : ℝ) := by positivity
      nlinarith
    have h₁₄ : ((h_log_b_upper : ℝ) / (h_log2_lower : ℝ)) * ((h_b_pow_b_upper : ℝ) + 1) < (h_g_a_lower : ℝ) := by
      exact_mod_cast h_final
    linarith
  have h₄ : (h_g_a_lower : ℝ) ≤ (2 : ℝ) ^ ((a : ℝ) ^ ((2 : ℝ) ^ ((2 : ℝ) / 3))) := by
    linarith [h_g_a_lower_proof]
  linarith

-- ============================================================
-- NOTES ON USAGE
-- ============================================================
/-
The workflow for the 150 intervals:

1. EXTERNAL COMPUTATION (Python/MPFR):
   For each interval [a_i, b_i]:
   - Compute high-precision values of:
     * log 2
     * log a_i
     * log b_i
     * a_i^(2^(2/3))
     * 2^(a_i^(2^(2/3))) = g(a_i)
     * b_i^b_i
   - Output rational lower/upper bounds for each

2. LEAN VERIFICATION:
   - For each interval, call `verify_interval` with the pre-computed rational bounds
   - The `h_final` hypothesis is a pure rational arithmetic check:
     ((log_b_upper) / (log2_lower)) * (b_pow_b_upper + 1) < g_a_lower
   - This is verified entirely by `norm_num` at the meta-level
   - Lean checks that the transcendental values actually lie within the bounds

3. COMBINING INTERVALS:
   - Use `interval_union` from the main proof to combine all 150 intervals
   - This gives the full [2, 16] case

The key insight: Lean only does rational arithmetic verification.
All transcendental reasoning is done externally and checked via bounds.
-/