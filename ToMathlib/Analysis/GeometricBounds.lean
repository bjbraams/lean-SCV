/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Real root limits and geometric bounds

Elementary limits and estimates for geometric majorants, independent of complex analysis.

## Main results

* `Real.tendsto_rpow_inv_natCast_succ`: Roots of a fixed positive constant tend to one.
* `Real.rpow_inv_succ_le_of_le_mul_pow`: A root of an exponential-type bound is bounded by a
  root of the constant times the reciprocal radius.
* `Real.le_geometric_of_bounds`: A sequence with a uniform exponential bound and an eventual
  geometric bound has a single geometric majorant.

## References

* `Mathlib.Analysis.SpecialFunctions.Pow.Real`: formal background used by this module.
* `Mathlib.Analysis.SpecificLimits.Basic`: formal background used by this module.
-/

public section

open Filter
open scoped Topology

namespace Real

/-- Roots of a fixed positive constant tend to one. -/
theorem tendsto_rpow_inv_natCast_succ {M : ℝ} (hM : 0 < M) :
    Tendsto (fun n : ℕ => M ^ ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => Real.log M * ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (Real.log M)).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, div_eq_mul_inv] using this
  simpa [Function.comp_def, Real.rpow_def_of_pos hM] using
    Real.tendsto_exp_nhds_zero_nhds_one.comp h

/-- A root of an exponential-type bound is bounded by a root of the constant times the reciprocal
radius. -/
theorem rpow_inv_succ_le_of_le_mul_pow {x M ρ : ℝ} (hx : 0 ≤ x) (hM : 0 ≤ M) (hρ : 0 < ρ)
    (n : ℕ) (h : x ≤ M * ρ⁻¹ ^ (n + 1)) :
    x ^ ((n + 1 : ℕ) : ℝ)⁻¹ ≤ M ^ ((n + 1 : ℕ) : ℝ)⁻¹ * ρ⁻¹ := by
  calc x ^ ((n + 1 : ℕ) : ℝ)⁻¹ ≤ (M * ρ⁻¹ ^ (n + 1)) ^ ((n + 1 : ℕ) : ℝ)⁻¹ :=
        Real.rpow_le_rpow hx h (by positivity)
    _ = M ^ ((n + 1 : ℕ) : ℝ)⁻¹ * ρ⁻¹ := by
        rw [Real.mul_rpow hM (by positivity),
          Real.pow_rpow_inv_natCast (inv_nonneg.mpr hρ.le) n.succ_ne_zero]

/-- A sequence with a uniform exponential bound and an eventual geometric bound has a single
geometric majorant. -/
theorem le_geometric_of_bounds {a : ℕ → ℝ} {M s q : ℝ} {N : ℕ} (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (h1 : ∀ k, a k ≤ M * s ^ k)
    (h2 : ∀ k, N + 1 ≤ k → a k ≤ q ^ k) (k : ℕ) :
    a k ≤ max 1 (M * max 1 s ^ N / q ^ N) * q ^ k := by
  have hqk : 0 ≤ q ^ k := pow_nonneg hq0.le k
  by_cases hk : N + 1 ≤ k
  · exact (h2 k hk).trans (le_mul_of_one_le_left hqk (le_max_left _ _))
  · have hkN : k ≤ N := by omega
    have hqN : q ^ N ≤ q ^ k := pow_le_pow_of_le_one hq0.le hq1 hkN
    have hC₀ : M * s ^ k ≤ M * max 1 s ^ N :=
      mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hs (le_max_right 1 s) k).trans
        (pow_le_pow_right₀ (le_max_left 1 s) hkN)) hM
    have hqN0 : 0 < q ^ N := pow_pos hq0 N
    calc a k ≤ M * max 1 s ^ N := (h1 k).trans hC₀
      _ = M * max 1 s ^ N / q ^ N * q ^ N := by field_simp
      _ ≤ M * max 1 s ^ N / q ^ N * q ^ k :=
          mul_le_mul_of_nonneg_left hqN (div_nonneg (by positivity) hqN0.le)
      _ ≤ max 1 (M * max 1 s ^ N / q ^ N) * q ^ k :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hqk

end Real
