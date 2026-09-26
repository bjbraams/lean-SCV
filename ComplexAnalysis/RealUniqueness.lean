/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Uniqueness of holomorphic functions from real parameters

Analytic functions with values in a complex normed space are determined on a preconnected domain
by agreement on a real neighborhood of a point in the domain. In particular, two entire
functions agreeing on the positive real axis are equal.

## Main results

* `AnalyticOnNhd.eqOn_of_eventuallyEq_ofReal`: Local one-variable uniqueness from agreement on a
  real germ. This is the form useful when the functions are only analytic on a connected
  continuation domain rather than entire.
* `AnalyticOnNhd.eq_of_eqOn_posReal`: Two entire functions of one complex variable which agree
  at every positive real number agree everywhere.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Local one-variable uniqueness from agreement on a real germ. This is the form useful when the
functions are only analytic on a connected continuation domain rather than entire. -/
theorem AnalyticOnNhd.eqOn_of_eventuallyEq_ofReal {U : Set ℂ} {F G : ℂ → H}
    {x₀ : ℝ} (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hU : IsPreconnected U) (hx₀ : (x₀ : ℂ) ∈ U)
    (hEq : ∀ᶠ x : ℝ in 𝓝 x₀, F (x : ℂ) = G (x : ℂ)) : Set.EqOn F G U := by
  let wR : ℕ → ℝ := fun n ↦ x₀ + (n + 1 : ℝ)⁻¹
  let w : ℕ → ℂ := fun n ↦ (wR n : ℂ)
  have hwR : Tendsto wR atTop (𝓝 x₀) := by
    simpa [wR] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hw : Tendsto w atTop (𝓝 (x₀ : ℂ)) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hwR
  have hwne : ∀ n, w n ≠ (x₀ : ℂ) := by
    intro n h
    have hr : x₀ + (n + 1 : ℝ)⁻¹ = x₀ := Complex.ofReal_injective h
    have : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by positivity
    linarith
  have hwithin : Tendsto w atTop (𝓝[≠] (x₀ : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hw, Eventually.of_forall hwne⟩
  have hagree : ∀ᶠ n : ℕ in atTop, F (w n) = G (w n) := by
    filter_upwards [hwR.eventually hEq] with n hn
    exact hn
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hU hx₀
    (hwithin.frequently hagree.frequently)

/-- Two entire functions of one complex variable which agree at every positive real number agree
everywhere. -/
theorem AnalyticOnNhd.eq_of_eqOn_posReal {F G : ℂ → H}
    (hF : AnalyticOnNhd ℂ F univ) (hG : AnalyticOnNhd ℂ G univ)
    (hEq : ∀ x : ℝ, 0 < x → F (x : ℂ) = G (x : ℂ)) : F = G := by
  have hEq' : ∀ᶠ x : ℝ in 𝓝 1, F (x : ℂ) = G (x : ℂ) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact hEq x hx
  have h := hF.eqOn_of_eventuallyEq_ofReal hG isPreconnected_univ (Set.mem_univ _) hEq'
  exact funext fun z ↦ h (Set.mem_univ z)

end
