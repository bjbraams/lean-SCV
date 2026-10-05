/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Complex.CauchyIntegral
public import TauCeti.Analysis.Complex.Conformal.LocalDegree

/-!
# Nonsingularity of injective holomorphic functions of one variable

Nonsingularity is imported from the Tau Ceti contributors'
`TauCeti.deriv_ne_zero_of_injOn` in `TauCeti.Analysis.Complex.Conformal.LocalDegree` and
restated in the `Complex` namespace. Nonconstancy and the logarithmic-derivative circle-integral
formulas are proved here.

## Main results

`deriv_ne_zero_of_injOn` is nonsingularity of an injective holomorphic function of one complex
variable. `not_eventually_constant_of_injOn_complex` excludes a locally constant germ.
`circleIntegral_deriv_div_sub_eq_two_pi_I` and `circleIntegral_deriv_div_sub_eq_zero` evaluate
the circle integral of the logarithmic derivative of `f - f w` for a value `f w` taken only at
`w` (with nonzero derivative) and for an omitted value, respectively.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Filter Metric Function
open scoped Topology

namespace Complex

/-- A function injective on a neighborhood in the complex plane is not locally constant. -/
theorem not_eventually_constant_of_injOn_complex {f : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hU : U ∈ 𝓝 a) (hi : InjOn f U) : ¬ ∀ᶠ z in 𝓝 a, f z = f a := by
  intro hc
  have hs : ({a} : Set ℂ) ∈ 𝓝 a := by
    filter_upwards [hU, hc] with z hz he
    exact hi hz (mem_of_mem_nhds hU) he
  have := mem_interior_iff_mem_nhds.mpr hs
  simp at this

/-- An injective holomorphic function of one complex variable has nonzero derivative.

This adapts the Tau Ceti contributors' `TauCeti.deriv_ne_zero_of_injOn` from
`TauCeti.Analysis.Complex.Conformal.LocalDegree`. -/
theorem deriv_ne_zero_of_injOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 :=
  TauCeti.deriv_ne_zero_of_injOn hf hU hi ha

section LogDeriv

variable {U : Set ℂ} {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}

/-- If `f` omits `w` on a closed disc, the logarithmic derivative of `f - w` has vanishing circle
integral. -/
theorem circleIntegral_deriv_div_sub_eq_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hR : 0 ≤ R) (hRU : closedBall c R ⊆ U) (hne : ∀ z ∈ closedBall c R, f z ≠ w) :
    ∮ z in C(c, R), deriv f z / (f z - w) = 0 := by
  have hd := (hf.analyticOnNhd hU).deriv
  have h0 : ∀ z ∈ closedBall c R, f z - w ≠ 0 := fun z hz ↦ sub_ne_zero.mpr (hne z hz)
  have hcont : ContinuousOn (fun z ↦ deriv f z / (f z - w)) (closedBall c R) :=
    (hd.continuousOn.mono hRU).div ((hf.continuousOn.mono hRU).sub continuousOn_const) h0
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty hcont
    fun z hz ↦ ?_
  have hzU : z ∈ U := hRU (ball_subset_closedBall hz.1)
  exact (hd z hzU).differentiableAt.div
    (((hf z hzU).differentiableAt (hU.mem_nhds hzU)).sub_const w)
    (h0 z (ball_subset_closedBall hz.1))

/-- If `f w` is attained only at `w`, with nonzero derivative there, the logarithmic derivative
of `f - f w` has circle integral `2πi` around any disc containing `w`. -/
theorem circleIntegral_deriv_div_sub_eq_two_pi_I (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hw : w ∈ ball c R) (hRU : closedBall c R ⊆ U) (hw' : deriv f w ≠ 0)
    (huniq : ∀ z ∈ U, f z = f w → z = w) :
    ∮ z in C(c, R), deriv f z / (f z - f w) = 2 * Real.pi * I := by
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg hw
  have hwU := hRU (ball_subset_closedBall hw)
  let g := dslope f w
  have hg : DifferentiableOn ℂ g U := (differentiableOn_dslope (hU.mem_nhds hwU)).mpr hf
  have hg0 : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz
    by_cases hzw : z = w
    · subst hzw
      change dslope f z z ≠ 0
      rw [dslope_same]
      exact hw'
    · change dslope f w z ≠ 0
      rw [dslope_of_ne _ hzw, slope_def_field]
      exact div_ne_zero (sub_ne_zero.mpr fun he ↦ hzw (huniq z hz he)) (sub_ne_zero.mpr hzw)
  have hlog : DifferentiableOn ℂ (fun z ↦ deriv g z / g z) U :=
    (hg.analyticOnNhd hU).deriv.differentiableOn.div hg hg0
  have hzero := circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le countable_empty
    (hlog.continuousOn.mono hRU) (fun z hz ↦
      (hlog z (hRU (ball_subset_closedBall hz.1))).differentiableAt
        (hU.mem_nhds (hRU (ball_subset_closedBall hz.1))))
  have he : EqOn (fun z ↦ deriv f z / (f z - f w))
      (fun z ↦ (z - w)⁻¹ + deriv g z / g z) (sphere c R) := by
    intro z hz
    change deriv f z / (f z - f w) = (z - w)⁻¹ + deriv g z / g z
    have hzU := hRU (sphere_subset_closedBall hz)
    have hzw : z ≠ w := sphere_disjoint_ball.ne_of_mem hz hw
    have hfact : ∀ t, (t - w) * g t = f t - f w := fun t ↦ sub_smul_dslope f w t
    have hd := (((hasDerivAt_id z).sub_const w).mul
      ((hg z hzU).differentiableAt (hU.mem_nhds hzU)).hasDerivAt).deriv
    change deriv (fun t ↦ (t - w) * g t) z = 1 * g z + (z - w) * deriv g z at hd
    have hefun : (fun t ↦ (t - w) * g t) = (fun t ↦ f t - f w) := funext hfact
    rw [hefun, deriv_sub_const] at hd
    rw [hd, ← hfact z]
    field_simp [sub_ne_zero.mpr hzw, hg0 z hzU]
  rw [circleIntegral.integral_congr hR.le he, circleIntegral.integral_add, hzero, add_zero,
    circleIntegral.integral_sub_inv_of_mem_ball hw]
  · exact ((continuousOn_id.sub continuousOn_const).inv₀
      (fun z hz ↦ sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hw))).circleIntegrable hR.le
  · exact (hlog.continuousOn.mono (sphere_subset_closedBall.trans hRU)).circleIntegrable hR.le

end LogDeriv

end Complex
