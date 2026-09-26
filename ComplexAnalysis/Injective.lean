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

/-!
# Nonsingularity of injective holomorphic functions of one variable

The open mapping theorem makes the inverse continuous. Isolated zeros of the derivative make it
holomorphic off the image of the base point, so the removable singularity theorem makes it
holomorphic there too. The chain rule then excludes a zero derivative.

## Main results

`deriv_ne_zero_of_injOn` is nonsingularity of an injective holomorphic function of one complex
variable. `not_eventually_constant_of_injOn_complex` and `not_eventually_deriv_eq_zero_of_injOn`
exclude a locally constant germ and a locally vanishing derivative.
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

/-- The derivative of a locally injective analytic function is not locally identically zero. -/
theorem not_eventually_deriv_eq_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hU : U ∈ 𝓝 a) (hi : InjOn f U) (hf : AnalyticAt ℂ f a) :
    ¬ deriv f =ᶠ[𝓝 a] 0 := by
  intro hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hU (hf.eventually_analyticAt.and hz))
  apply not_eventually_constant_of_injOn_complex hU hi
  filter_upwards [ball_mem_nhds a hr] with z hz
  exact isOpen_ball.is_const_of_deriv_eq_zero isPreconnected_ball
    (fun w hw ↦ ((hball hw).2.1).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hball hw).2.2) hz (mem_ball_self hr)

/-- An injective holomorphic function of one complex variable has nonzero derivative. -/
theorem deriv_ne_zero_of_injOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  have hfa := hf.analyticOnNhd hU a ha
  have hopen : 𝓝 (f a) ≤ map f (𝓝 a) :=
    hfa.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (not_eventually_constant_of_injOn_complex (hU.mem_nhds ha) hi)
  let g := invFunOn f U
  have hleft : (g ∘ f) =ᶠ[𝓝 a] id :=
    Filter.mem_of_superset (hU.mem_nhds ha) (fun _ hz ↦ hi.leftInvOn_invFunOn hz)
  have hga : g (f a) = a := hi.leftInvOn_invFunOn ha
  have hgcont : ContinuousAt g (f a) := by
    rw [ContinuousAt, hga]
    have ht : Tendsto (g ∘ f) (𝓝 a) (𝓝 a) := tendsto_id.congr' hleft.symm
    change map (g ∘ f) (𝓝 a) ≤ 𝓝 a at ht
    exact (Filter.map_mono hopen).trans (by rwa [map_map])
  have hisol : ∀ᶠ z in 𝓝[≠] a, deriv f z ≠ 0 :=
    hfa.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (not_eventually_deriv_eq_zero_of_injOn (hU.mem_nhds ha) hi hfa)
  have hV : {z | z ∈ U ∧ (z ≠ a → deriv f z ≠ 0)} ∈ 𝓝 a :=
    inter_mem (hU.mem_nhds ha) (eventually_nhdsWithin_iff.mp hisol)
  have hW : f '' {z | z ∈ U ∧ (z ≠ a → deriv f z ≠ 0)} ∈ 𝓝 (f a) :=
    hopen (image_mem_map hV)
  have hgd : ∀ᶠ w in 𝓝[≠] (f a), DifferentiableAt ℂ g w := by
    filter_upwards [nhdsWithin_le_nhds hW, self_mem_nhdsWithin] with w hw hwne
    obtain ⟨z, ⟨hz, hdz⟩, rfl⟩ := hw
    have hzane : z ≠ a := fun h ↦ hwne (by simp [h])
    have hstrict := (hf.analyticOnNhd hU z hz).contDiffAt.hasStrictDerivAt (n := 1) one_ne_zero
    exact (hstrict.to_local_left_inverse (hdz hzane)
      (Filter.mem_of_superset (hU.mem_nhds hz)
        (fun _ ht ↦ hi.leftInvOn_invFunOn ht))).hasDerivAt.differentiableAt
  have hgan := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hgcont
  have hder : deriv g (f a) * deriv f a = 1 := by
    have hc := hgan.differentiableAt.hasDerivAt.comp a hfa.differentiableAt.hasDerivAt
    exact hc.deriv.symm.trans ((Filter.EventuallyEq.deriv_eq hleft).trans (deriv_id a))
  intro hz
  simp [hz] at hder

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
