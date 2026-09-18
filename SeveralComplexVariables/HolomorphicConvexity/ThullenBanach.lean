/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.HolomorphicConvexity.Thullen
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Thullen's continuation lemma for Banach-valued functions

Modulus bounds transfer from a compact set to its scalar holomorphic hull also for
Banach-valued holomorphic functions, by evaluating a norming functional. Consequently the
normalized Taylor coefficients of a Banach-valued holomorphic function at a hull point obey
the Cauchy bounds valid on the compact set, and the Taylor series at the hull point converges
on a sup-norm ball whose radius is a uniform radius of balls around the compact set inside
the domain. This is the constant-radius form of Thullen's lemma with Banach-valued targets.

References: Scheidemann §6.2, Lemma 6.2.7; Hörmander §2.5, Lemma 2.5.3.
-/

@[expose] public noncomputable section

open Set Filter Metric Function
open scoped Topology ENNReal

namespace SeveralComplexVariables

section Hull

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Norm bounds transfer from a set to its scalar holomorphic hull for Banach-valued
holomorphic maps, by norming functionals. -/
theorem norm_le_on_holomorphicHull_vector {U K : Set E} {G : E → F}
    (hG : AnalyticOnNhd ℂ G U) {M : ℝ} (hM : ∀ w ∈ K, ‖G w‖ ≤ M) :
    ∀ z ∈ holomorphicHull U K, ‖G z‖ ≤ M := by
  intro z hz
  obtain ⟨ℓ, hℓ, hℓz⟩ := exists_dual_vector'' ℂ (G z)
  have hcomp : AnalyticOnNhd ℂ (fun w => ℓ (G w)) U :=
    (ℓ.analyticOnNhd univ).comp hG (mapsTo_univ _ _)
  have := hz.2 _ hcomp M fun w hw =>
    calc ‖ℓ (G w)‖ ≤ ‖ℓ‖ * ‖G w‖ := ℓ.le_opNorm _
      _ ≤ 1 * M := by
          gcongr
          exact hM w hw
      _ = M := one_mul M
  rwa [hℓz, RCLike.norm_ofReal, abs_norm] at this

end Hull

section Taylor

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The normalized Taylor coefficients of a Banach-valued function at a center. -/
def vectorTaylorSeries (f : (Fin n → ℂ) → F) (c : Fin n → ℂ) : MvPowerSeries (Fin n) F :=
  fun m => (∏ i, (m i).factorial : ℂ)⁻¹ • multiIndexDeriv m f c

/-- The Taylor coefficients coincide with the integral Cauchy coefficients. -/
theorem coeff_vectorTaylorSeries {f : (Fin n → ℂ) → F} {c : Fin n → ℂ}
    {R : Fin n → ℝ} (hR : ∀ i, 0 < R i)
    (hfc : ContinuousOn f (closedPolydiscWithRadii c R))
    (hfa : ∀ z ∈ closedPolydiscWithRadii c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i)) (m : Fin n →₀ ℕ) :
    vectorTaylorSeries f c m = polydiscCauchyCoeffWithRadii f c R m :=
  (polydiscCauchyCoeffWithRadii_eq_multiIndexDeriv hR hfc hfa m).symm

/-- The Taylor sum of a Banach-valued function centered at a point. -/
def vectorTaylorSumAt (f : (Fin n → ℂ) → F) (a z : Fin n → ℂ) : F :=
  powerSeriesSum (vectorTaylorSeries f a) (z - a)

omit [CompleteSpace F] in
/-- Separate analyticity on a closed polydisc from joint analyticity. -/
theorem analyticAt_update_of_analyticOnNhd_closedPolydisc {f : (Fin n → ℂ) → F}
    {a : Fin n → ℂ} {r : ℝ} (hA : AnalyticOnNhd ℂ f (closedPolydiscWithRadii a (fun _ => r))) :
    ∀ z ∈ closedPolydiscWithRadii a (fun _ => r), ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i) := by
  intro z hz i
  convert hA.analyticAt_update hz i using 1
  funext v
  congr 1
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp [Function.update, hj]

/-- A bound on a closed coordinate ball bounds each normalized Taylor coefficient. -/
theorem norm_vectorTaylorCoeff_le {U : Set (Fin n → ℂ)}
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U)
    {a : Fin n → ℂ} {r M : ℝ} (hr : 0 < r) (hball : closedBall a r ⊆ U)
    (hM : ∀ z ∈ closedBall a r, ‖f z‖ ≤ M) (m : Fin n →₀ ℕ) :
    ‖vectorTaylorSeries f a m‖ ≤ M * ∏ i, r⁻¹ ^ m i := by
  have he : closedPolydiscWithRadii a (fun _ => r) = closedBall a r := by
    rw [closedPolydiscWithRadii_const, closedPolydisc_eq_closedBall hr.le]
  have hA : AnalyticOnNhd ℂ f (closedPolydiscWithRadii a (fun _ => r)) :=
    hf.mono (he ▸ hball)
  rw [coeff_vectorTaylorSeries (fun _ => hr) hA.continuousOn
    (analyticAt_update_of_analyticOnNhd_closedPolydisc hA)]
  exact norm_polydiscCauchyCoeffWithRadii_le (fun _ => hr) (he ▸ hM) m

/-- The Taylor sum of an analytic germ agrees with its representative nearby. -/
theorem vectorTaylorSumAt_eventuallyEq {f : (Fin n → ℂ) → F} {a : Fin n → ℂ}
    (hf : AnalyticAt ℂ f a) : vectorTaylorSumAt f a =ᶠ[𝓝 a] f := by
  classical
  have hb := hf.continuousAt.norm.eventually_lt_const
    (show ‖f a‖ < ‖f a‖ + 1 by linarith)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hf.eventually_analyticAt.and hb)
  have hr₂ : 0 < r / 2 := half_pos hr
  have hsub : closedPolydiscWithRadii a (fun _ => r / 2) ⊆ ball a r := by
    rw [closedPolydiscWithRadii_const, closedPolydisc_eq_closedBall hr₂.le]
    exact closedBall_subset_ball (half_lt_self hr)
  have hA : AnalyticOnNhd ℂ f (closedPolydiscWithRadii a (fun _ => r / 2)) :=
    fun z hz => (hball (hsub hz)).1
  have hs := analyticAt_update_of_analyticOnNhd_closedPolydisc hA
  filter_upwards [ball_mem_nhds a hr₂] with z hz
  have hh : ∀ i, ‖(z - a) i‖ < r / 2 := fun i =>
    (norm_le_pi_norm (z - a) i).trans_lt (by simpa only [mem_ball, dist_eq_norm] using hz)
  have hsum := hasSum_polydiscTaylor (fun _ => hr₂) hh hA.continuousOn hs
    (fun z hz => (hball (hsub hz)).2.le)
  have hc (m : Fin n →₀ ℕ) :
      polydiscCauchyCoeffWithRadii f a (fun _ => r / 2) (Finsupp.equivFunOnFinite m) =
        vectorTaylorSeries f a m :=
    (coeff_vectorTaylorSeries (fun _ => hr₂) hA.continuousOn hs m).symm
  have H := (Finsupp.equivFunOnFinite.hasSum_iff).mpr hsum
  simpa only [vectorTaylorSumAt, powerSeriesSum, Pi.sub_apply, hc,
    add_sub_cancel, Function.comp_apply, Finsupp.equivFunOnFinite_apply] using H.tsum_eq

/-- Uniform weighted Cauchy bounds on a compact set with a uniform radius. -/
theorem exists_bound_vectorTaylorCoeff_mul_radius {U K : Set (Fin n → ℂ)}
    (hK : IsCompact K) {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U)
    {r : ℝ} (hr : 0 < r) (hball : ∀ w ∈ K, ball w r ⊆ U) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (m : Fin n →₀ ℕ) w, w ∈ K →
      ‖vectorTaylorSeries f w m‖ * (t * r) ^ (∑ i, m i) ≤ M := by
  classical
  have htr : 0 < t * r := mul_pos ht hr
  let T := (fun p : (Fin n → ℂ) × (Fin n → ℂ) => p.1 + ((t * r : ℝ) : ℂ) • p.2) ''
    (K ×ˢ closedBall 0 1)
  have hTc : IsCompact T := (hK.prod (isCompact_closedBall _ _)).image (by fun_prop)
  have hTU : T ⊆ U := by
    rintro _ ⟨⟨w, v⟩, ⟨hw, hv⟩, rfl⟩
    apply hball w hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg htr.le]
    have hv' : ‖v‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hv
    calc t * r * ‖v‖ ≤ t * r * 1 := mul_le_mul_of_nonneg_left hv' htr.le
      _ < r := by nlinarith
  have hballT (w) (hw : w ∈ K) : closedBall w (t * r) ⊆ T := by
    intro z hz
    refine ⟨(w, ((t * r : ℝ) : ℂ)⁻¹ • (z - w)), ⟨hw, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg htr.le]
      rw [mem_closedBall, dist_eq_norm] at hz
      exact inv_mul_le_one_of_le₀ hz htr.le
    · simp only
      rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast htr.ne'), one_smul, add_sub_cancel]
  obtain ⟨M, hM⟩ := hTc.exists_bound_of_continuousOn (hf.continuousOn.mono hTU)
  refine ⟨max M 0, le_max_right _ _, fun m w hw => ?_⟩
  have hb := norm_vectorTaylorCoeff_le hf htr ((hballT w hw).trans hTU)
    (fun z hz => hM z (hballT w hw hz)) m
  have hp : (∏ i, (t * r)⁻¹ ^ m i) * (t * r) ^ (∑ i, m i) = 1 := by
    rw [Finset.prod_pow_eq_pow_sum, ← mul_pow, inv_mul_cancel₀ htr.ne', one_pow]
  calc
    _ ≤ (M * ∏ i, (t * r)⁻¹ ^ m i) * (t * r) ^ (∑ i, m i) := by gcongr
    _ = M := by rw [mul_assoc, hp, mul_one]
    _ ≤ max M 0 := le_max_left _ _

/-- **Thullen's lemma for Banach-valued functions, constant radius.** At a point of the
holomorphic hull of a compact set around which balls of radius `r` lie in the domain, the
Taylor series converges on the ball of radius `r` and continues the original germ. -/
theorem taylor_continuation_on_holomorphicHull_vector {U K : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (hball : ∀ w ∈ K, ball w r ⊆ U) {a : Fin n → ℂ} (ha : a ∈ holomorphicHull U K)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U) :
    AnalyticOnNhd ℂ (vectorTaylorSumAt f a) (ball a r) ∧ vectorTaylorSumAt f a =ᶠ[𝓝 a] f := by
  classical
  have hbound {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ m : Fin n →₀ ℕ,
        ‖vectorTaylorSeries f a m‖ * (t * r) ^ (∑ i, m i) ≤ M := by
    obtain ⟨M, hM0, hM⟩ := exists_bound_vectorTaylorCoeff_mul_radius hK hf hr hball ht ht1
    refine ⟨M, hM0, fun m => ?_⟩
    have hg : AnalyticOnNhd ℂ
        (fun w => ((t * r : ℝ) : ℂ) ^ (∑ i, m i) • vectorTaylorSeries f w m) U :=
      analyticOnNhd_const.smul (analyticOnNhd_const.smul
        (hf.iteratedPartialDeriv ho (multiIndexList m)))
    have hnorm (w) : ‖((t * r : ℝ) : ℂ) ^ (∑ i, m i) • vectorTaylorSeries f w m‖ =
        ‖vectorTaylorSeries f w m‖ * (t * r) ^ (∑ i, m i) := by
      rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (mul_pos ht hr).le,
        mul_comm]
    exact (hnorm a) ▸ norm_le_on_holomorphicHull_vector hg
      (fun w hw => (hnorm w).symm ▸ hM m w hw) a ha
  have habs : ball (0 : Fin n → ℂ) r ⊆
      powerSeriesAbsConvergenceSet (vectorTaylorSeries f a) := by
    intro z hz
    have hzr : ‖z‖ < r := by simpa only [mem_ball, dist_zero_right] using hz
    obtain ⟨s, hzs, hsr⟩ := exists_between hzr
    have hs0 : 0 < s := (norm_nonneg z).trans_lt hzs
    obtain ⟨M, hM0, hM⟩ := hbound (div_pos hs0 hr) ((div_lt_one hr).mpr hsr)
    simp only [div_mul_cancel₀ _ hr.ne'] at hM
    have hratio : ‖‖z‖ / s‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hs0.le)]
      exact (div_lt_one hs0).mpr hzs
    have hsum := ((hasSum_pi_geometric (fun _ : Fin n => ‖z‖ / s)
      (fun _ => hratio)).summable.mul_left M).comp_injective Finsupp.equivFunOnFinite.injective
    apply hsum.of_nonneg_of_le (fun _ => by positivity)
    intro m
    calc
      ‖vectorTaylorSeries f a m‖ * ∏ i, ‖z i‖ ^ m i ≤
          ‖vectorTaylorSeries f a m‖ * ∏ i, ‖z‖ ^ m i := by
        gcongr
        exact norm_le_pi_norm z _
      _ = (‖vectorTaylorSeries f a m‖ * s ^ (∑ i, m i)) * ∏ i, (‖z‖ / s) ^ m i := by
        rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, div_pow]
        field_simp
      _ ≤ M * ∏ i, (‖z‖ / s) ^ m i := by
        apply mul_le_mul_of_nonneg_right (hM m)
        positivity
  have hdom : ball (0 : Fin n → ℂ) r ⊆
      powerSeriesConvergenceDomain (vectorTaylorSeries f a) :=
    isOpen_ball.subset_interior_iff.mpr habs
  have hmaps : MapsTo (fun z => z - a) (ball a r)
      (powerSeriesConvergenceDomain (vectorTaylorSeries f a)) := by
    intro z hz
    apply hdom
    simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hz
  exact ⟨(analyticOnNhd_powerSeriesSum _).comp
    (analyticOnNhd_id.sub analyticOnNhd_const) hmaps,
    vectorTaylorSumAt_eventuallyEq (hf a ha.1)⟩

end Taylor

end SeveralComplexVariables
