/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary bounds for Taylor remainders

A uniform second-order Taylor bound for real normed spaces, with real inequalities
for choosing a radius and absorbing a cubic error into a quadratic bound.

## Main results

* `ContDiffAt.exists_taylor_bound`: Uniform second-order remainder estimate for a `C²` function
  on a real normed space.

* `le_one_and_mul_add_le_of_le_min`: Radius constraints used to absorb a cubic Taylor error into a
  quadratic budget `η t ^ 2`.
* `taylor_remainder_add_cubic_le`: Combine a second-order remainder of size `O(t ^ 2)` with a cubic
  error of size `O(t ^ 3)` into a single quadratic bound `η t ^ 2`.

## References

* `Mathlib.Analysis.SpecialFunctions.Pow.Real`: formal background used by this module.
* `Mathlib.Analysis.Calculus.FDeriv.Symmetric`: formal background used by this module.
* `Mathlib.Analysis.Calculus.MeanValue`: formal background used by this module.
-/

public section

namespace Real

/-- Radius constraints used to absorb a cubic Taylor error into a quadratic budget `η t ^ 2`. -/
theorem le_one_and_mul_add_le_of_le_min {η M₀ M₁ δ' r : ℝ} (hM₀ : 0 ≤ M₀)
    (hM₁ : 0 ≤ M₁) (hr : 0 < r)
    (hr₀ : r ≤ min 1 (min (η / (2 * (M₁ + 1))) (δ' / (2 * (M₀ + 1))))) :
    r ≤ 1 ∧ r * (M₁ + 1) ≤ η / 2 ∧ r * (M₀ + 1) < δ' := by
  have hr1 : r ≤ 1 := hr₀.trans (min_le_left _ _)
  have hrM₁ : r * (M₁ + 1) ≤ η / 2 := by
    have := hr₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hrδ' : r * (M₀ + 1) < δ' := by
    have := hr₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at this
    have : 0 < r * (M₀ + 1) := by positivity
    linarith
  exact ⟨hr1, hrM₁, hrδ'⟩

/-- Combine a second-order remainder of size `O(t ^ 2)` with a cubic error of size `O(t ^ 3)` into a
single quadratic bound `η t ^ 2`. -/
theorem taylor_remainder_add_cubic_le {η t M₀ M₁ rem cub : ℝ} (ht : 0 < t) (hη : 0 < η)
    (htM₁ : t * (M₁ + 1) ≤ η / 2)
    (hrem : |rem| ≤ η / (2 * (M₀ ^ 2 + 1)) * (t * M₀) ^ 2) (hcub : |cub| ≤ M₁ * t ^ 3) :
    |rem + cub| ≤ η * t ^ 2 := by
  have hR : |rem| ≤ η / 2 * t ^ 2 := by
    refine hrem.trans ?_
    rw [mul_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : M₀ ^ 2 ≤ M₀ ^ 2 + 1 := by linarith
    calc η * (t ^ 2 * M₀ ^ 2) ≤ η * (t ^ 2 * (M₀ ^ 2 + 1)) := by gcongr
      _ = η / 2 * t ^ 2 * (2 * (M₀ ^ 2 + 1)) := by ring
  have hC : |cub| ≤ η / 2 * t ^ 2 := by
    refine hcub.trans ?_
    calc M₁ * t ^ 3 = t * M₁ * t ^ 2 := by ring
      _ ≤ η / 2 * t ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : t * M₁ ≤ t * (M₁ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) ht.le
          linarith
  calc |rem + cub| ≤ |rem| + |cub| := abs_add_le _ _
    _ ≤ η / 2 * t ^ 2 + η / 2 * t ^ 2 := add_le_add hR hC
    _ = η * t ^ 2 := by ring

end Real

end

public section

open Filter Metric Set
open scoped Topology

namespace ContDiffAt

/-- **Uniform second-order Taylor bound.** For a `C²` function on a real normed space, the
second-order Taylor remainder at a point is bounded by `ε ‖h‖ ^ 2` for all small increments
`h`. The bound is uniform in the direction of `h`. -/
theorem exists_taylor_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : G → ℝ}
    {t₀ : G} (hg : ContDiffAt ℝ 2 g t₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : G, ‖h‖ < δ →
      |g (t₀ + h) - g t₀ - fderiv ℝ g t₀ h - (1 / 2) * fderiv ℝ (fderiv ℝ g) t₀ h h|
        ≤ ε * ‖h‖ ^ 2 := by
  set D := fderiv ℝ g
  set B := fderiv ℝ (fderiv ℝ g) t₀
  have hD : HasFDerivAt D B t₀ :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hev : ∀ᶠ y in 𝓝 t₀, HasFDerivAt g (D y) y := by
    filter_upwards [hg.eventually (by simp)] with y hy
    exact (hy.differentiableAt (by norm_num)).hasFDerivAt
  have hsymm : ∀ v w, B v w = B w v := second_derivative_symmetric_of_eventually hev hD
  have hlo : ∀ᶠ h in 𝓝 (0 : G), ‖D (t₀ + h) - D t₀ - B h‖ ≤ ε * ‖h‖ :=
    (hasFDerivAt_iff_isLittleO_nhds_zero.mp hD).def hε
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.mem_nhds_iff.mp hlo
  obtain ⟨δ₂, hδ₂, hball₂⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun h hh ↦ ?_⟩
  set φ : G → ℝ := fun k ↦ g (t₀ + k) - g t₀ - D t₀ k - (1 / 2) * B k k with hφdef
  have hφ' : ∀ k : G, ‖k‖ < min δ₁ δ₂ → HasFDerivAt φ (D (t₀ + k) - D t₀ - B k) k := by
    intro k hk
    have hk₂ : t₀ + k ∈ ball t₀ δ₂ := by
      simpa [dist_eq_norm] using hk.trans_le (min_le_right _ _)
    have h1 : HasFDerivAt (fun k ↦ g (t₀ + k)) (D (t₀ + k)) k :=
      ((hball₂ hk₂).comp k ((hasFDerivAt_id k).const_add t₀)).congr_fderiv
        (ContinuousLinearMap.comp_id _)
    have h2 : HasFDerivAt (fun k ↦ D t₀ k) (D t₀) k := (D t₀).hasFDerivAt
    have h3 : HasFDerivAt (fun k ↦ (1 / 2 : ℝ) * B k k) (B k) k := by
      have hb := (B.hasFDerivAt (x := k)).clm_apply (hasFDerivAt_id k)
      have := hb.const_mul (1 / 2 : ℝ)
      refine this.congr_fderiv ?_
      ext s
      simp
      linarith [hsymm s k]
    have := (h1.sub_const (g t₀)).sub h2 |>.sub h3
    convert this using 1
  have hbound : ∀ k ∈ closedBall (0 : G) ‖h‖, ‖D (t₀ + k) - D t₀ - B k‖ ≤ ε * ‖h‖ := by
    intro k hk
    have hk' : ‖k‖ ≤ ‖h‖ := by simpa using hk
    have hk₁ : k ∈ ball (0 : G) δ₁ := by
      simpa using hk'.trans_lt (hh.trans_le (min_le_left _ _))
    exact (hball₁ hk₁).trans (mul_le_mul_of_nonneg_left hk' hε.le)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := φ) (f' := fun k ↦ D (t₀ + k) - D t₀ - B k) (s := closedBall (0 : G) ‖h‖)
    (fun k hk ↦ (hφ' k (by
      have hk' : ‖k‖ ≤ ‖h‖ := by simpa using hk
      exact hk'.trans_lt hh)).hasFDerivWithinAt)
    hbound (convex_closedBall _ _) (mem_closedBall_self (norm_nonneg h))
    (mem_closedBall_zero_iff.mpr le_rfl)
  have hφ0 : φ 0 = 0 := by simp [hφdef]
  rw [hφ0, sub_zero, sub_zero, Real.norm_eq_abs] at hmvt
  calc |g (t₀ + h) - g t₀ - fderiv ℝ g t₀ h - (1 / 2) * fderiv ℝ (fderiv ℝ g) t₀ h h|
      = |φ h| := rfl
    _ ≤ ε * ‖h‖ * ‖h‖ := hmvt
    _ = ε * ‖h‖ ^ 2 := by ring

end ContDiffAt

end
