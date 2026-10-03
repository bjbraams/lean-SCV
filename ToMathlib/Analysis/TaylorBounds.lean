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
# Second-order Taylor remainders in normed spaces

A uniform second-order Taylor bound and Taylor–Peano remainder for maps between
real normed spaces. The source and target may be infinite-dimensional.

## Main results

* `ContDiffAt.exists_taylor_norm_bound`: Vector-valued uniform second-order remainder estimate.
* `ContDiffAt.isLittleO_sub_sub_fderiv_second_order`: Taylor–Peano remainder.
* `ContDiffAt.exists_taylor_bound`: Real-valued corollary.

## References

* `Mathlib.Analysis.SpecialFunctions.Pow.Real`: formal background used by this module.
* `Mathlib.Analysis.Calculus.FDeriv.Symmetric`: formal background used by this module.
* `Mathlib.Analysis.Calculus.MeanValue`: formal background used by this module.
-/

public section

open Filter Metric Set
open scoped Topology

namespace ContDiffAt

/-- **Uniform second-order Taylor bound.** For a `C²` function on a real normed space, the
second-order Taylor remainder at a point is bounded by `ε ‖h‖ ^ 2` for all small increments
`h`. The bound is uniform in the direction of `h`. -/
theorem exists_taylor_norm_bound {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : G → F}
    {t₀ : G} (hg : ContDiffAt ℝ 2 g t₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : G, ‖h‖ < δ →
      ‖g (t₀ + h) - g t₀ - fderiv ℝ g t₀ h - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ g) t₀ h h‖
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
  set φ : G → F := fun k ↦ g (t₀ + k) - g t₀ - D t₀ k - (1 / 2 : ℝ) • B k k with hφdef
  have hφ' : ∀ k : G, ‖k‖ < min δ₁ δ₂ → HasFDerivAt φ (D (t₀ + k) - D t₀ - B k) k := by
    intro k hk
    have hk₂ : t₀ + k ∈ ball t₀ δ₂ := by
      simpa [dist_eq_norm] using hk.trans_le (min_le_right _ _)
    have h1 : HasFDerivAt (fun k ↦ g (t₀ + k)) (D (t₀ + k)) k :=
      ((hball₂ hk₂).comp k ((hasFDerivAt_id k).const_add t₀)).congr_fderiv
        (ContinuousLinearMap.comp_id _)
    have h2 : HasFDerivAt (fun k ↦ D t₀ k) (D t₀) k := (D t₀).hasFDerivAt
    have h3 : HasFDerivAt (fun k ↦ (1 / 2 : ℝ) • B k k) (B k) k := by
      have hb := (B.hasFDerivAt (x := k)).clm_apply (hasFDerivAt_id k)
      have := hb.const_smul (1 / 2 : ℝ)
      refine this.congr_fderiv ?_
      ext s
      simp [hsymm s k, ← two_smul ℝ, smul_smul]
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
  rw [hφ0, sub_zero, sub_zero] at hmvt
  calc ‖g (t₀ + h) - g t₀ - fderiv ℝ g t₀ h - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ g) t₀ h h‖
      = ‖φ h‖ := rfl
    _ ≤ ε * ‖h‖ * ‖h‖ := hmvt
    _ = ε * ‖h‖ ^ 2 := by ring

/-- The second-order Taylor remainder is little-o of the squared increment norm. -/
theorem isLittleO_sub_sub_fderiv_second_order {G F : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : G → F} {t₀ : G} (hg : ContDiffAt ℝ 2 g t₀) :
    (fun h => g (t₀ + h) - g t₀ - fderiv ℝ g t₀ h -
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ g) t₀ h h) =o[𝓝 (0 : G)]
        (fun h => ‖h‖ ^ 2) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hg.exists_taylor_norm_bound hε
  filter_upwards [Metric.ball_mem_nhds (0 : G) hδ] with h hh
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖)] using
    hbound h (by simpa using hh)

/-- Scalar-valued form of the uniform second-order Taylor estimate. -/
theorem exists_taylor_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : G → ℝ} {t₀ : G} (hg : ContDiffAt ℝ 2 g t₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : G, ‖h‖ < δ →
      |g (t₀ + h) - g t₀ - fderiv ℝ g t₀ h - (1 / 2) * fderiv ℝ (fderiv ℝ g) t₀ h h|
        ≤ ε * ‖h‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, smul_eq_mul] using hg.exists_taylor_norm_bound hε

end ContDiffAt

end
