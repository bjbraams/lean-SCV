/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Second-order Taylor remainders in normed spaces

A uniform second-order Taylor bound and Taylor–Peano remainder for maps between
real normed spaces. The source and target may be infinite-dimensional.

## Main results

* `DifferentiableAt.isLittleO_sub_sub_fderiv_second_order`: Taylor–Peano remainder for a map
  that is differentiable near the point and whose derivative is differentiable at the point.
* `ContDiffAt.isLittleO_sub_sub_fderiv_second_order`: the same for a `C²` map.
* `ContDiffAt.exists_taylor_norm_bound`: Vector-valued uniform second-order remainder estimate.
* `ContDiffAt.exists_taylor_bound`: Real-valued corollary.

## Implementation notes

The remainder estimate integrates the little-o bound for the derivative of the remainder along
segments with Mathlib's `Convex.isLittleO_pow_succ`; symmetry of the second derivative is
`second_derivative_symmetric_of_eventually`.
-/

public section

open Filter Metric Set
open scoped Topology

/-- **Taylor–Peano remainder of order two.** Let `g` be differentiable near `t₀`, with
`fderiv ℝ g` differentiable at `t₀`. Then the second-order Taylor remainder at `t₀` is little-o of
the squared increment norm. The derivative of the remainder is `o(‖h‖)` by differentiability of
`fderiv ℝ g` and symmetry of the second derivative; Mathlib's `Convex.isLittleO_pow_succ`
integrates this along segments. -/
theorem DifferentiableAt.isLittleO_sub_sub_fderiv_second_order {G F : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : G → F} {t₀ : G} (hg' : DifferentiableAt ℝ (fderiv ℝ g) t₀)
    (hg : ∀ᶠ y in 𝓝 t₀, DifferentiableAt ℝ g y) :
    (fun h ↦ g (t₀ + h) - g t₀ - fderiv ℝ g t₀ h -
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ g) t₀ h h) =o[𝓝 (0 : G)]
        (fun h ↦ ‖h‖ ^ 2) := by
  set D := fderiv ℝ g
  set B := fderiv ℝ (fderiv ℝ g) t₀
  have hD : HasFDerivAt D B t₀ := hg'.hasFDerivAt
  have hev : ∀ᶠ y in 𝓝 t₀, HasFDerivAt g (D y) y := hg.mono fun _ hy ↦ hy.hasFDerivAt
  have hsymm : ∀ v w, B v w = B w v := second_derivative_symmetric_of_eventually hev hD
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hφ' : ∀ k ∈ ball (0 : G) δ, HasFDerivWithinAt
      (fun k ↦ g (t₀ + k) - g t₀ - D t₀ k - (1 / 2 : ℝ) • B k k) (D (t₀ + k) - D t₀ - B k)
      (ball 0 δ) k := by
    intro k hk
    have hk' : t₀ + k ∈ ball t₀ δ := by simpa [dist_eq_norm] using hk
    have h1 : HasFDerivAt (fun k ↦ g (t₀ + k)) (D (t₀ + k)) k :=
      ((hball hk').comp k ((hasFDerivAt_id k).const_add t₀)).congr_fderiv
        (ContinuousLinearMap.comp_id _)
    have h3 : HasFDerivAt (fun k ↦ (1 / 2 : ℝ) • B k k) (B k) k := by
      refine (((B.hasFDerivAt (x := k)).clm_apply (hasFDerivAt_id k)).const_smul
        (1 / 2 : ℝ)).congr_fderiv ?_
      ext s
      simp [hsymm s k, ← two_smul ℝ, smul_smul]
    exact (((h1.sub_const (g t₀)).sub (D t₀).hasFDerivAt).sub h3).hasFDerivWithinAt
  have hlo : (fun k ↦ D (t₀ + k) - D t₀ - B k) =o[𝓝[ball 0 δ] (0 : G)]
      fun k ↦ ‖k - 0‖ ^ 1 := by
    simpa using ((hasFDerivAt_iff_isLittleO_nhds_zero.mp hD).norm_right).mono nhdsWithin_le_nhds
  have h := (convex_ball (0 : G) δ).isLittleO_pow_succ (mem_ball_self hδ) hφ' hlo
  rw [nhdsWithin_eq_nhds.mpr (ball_mem_nhds _ hδ)] at h
  simpa using h

namespace ContDiffAt

/-- **Taylor–Peano remainder of order two** for a `C²` function on a real normed space. -/
theorem isLittleO_sub_sub_fderiv_second_order {G F : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : G → F} {t₀ : G} (hg : ContDiffAt ℝ 2 g t₀) :
    (fun h ↦ g (t₀ + h) - g t₀ - fderiv ℝ g t₀ h -
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ g) t₀ h h) =o[𝓝 (0 : G)]
        (fun h ↦ ‖h‖ ^ 2) :=
  ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    |>.isLittleO_sub_sub_fderiv_second_order
      (hg.eventually (by simp) |>.mono fun _ hy ↦ hy.differentiableAt (by norm_num))

/-- **Uniform second-order Taylor bound.** For a `C²` function on a real normed space, the
second-order Taylor remainder at a point is bounded by `ε ‖h‖ ^ 2` for all small increments
`h`. The bound is uniform in the direction of `h`. -/
theorem exists_taylor_norm_bound {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : G → F}
    {t₀ : G} (hg : ContDiffAt ℝ 2 g t₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : G, ‖h‖ < δ →
      ‖g (t₀ + h) - g t₀ - fderiv ℝ g t₀ h - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ g) t₀ h h‖
        ≤ ε * ‖h‖ ^ 2 := by
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp (hg.isLittleO_sub_sub_fderiv_second_order.def hε)
  exact ⟨δ, hδ, fun h hh ↦ by simpa using hb (by simpa using hh)⟩

/-- Scalar-valued form of the uniform second-order Taylor estimate. -/
theorem exists_taylor_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : G → ℝ} {t₀ : G} (hg : ContDiffAt ℝ 2 g t₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : G, ‖h‖ < δ →
      |g (t₀ + h) - g t₀ - fderiv ℝ g t₀ h - (1 / 2) * fderiv ℝ (fderiv ℝ g) t₀ h h|
        ≤ ε * ‖h‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, smul_eq_mul] using hg.exists_taylor_norm_bound hε

end ContDiffAt

end
