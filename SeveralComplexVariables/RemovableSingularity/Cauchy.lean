/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Banach-valued holomorphic circle integrals

A compact contour integral of a jointly analytic Banach-valued kernel is analytic
in the parameters. This is the parameter-dependent Cauchy integral used for Riemann
extension. The contour is fixed while its kernel may depend on all parameters.

## Main results

`analyticOnNhd_circleIntegral_kernel` is holomorphy of a circle integral of a jointly
analytic Banach-valued kernel. `analyticOnNhd_integral_smul_compact_kernel` is the
compactly parametrized form.
-/

public section

open Complex MeasureTheory Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E F α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α] [T2Space α] [SecondCountableTopology α]

/-- A compact integral of a jointly analytic Banach-valued kernel, with a fixed
integrable scalar weight, is analytic in its parameters. -/
theorem analyticOnNhd_integral_smul_compact_kernel
    {μ : Measure α} {K : Set α} (hK : IsCompact K)
    {g : α → ℂ} (hg : IntegrableOn g K μ)
    {γ : α → ℂ} (hγ : ContinuousOn γ K)
    {U : Set E} (hU : IsOpen U) {W : Set (E × ℂ)}
    {H : E × ℂ → F} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ x ∈ U, ∀ t ∈ K, (x, γ t) ∈ W) :
    AnalyticOnNhd ℂ (fun x => ∫ t in K, g t • H (x, γ t) ∂μ) U := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  let D := fun (x : E) (t : α) =>
    (fderiv ℂ H (x, γ t)).comp (ContinuousLinearMap.inl ℂ E ℂ)
  have hc : ContinuousOn (fun p : E × α => H (p.1, γ p.2)) (U ×ˢ K) :=
    hH.continuousOn.comp
      (continuousOn_fst.prodMk (hγ.comp continuousOn_snd (fun _ hp => hp.2)))
      (fun p hp => hW p.1 hp.1 p.2 hp.2)
  have hD : ContinuousOn (fun p : E × α => D p.1 p.2) (U ×ˢ K) :=
    (hH.fderiv.continuousOn.comp
      (continuousOn_fst.prodMk (hγ.comp continuousOn_snd (fun _ hp => hp.2)))
      (fun p hp => hW p.1 hp.1 p.2 hp.2)).clm_comp continuousOn_const
  have hslice {x : E} (hx : x ∈ U) : ContinuousOn (fun t => H (x, γ t)) K :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hx, ht⟩)
  apply DifferentiableOn.analyticOnNhd_finiteDimensional _ hU
  intro x hx
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x r).prod hK).bddAbove_image
    (hD.mono (Set.prod_mono hball Subset.rfl)).norm
  apply (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ.restrict K) (F := fun x t => g t • H (x, γ t))
    (F' := fun x t => g t • D x t) (bound := fun t => ‖g t‖ * M)
    (closedBall_mem_nhds x hr) ?_ (hg.smul_continuousOn (hslice hx) hK) ?_ ?_
    (hg.norm.mul_const M) ?_).differentiableAt.differentiableWithinAt
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hg.smul_continuousOn (hslice hy) hK).aestronglyMeasurable
  · exact hg.aestronglyMeasurable.smul
      ((hD.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hx, ht⟩)).aestronglyMeasurable hK.measurableSet)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro y hy
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hM ⟨(y, t), ⟨hy, ht⟩, rfl⟩) (norm_nonneg _)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro y hy
    exact (((hH _ (hW y (hball hy) t ht)).differentiableAt.hasFDerivAt).comp y
      (hasFDerivAt_prodMk_left (𝕜 := ℂ) y (γ t))).const_smul (g t)

omit [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α] [T2Space α] [SecondCountableTopology α] in
/-- A Banach-valued jointly analytic kernel has an analytic circle integral. -/
theorem analyticOnNhd_circleIntegral_kernel
    {U : Set E} (hU : IsOpen U) {W : Set (E × ℂ)}
    {H : E × ℂ → F} (hH : AnalyticOnNhd ℂ H W)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hW : ∀ x ∈ U, ∀ t ∈ sphere c R, (x, t) ∈ W) :
    AnalyticOnNhd ℂ (fun x => ∮ t in C(c, R), H (x, t)) U := by
  have hg : ContinuousOn (fun t : ℝ => deriv (circleMap c R) t) (Icc 0 (2 * Real.pi)) := by
    simp only [deriv_circleMap]
    fun_prop
  have h := analyticOnNhd_integral_smul_compact_kernel (μ := volume) isCompact_Icc
    (hg.integrableOn_compact isCompact_Icc) (continuous_circleMap c R).continuousOn hU hH
    (fun x hx t _ => hW x hx _ (circleMap_mem_sphere c hR t))
  simpa only [circleIntegral_def_Icc] using h

end SeveralComplexVariables
