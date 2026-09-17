/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.HartogsExtension
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Isolated singularities and spherical shells

Punctured product polydiscs extend by the proved Hartogs continuity theorem, without
boundedness assumptions. A radial argument proves connectedness of norm shells; spherical
shell extension is then a corollary of the still-pending general compact-hole theorem.
For Euclidean spheres instantiate the source with `EuclideanSpace ℂ ι`, not the supremum
norm on `ι → ℂ`. References: Korevaar–Wiegerinck (2017), Applications 2.6.2 and 2.8.3.
-/

public section

open Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- An isolated puncture in a product polydisc is removable in complex dimension at least
two. The nonempty base index type makes the dimension restriction explicit. -/
theorem exists_extension_punctured_polydisc {ι : Type*} [Fintype ι] [Nonempty ι]
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {f : ((ι → ℂ) × ℂ) → F}
    (hf : AnalyticOnNhd ℂ f ((ball 0 r ×ˢ ball 0 R) \ {0})) :
    ∃ g, AnalyticOnNhd ℂ g (ball 0 r ×ˢ ball 0 R) ∧
      EqOn g f ((ball 0 r ×ˢ ball 0 R) \ {0}) := by
  classical
  have he : hartogsCylinder (ball (0 : ι → ℂ) r) (ball 0 r \ {0}) 0 R =
      (ball 0 r ×ˢ ball 0 R) \ {0} := by
    ext ⟨z, w⟩
    simp only [hartogsCylinder, mem_union, mem_prod, mem_sdiff, closedBall_zero,
      mem_singleton_iff, Prod.zero_eq_mk, Prod.mk.injEq]
    tauto
  have hn : (ball (0 : ι → ℂ) r \ {0}).Nonempty := by
    refine ⟨fun _ => (r / 2 : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_pi_lt_iff hr]
      intro i
      simpa [abs_of_pos hr] using half_lt_self hr
    · intro hz
      have heq := congrFun hz (Classical.arbitrary ι)
      change (r / 2 : ℂ) = 0 at heq
      have : (r / 2 : ℝ) = 0 := by exact_mod_cast heq
      linarith
  obtain ⟨g, hg, heq⟩ := exists_extension_hartogsCylinder isOpen_ball isPreconnected_ball
    (isOpen_ball.sdiff isClosed_singleton) hn sdiff_subset (le_refl 0) hR (he ▸ hf)
  exact ⟨g, hg, he ▸ heq⟩

/-- A shell in a real normed space of dimension at least two is preconnected. This radial
argument is independent of any analytic extension theorem. -/
theorem isPreconnected_normShell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hdim : 1 < Module.rank ℝ E) {ρ R : ℝ} (hρ : 0 ≤ ρ) :
    IsPreconnected (ball (0 : E) R \ closedBall 0 ρ) := by
  let A : Set (ℝ × E) := Ioo ρ R ×ˢ sphere 0 1
  have hA : IsPreconnected A := isPreconnected_Ioo.prod
    (isPreconnected_sphere hdim (0 : E) 1)
  have hc : Continuous (fun p : ℝ × E => p.1 • p.2) := continuous_fst.smul continuous_snd
  have he : (fun p : ℝ × E => p.1 • p.2) '' A = ball (0 : E) R \ closedBall 0 ρ := by
    apply Subset.antisymm
    · rintro z ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩
      have hvn : ‖v‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hv
      have htn : 0 < t := hρ.trans_lt ht.1
      simpa [mem_ball, mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg htn.le, hvn] using ⟨ht.2, ht.1⟩
    · intro z hz
      have hzR : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hz.1
      have hzρ : ρ < ‖z‖ := by simpa [mem_closedBall, dist_zero_right] using hz.2
      have hn : 0 < ‖z‖ := hρ.trans_lt hzρ
      refine ⟨(‖z‖, ‖z‖⁻¹ • z), ⟨⟨hzρ, hzR⟩, ?_⟩, ?_⟩
      · simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le),
          inv_mul_cancel₀ hn.ne']
      · simp [smul_smul, mul_inv_cancel₀ hn.ne']
  rw [← he]
  exact hA.image _ hc.continuousOn

/-- **Spherical-shell extension.** This works for any norm in finite complex dimension at
least two. The proof currently depends on the pending general compact-hole theorem. -/
theorem exists_extension_sphericalShell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (hdim : 2 ≤ Module.finrank ℂ E)
    {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) {f : E → F}
    (hf : AnalyticOnNhd ℂ f (ball 0 R \ closedBall 0 ρ)) :
    ∃ g, AnalyticOnNhd ℂ g (ball 0 R) ∧ EqOn g f (ball 0 R \ closedBall 0 ρ) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hdimR : 1 < Module.finrank ℝ E := by
    rw [← Module.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]
    omega
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hdimR
  exact exists_analyticOnNhd_extension_of_isCompact hdim isOpen_ball isPreconnected_ball
    (isCompact_closedBall 0 ρ) (closedBall_subset_ball hρR)
    (isPreconnected_normShell hrank hρ) hf

/-- The exterior of a closed norm ball is preconnected in real dimension at least two.
It is the directed union of the finite shells. -/
theorem isPreconnected_compl_closedBall_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hdim : 1 < Module.rank ℝ E) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsPreconnected ((closedBall (0 : E) ρ)ᶜ) := by
  have h : IsPreconnected (⋃ n : ℕ, ball (0 : E) (n : ℝ) \ closedBall 0 ρ) := by
    rw [← sUnion_range]
    apply IsPreconnected.sUnion_directed
    · rintro s ⟨n, rfl⟩ t ⟨m, rfl⟩
      refine ⟨ball (0 : E) ((max n m : ℕ) : ℝ) \ closedBall 0 ρ, ⟨max n m, rfl⟩, ?_, ?_⟩
      · exact sdiff_subset_sdiff_left (ball_subset_ball (by exact_mod_cast le_max_left n m))
      · exact sdiff_subset_sdiff_left (ball_subset_ball (by exact_mod_cast le_max_right n m))
    · rintro s ⟨n, rfl⟩
      exact isPreconnected_normShell hdim hρ
  simpa only [← iUnion_sdiff, iUnion_ball_nat, ← compl_eq_univ_sdiff] using h

/-- The infinite-outer-radius case of shell extension: a function outside a closed ball
extends to the whole space. This depends on the pending compact-hole theorem and imposes
no boundedness at infinity or near the inner sphere. -/
theorem exists_extension_exterior_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (hdim : 2 ≤ Module.finrank ℂ E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {f : E → F} (hf : AnalyticOnNhd ℂ f (closedBall (0 : E) ρ)ᶜ) :
    ∃ g, AnalyticOnNhd ℂ g univ ∧ EqOn g f (closedBall (0 : E) ρ)ᶜ := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hdimR : 1 < Module.finrank ℝ E := by
    rw [← Module.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]
    omega
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hdimR
  simpa only [← compl_eq_univ_sdiff] using exists_analyticOnNhd_extension_of_isCompact hdim
    isOpen_univ isPreconnected_univ (isCompact_closedBall 0 ρ) (subset_univ _)
    (by simpa only [← compl_eq_univ_sdiff] using isPreconnected_compl_closedBall_zero hrank hρ)
    (by simpa only [← compl_eq_univ_sdiff] using hf)

end SeveralComplexVariables
