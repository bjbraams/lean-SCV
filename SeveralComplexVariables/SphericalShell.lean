/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import ToMathlib.Analysis.Connected
public import SeveralComplexVariables.HartogsExtension

/-!
# Spherical shells and exteriors of balls

A radial argument proves connectedness of norm shells; spherical shell extension and extension
from the exterior of a closed ball are then corollaries of the general compact-hole theorem,
without boundedness assumptions. For Euclidean spheres instantiate the
source with `EuclideanSpace ℂ ι`, not the supremum norm on `ι → ℂ`. References:
[Korevaar–Wiegerinck][KorevaarWiegerinck2017] (2017), Applications 2.6.2 and 2.8.3.

## Main results

* `exists_extension_sphericalShell`: **Spherical-shell extension.** This works for any norm in
  finite complex dimension at least two.

## References

* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
-/

public section

open Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Spherical-shell extension.** This works for any norm in finite complex dimension at
least two. The proof applies the general compact-hole theorem. -/
theorem exists_extension_sphericalShell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (hdim : 2 ≤ Module.finrank ℂ E)
    {ρ R : ℝ} (_hρ : 0 ≤ ρ) (hρR : ρ < R) {f : E → F}
    (hf : AnalyticOnNhd ℂ f (ball 0 R \ closedBall 0 ρ)) :
    ∃ g, AnalyticOnNhd ℂ g (ball 0 R) ∧ EqOn g f (ball 0 R \ closedBall 0 ρ) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hrank := one_lt_rank_real_of_two_le_finrank_complex hdim
  exact exists_analyticOnNhd_extension_of_isCompact hdim isOpen_ball
    (isCompact_closedBall 0 ρ) (closedBall_subset_ball hρR)
    (isPreconnected_ball_diff_closedBall hrank 0 ρ R) hf

/-- The infinite-outer-radius case of shell extension: a function outside a closed ball extends to
the whole space. This follows from the compact-hole theorem and imposes no boundedness at
infinity or near the inner sphere. -/
theorem exists_extension_exterior_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (hdim : 2 ≤ Module.finrank ℂ E) {ρ : ℝ} (_hρ : 0 ≤ ρ)
    {f : E → F} (hf : AnalyticOnNhd ℂ f (closedBall (0 : E) ρ)ᶜ) :
    ∃ g, AnalyticOnNhd ℂ g univ ∧ EqOn g f (closedBall (0 : E) ρ)ᶜ := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hrank := one_lt_rank_real_of_two_le_finrank_complex hdim
  simpa only [← compl_eq_univ_sdiff] using exists_analyticOnNhd_extension_of_isCompact hdim
    isOpen_univ (isCompact_closedBall 0 ρ) (subset_univ _)
    (by simpa only [← compl_eq_univ_sdiff] using isPreconnected_compl_closedBall hrank 0 ρ)
    (by simpa only [← compl_eq_univ_sdiff] using hf)

end SeveralComplexVariables
