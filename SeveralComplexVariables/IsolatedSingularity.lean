/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.SphericalShell

/-!
# Removal of isolated singularities

A point is a compact hole whose complement in a small ball is preconnected in complex dimension
at least two, so the compact-hole theorem extends the function across it locally. The extension
is then glued to the original function. No boundedness hypothesis is imposed near the puncture. Reference:
[Scheidemann][Scheidemann2005] (2005), Corollary 2.3.2.

## Main results

`exists_analyticOnNhd_extension_diff_singleton` removes an isolated singularity of a Banach-valued
holomorphic map on an open set in complex dimension at least two, without a local boundedness
hypothesis.

## References

* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Metric Filter
open scoped Topology

namespace SeveralComplexVariables

/-- An isolated singularity is removable on any open set in complex dimension at least two. The
target is any complex Banach space, and the domain need not be connected. This is the special case
of the compact-hole theorem `exists_analyticOnNhd_extension_of_isCompact` for a point hole in a
small ball, whose punctured ball is preconnected; the local extension is glued to `f`. -/
theorem exists_analyticOnNhd_extension_diff_singleton
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (hdim : 2 ≤ Module.finrank ℂ E) {U : Set E} (ho : IsOpen U)
    {a : E} (ha : a ∈ U) {f : E → F} (hf : AnalyticOnNhd ℂ f (U \ {a})) :
    ∃ g, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ {a}) := by
  classical
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp ho a ha
  have hconn : IsPreconnected (ball a r \ {a}) := by
    simpa only [closedBall_zero] using
      isPreconnected_ball_diff_closedBall (one_lt_rank_real_of_two_le_finrank_complex hdim) a 0 r
  obtain ⟨g, hg, hgf⟩ := exists_analyticOnNhd_extension_of_isCompact hdim isOpen_ball
    isCompact_singleton (singleton_subset_iff.mpr (mem_ball_self hr)) hconn
    (hf.mono (sdiff_subset_sdiff_left hrU))
  refine ⟨Function.update f a (g a), fun x hx => ?_, fun x hx => Function.update_of_ne hx.2 _ _⟩
  by_cases hxa : x = a
  · subst x
    refine (hg a (mem_ball_self hr)).congr ?_
    filter_upwards [ball_mem_nhds a hr] with y hy
    by_cases hya : y = a
    · simp [hya]
    · rw [Function.update_of_ne hya, hgf ⟨hy, hya⟩]
  · refine (hf x ⟨hx, hxa⟩).congr ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hxa] with y hy
    exact (Function.update_of_ne hy _ _).symm

end SeveralComplexVariables
