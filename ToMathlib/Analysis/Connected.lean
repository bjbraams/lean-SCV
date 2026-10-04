/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.Analysis.Normed.Module.Ball.Exterior
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Connectedness of shells and exteriors of balls

In a real normed space of dimension at least two, spherical shells and exteriors of closed balls
with arbitrary centers and radii are preconnected. A shell is the image of the product of an
interval and the unit sphere. Nonempty annuli are path connected. Exterior connectedness uses
the Tau Ceti contributors' `TauCeti.isPreconnected_compl_closedBall` from
`TauCeti.Analysis.Normed.Module.Ball.Exterior`.

## Main results

* `isPreconnected_ball_diff_closedBall`: A shell in a real normed space of dimension at least
  two is preconnected.
* `isPreconnected_compl_closedBall`: The exterior of a closed norm ball is preconnected in
  real dimension at least two.

## References

* `Mathlib.Analysis.Normed.Module.Connected`: formal background used by this module.
-/

public section

open Metric Set

/-- A shell in a real normed space of dimension at least two is preconnected. This radial argument
is independent of any analytic extension theorem. -/
private theorem isPreconnected_ball_diff_closedBall_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
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

/-- An annulus about any center is preconnected in real dimension at least two.
The radii are arbitrary, so empty annuli and negative inner radii are included. -/
theorem isPreconnected_ball_diff_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hdim : 1 < Module.rank ℝ E) (c : E) (ρ R : ℝ) :
    IsPreconnected (ball c R \ closedBall c ρ) := by
  by_cases hρ : 0 ≤ ρ
  · have he : (fun y : E => y + c) '' (ball 0 R \ closedBall 0 ρ) =
        ball c R \ closedBall c ρ := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [mem_ball, mem_closedBall, dist_eq_norm] using hy
      · intro hz
        refine ⟨z - c, ?_, sub_add_cancel z c⟩
        simpa [mem_ball, mem_closedBall, dist_eq_norm] using hz
    rw [← he]
    exact (isPreconnected_ball_diff_closedBall_zero hdim hρ).image _
      (continuous_id.add continuous_const).continuousOn
  · rw [closedBall_eq_empty.mpr (lt_of_not_ge hρ), sdiff_empty]
    exact isPreconnected_ball

/-- The exterior of a closed ball about any center is preconnected in dimension at least two.

This adapts the Tau Ceti contributors' `TauCeti.isPreconnected_compl_closedBall` from
`TauCeti.Analysis.Normed.Module.Ball.Exterior`, including negative radii. -/
theorem isPreconnected_compl_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hdim : 1 < Module.rank ℝ E) (c : E) (ρ : ℝ) :
    IsPreconnected ((closedBall c ρ)ᶜ) :=
  TauCeti.isPreconnected_compl_closedBall hdim c ρ

/-- Every nonempty annulus in real dimension at least two is path connected. -/
theorem isPathConnected_ball_diff_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hdim : 1 < Module.rank ℝ E) (c : E) (ρ R : ℝ)
    (hne : (ball c R \ closedBall c ρ).Nonempty) :
    IsPathConnected (ball c R \ closedBall c ρ) :=
  (isOpen_ball.sdiff isClosed_closedBall).isConnected_iff_isPathConnected.mp
    ⟨hne, isPreconnected_ball_diff_closedBall hdim c ρ R⟩

end
