/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Connected annuli and circular neighborhoods in the complex plane

This file proves connectedness of open complex annuli and circular neighborhoods specified by
bounds on the norm. It also chooses inner and outer coefficient circles with strict bounds
suitable for Laurent-series estimates, treating the zero-radius case separately.

## Main results

* `Complex.isConnected_complex_annulus`: An open annulus with nonnegative inner radius is
  connected.
* `Complex.isConnected_norm_preimage_ball`: A positive-width neighborhood of a nonnegative
  radius is a connected circular domain.
* `Complex.exists_circular_radii_bounds`: Choose inner and outer coefficient circles and
  stricter evaluation bounds. At zero only the upper evaluation bound is required.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Complex

/-- An open annulus with nonnegative inner radius is connected. -/
theorem isConnected_complex_annulus {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    IsConnected {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b} := by
  have hc := (isConnected_Ioo hab).prod (isConnected_univ : IsConnected (univ : Set ℝ))
  have hcont : Continuous (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * exp (p.2 * I)) := by fun_prop
  have he : (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * exp (p.2 * I)) '' (Ioo a b ×ˢ univ) =
      {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b} := by
    ext z
    constructor
    · rintro ⟨⟨r, θ⟩, ⟨hr, _⟩, rfl⟩
      simpa [abs_of_pos (ha.trans_lt hr.1)] using hr
    · intro hz
      exact ⟨(‖z‖, z.arg), ⟨hz, mem_univ _⟩, norm_mul_exp_arg_mul_I z⟩
  rw [← he]
  exact hc.image _ hcont.continuousOn

/-- A positive-width neighborhood of a nonnegative radius is a connected circular domain. -/
theorem isConnected_norm_preimage_ball {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    IsConnected ((norm : ℂ → ℝ) ⁻¹' ball a δ) := by
  by_cases h : a < δ
  · have he : (norm : ℂ → ℝ) ⁻¹' ball a δ = ball 0 (a + δ) := by
      ext z
      simp only [mem_preimage, mem_ball, Real.dist_eq, dist_zero_right, abs_sub_lt_iff]
      constructor
      · intro hz; linarith
      · intro hz; constructor <;> linarith [norm_nonneg z]
    rw [he]
    exact isConnected_ball (by linarith)
  · have he : (norm : ℂ → ℝ) ⁻¹' ball a δ =
        {z : ℂ | a - δ < ‖z‖ ∧ ‖z‖ < a + δ} := by
      ext z
      simp only [mem_preimage, mem_ball, Real.dist_eq, mem_ofPred_eq, abs_sub_lt_iff]
      constructor <;> intro hz <;> constructor <;> linarith [hz.1, hz.2]
    rw [he]
    exact isConnected_complex_annulus (by linarith) (by linarith)

/-- Choose inner and outer coefficient circles and stricter evaluation bounds. At zero only the
upper evaluation bound is required. -/
theorem exists_circular_radii_bounds {V : Set ℂ} (ho : IsOpen V)
    (hrot : ∀ z ∈ V, ∀ w : ℂ, ‖w‖ = ‖z‖ → w ∈ V) {z : ℂ} (hz : z ∈ V) :
    ∃ a b t T : ℝ, 0 < a ∧ a < t ∧ 0 < T ∧ T < b ∧
      (a : ℂ) ∈ V ∧ (b : ℂ) ∈ V ∧ ‖z‖ < T ∧ (z ≠ 0 → t < ‖z‖) := by
  by_cases hz0 : z = 0
  · subst z
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp ho _ hz
    have hb : ((δ / 2 : ℝ) : ℂ) ∈ V := hball (by
      simpa [abs_of_pos hδ] using half_lt_self hδ)
    refine ⟨δ / 2, δ / 2, δ, δ / 4, by positivity, by linarith,
      by positivity, by linarith, hb, hb, ?_, ?_⟩
    · simp only [norm_zero]; positivity
    · simp
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hzV : (‖z‖ : ℂ) ∈ V := hrot z hz _ (by simp)
    obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      ((ho.preimage continuous_ofReal).mem_nhds hzV)
    obtain ⟨a, ha, haz⟩ := exists_between (max_lt hn hlu.1)
    obtain ⟨b, hzb, hb⟩ := exists_between hlu.2
    refine ⟨a, b, (a + ‖z‖) / 2, (‖z‖ + b) / 2,
      (le_max_left _ _).trans_lt ha, by linarith, by linarith, by linarith,
      hsub ⟨(le_max_right _ _).trans_lt ha, haz.trans hlu.2⟩,
      hsub ⟨hlu.1.trans hzb, hb⟩, by linarith, fun _ ↦ by linarith⟩

end Complex
