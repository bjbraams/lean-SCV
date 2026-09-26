/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.LaurentSeries.Geometry
public import SeveralComplexVariables.Polydisc

/-!
# Circular product neighborhoods in Reinhardt sets

An open Reinhardt set contains a product of connected circular domains around each point,
including points on coordinate hyperplanes.

## Main results

`IsReinhardt.exists_circular_product_neighborhood` produces such a product neighborhood of any
point. `isConnected_complex_annulus` and `isConnected_norm_preimage_ball` record connectedness
of the circular factors, including degenerate annuli that meet a coordinate hyperplane.

## References

* V. Scheidemann, *Introduction to Complex Analysis in Several Variables*,
  Birkhäuser, 2005 (background on holomorphic functions of several variables).
-/

public noncomputable section

open Complex Set Metric
open scoped Topology

namespace SeveralComplexVariables

/-- Every point of an open Reinhardt set has a circular product neighborhood with connected factors.
The factors containing zero are discs. -/
theorem IsReinhardt.exists_circular_product_neighborhood {n : ℕ} {U : Set (Fin n → ℂ)}
    (hR : IsReinhardt U) (ho : IsOpen U) {z : Fin n → ℂ} (hz : z ∈ U) :
    ∃ V : Fin n → Set ℂ,
      (∀ i, IsOpen (V i)) ∧ (∀ i, IsConnected (V i)) ∧
      (∀ i, ∀ v ∈ V i, ∀ w : ℂ, ‖w‖ = ‖v‖ → w ∈ V i) ∧
      z ∈ Set.pi univ V ∧ Set.pi univ V ⊆ U := by
  have hz' : (fun i => (‖z i‖ : ℂ)) ∈ U := hR hz (fun i => by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp ho _ hz'
  let V : Fin n → Set ℂ := fun i => (norm : ℂ → ℝ) ⁻¹' ball ‖z i‖ δ
  refine ⟨V, fun i => isOpen_ball.preimage continuous_norm,
    fun i => isConnected_norm_preimage_ball (norm_nonneg _) hδ, ?_, ?_, ?_⟩
  · intro i v hv w hw
    change ‖w‖ ∈ ball ‖z i‖ δ
    rwa [hw]
  · intro i _
    exact mem_ball_self hδ
  · intro w hw
    apply hR (z := fun i => (‖w i‖ : ℂ)) (hball ?_) (fun i => by simp)
    rw [mem_ball, dist_pi_lt_iff hδ]
    intro i
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [V, mem_preimage, mem_ball, Real.dist_eq] using hw i (mem_univ _)

end SeveralComplexVariables
