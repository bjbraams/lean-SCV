/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.Reinhardt.Extension

/-!
# Completion in selected Reinhardt coordinates

The selected coordinates can decrease in modulus; the others retain their moduli.
On Reinhardt sets this is precisely coordinate contraction without a coordinate ordering.
The geometric hull works for arbitrary index types. Openness is proved; the analytic
extension theorem is pending. Reference: Scheidemann (2005), Corollary 2.1.15.
-/

public section

open Set Filter
open scoped Topology

namespace SeveralComplexVariables

variable {ι : Type*} {U V : Set (ι → ℂ)} {I : Set ι}

/-- Reinhardt completeness restricted to a specified set of coordinates. -/
def IsCompleteReinhardtIn (I : Set ι) (U : Set (ι → ℂ)) : Prop :=
  ∀ ⦃z⦄, z ∈ U → ∀ ⦃w⦄, (∀ i, ‖w i‖ ≤ ‖z i‖) →
    (∀ i ∉ I, ‖w i‖ = ‖z i‖) → w ∈ U

/-- The hull formed by contracting selected moduli and preserving all other moduli. -/
def partialReinhardtHull (I : Set ι) (U : Set (ι → ℂ)) : Set (ι → ℂ) :=
  {w | ∃ z ∈ U, (∀ i, ‖w i‖ ≤ ‖z i‖) ∧ ∀ i ∉ I, ‖w i‖ = ‖z i‖}

/-- The original set is contained in its partial hull. -/
theorem subset_partialReinhardtHull : U ⊆ partialReinhardtHull I U :=
  fun z hz => ⟨z, hz, fun _ => le_rfl, fun _ _ => rfl⟩

/-- Partial completeness includes Reinhardt symmetry. -/
theorem IsCompleteReinhardtIn.isReinhardt (h : IsCompleteReinhardtIn I U) :
    IsReinhardt U := fun _ hz _ he => h hz (fun i => (he i).le) (fun i _ => he i)

/-- The partial hull has the stated partial completeness property. -/
theorem isCompleteReinhardtIn_partialReinhardtHull :
    IsCompleteReinhardtIn I (partialReinhardtHull I U) := by
  rintro z ⟨v, hv, hle, heq⟩ w hwl hwe
  exact ⟨v, hv, fun i => (hwl i).trans (hle i), fun i hi => (hwe i hi).trans (heq i hi)⟩

/-- The partial hull is the smallest partially complete Reinhardt superset. -/
theorem partialReinhardtHull_min (hUV : U ⊆ V) (hV : IsCompleteReinhardtIn I V) :
    partialReinhardtHull I U ⊆ V := by
  rintro w ⟨z, hz, hle, heq⟩
  exact hV (hUV hz) hle heq

/-- Every partial hull retains independent coordinate rotations. -/
theorem isReinhardt_partialReinhardtHull : IsReinhardt (partialReinhardtHull I U) :=
  isCompleteReinhardtIn_partialReinhardtHull.isReinhardt

/-- Partial completion is monotone in the original set. -/
theorem partialReinhardtHull_mono (hUV : U ⊆ V) :
    partialReinhardtHull I U ⊆ partialReinhardtHull I V :=
  partialReinhardtHull_min (hUV.trans subset_partialReinhardtHull)
    isCompleteReinhardtIn_partialReinhardtHull

/-- Completing twice in the same coordinates has no further effect. -/
theorem partialReinhardtHull_idem :
    partialReinhardtHull I (partialReinhardtHull I U) = partialReinhardtHull I U :=
  Subset.antisymm (partialReinhardtHull_min Subset.rfl isCompleteReinhardtIn_partialReinhardtHull)
    subset_partialReinhardtHull

/-- Completion in all coordinates recovers the existing complete Reinhardt hull. -/
theorem partialReinhardtHull_univ : partialReinhardtHull univ U = completeReinhardtHull U := by
  ext z
  simp [partialReinhardtHull, completeReinhardtHull]

/-- With no selected coordinates, a Reinhardt set is unchanged. -/
theorem partialReinhardtHull_empty (hU : IsReinhardt U) : partialReinhardtHull ∅ U = U := by
  apply Subset.antisymm ?_ subset_partialReinhardtHull
  rintro w ⟨z, hz, _, he⟩
  exact hU hz (fun i => he i (by simp))

/-- Partial hulls of open Reinhardt sets are open. A continuous modulus majorant supplies
nearby witnesses in the original open set. -/
theorem isOpen_partialReinhardtHull [Fintype ι] (ho : IsOpen U) (hR : IsReinhardt U) :
    IsOpen (partialReinhardtHull I U) := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨z, hz, hle, heq⟩
  let v : (ι → ℂ) → (ι → ℂ) := fun x i =>
    if i ∈ I then (max ‖x i‖ ‖z i‖ : ℝ) else (‖x i‖ : ℝ)
  have hv : Continuous v := by
    apply continuous_pi
    intro i
    dsimp [v]
    split_ifs <;> fun_prop
  have hvw : v w ∈ U := by
    apply hR hz
    intro i
    by_cases hi : i ∈ I
    · simp [v, hi, max_eq_right (hle i)]
    · simp [v, hi, heq i hi]
  apply Filter.mem_of_superset (hv.continuousAt.preimage_mem_nhds (ho.mem_nhds hvw))
  intro x hx
  refine ⟨v x, hx, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ I
    · simp [v, hi, abs_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))]
    · simp [v, hi]
  · intro i hi
    simp [v, hi]

/-- Extension in the coordinates whose zero hyperplanes meet the connected domain.
Proof pending: remove the corresponding negative Laurent coefficients and control the
remaining Laurent series on the partial hull. No common point on those hyperplanes is required. -/
theorem exists_extension_partialReinhardtHull {n : ℕ} {I : Set (Fin n)}
    {U : Set (Fin n → ℂ)} (ho : IsOpen U) (hc : IsConnected U) (hR : IsReinhardt U)
    (hmeet : ∀ i ∈ I, ∃ z ∈ U, z i = 0)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U) :
    ∃ g, AnalyticOnNhd ℂ g (partialReinhardtHull I U) ∧ EqOn g f U := by
  sorry

end SeveralComplexVariables
