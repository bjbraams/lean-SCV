/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Holomorphic.FunctionSpace
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Shared Montel and Vitali arguments

Compact-local bounds imply equicontinuity by the complex Schwarz estimate. Arzelà–Ascoli
then gives compactness when the holomorphic subspace is closed. Vitali convergence uses
convergence on a uniqueness set. Closedness and the uniqueness criterion are explicit inputs,
so both one-variable and several-variable analysis use this file without a dependency cycle.

## Main results

* `Complex.equicontinuous_of_holomorphic_bounded_on_compacts`: Compact-local bounds on a
  holomorphic family give equicontinuity. Banach targets are allowed here; finite dimensionality
  is needed only for compactness in Montel's theorem.
* `Complex.isCompact_closure_of_holomorphic_bounded_on_compacts_of_isClosed`: **Montel's
  theorem.** A compact-locally bounded family of holomorphic maps into a finite-dimensional
  complex normed space has compact closure in the compact-open topology.
* `Complex.exists_tendsto_of_holomorphic_bounded_on_compacts_of_isClosed_of_unique`:
  Compact-local bounds and convergence on a uniqueness set imply convergence of the whole
  sequence. Closedness of the holomorphic space is an explicit input, supplied by the relevant
  Weierstrass theorem.
* `Complex.exists_subseq_tendsto_of_holomorphic_bounded_on_compacts_of_isClosed`: The sequential
  Montel conclusion for compact-locally bounded holomorphic maps, with closedness supplied by a
  Weierstrass theorem.

## References

* `Mathlib.Analysis.Complex.Schwarz`: formal background used by this module.
* `Mathlib.Topology.MetricSpace.Equicontinuity`: formal background used by this module.
* `Mathlib.Topology.UniformSpace.Ascoli`: formal background used by this module.
-/

public section

open Filter Function Metric Set
open scoped Topology

namespace Complex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Compact-local bounds on a holomorphic family give equicontinuity. Banach targets are allowed
here; finite dimensionality is needed only for compactness in Montel's theorem. -/
theorem equicontinuous_of_holomorphic_bounded_on_compacts
    {U : TopologicalSpace.Opens E} {S : Set (HolomorphicMap U F)}
    (hb : ∀ K ⊆ (U : Set E), IsCompact K → ∃ M : ℝ,
      ∀ f ∈ S, ∀ z ∈ K, ‖openExtension U f.val z‖ ≤ M) :
    Equicontinuous (fun f : S ↦ (f.val.val : U → F)) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  intro c
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (U.isOpen.mem_nhds c.property)
  obtain ⟨M, hM⟩ := hb (closedBall (c : E) R) hRU (isCompact_closedBall _ _)
  let C : ℝ := 2 * max M 0 / R
  have hC : 0 ≤ C := div_nonneg (by positivity) hR.le
  refine ⟨min R (ε / (C + 1)), lt_min hR (div_pos hε (by positivity)), ?_⟩
  intro w hw f
  have hwr : dist (w : E) c < R := (lt_min_iff.mp hw).1
  have hwe : dist (w : E) c < ε / (C + 1) := (lt_min_iff.mp hw).2
  have hmaps : MapsTo (openExtension U f.val.val) (ball (c : E) R)
      (closedBall (openExtension U f.val.val c) (2 * max M 0)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖openExtension U f.val.val z - openExtension U f.val.val c‖ ≤
          ‖openExtension U f.val.val z‖ + ‖openExtension U f.val.val c‖ := norm_sub_le _ _
      _ ≤ max M 0 + max M 0 := add_le_add
        ((hM f.val f.property z (ball_subset_closedBall hz)).trans (le_max_left _ _))
        ((hM f.val f.property c (mem_closedBall_self hR.le)).trans (le_max_left _ _))
      _ = 2 * max M 0 := by ring
  have hn := dist_le_div_mul_dist_of_mapsTo_ball
    (f.val.property.differentiableOn.mono (ball_subset_closedBall.trans hRU)) hmaps hwr
  simp only [openExtension_coe] at hn
  have hlt : (C + 1) * dist (w : E) c < ε := by
    nlinarith [(lt_div_iff₀ (by positivity : 0 < C + 1)).mp hwe]
  rw [dist_comm]
  change dist (f.val.val w) (f.val.val c) < ε
  change dist (f.val.val w) (f.val.val c) ≤ C * dist (w : E) c at hn
  nlinarith [show 0 ≤ dist (w : E) (c : E) from dist_nonneg]

/-- **Montel's theorem.** A compact-locally bounded family of holomorphic maps into a
finite-dimensional complex normed space has compact closure in the compact-open topology.

For the one-variable scalar case, see Vincent Beffara's RMT4 formalization. See `CREDITS.md`. -/
theorem isCompact_closure_of_holomorphic_bounded_on_compacts_of_isClosed
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens E}
    {S : Set (HolomorphicMap U F)}
    (hclosed : IsClosed (holomorphicSubmodule (F := F) U : Set C(U, F)))
    (hb : ∀ K ⊆ (U : Set E), IsCompact K → ∃ M : ℝ,
      ∀ f ∈ S, ∀ z ∈ K, ‖openExtension U f.val z‖ ≤ M) : IsCompact (closure S) := by
  let := FiniteDimensional.proper ℂ F
  let : CompleteSpace (HolomorphicMap U F) := hclosed.isComplete.completeSpace_coe
  let := UniformOnFun.t2Space_of_covering (β := F)
    (𝔖 := {K : Set U | IsCompact K}) (by
      apply eq_univ_iff_forall.mpr
      intro z
      exact mem_sUnion_of_mem (mem_singleton z) isCompact_singleton)
  have he : Topology.IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set U | IsCompact K} ∘
        (fun f : HolomorphicMap U F ↦ (f.val : U → F))) := by
    exact (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.comp
      isUniformEmbedding_subtype_val).isClosedEmbedding
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK ↦ hK) he
  · intro K hK
    exact (equicontinuous_of_holomorphic_bounded_on_compacts hb).equicontinuousOn K
  · intro K hK z hz
    obtain ⟨M, hM⟩ := hb {(z : E)} (singleton_subset_iff.mpr z.property) isCompact_singleton
    refine ⟨closedBall (0 : F) (max M 0), isCompact_closedBall _ _, ?_⟩
    intro f hf
    have h := (hM f hf z (mem_singleton _)).trans (le_max_left M 0)
    simpa using h

/-- Compact-local bounds and convergence on a uniqueness set imply convergence of the whole
sequence. Closedness of the holomorphic space is an explicit input, supplied by the relevant
Weierstrass theorem. -/
theorem exists_tendsto_of_holomorphic_bounded_on_compacts_of_isClosed_of_unique
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens E}
    (hclosed : IsClosed (holomorphicSubmodule (F := F) U : Set C(U, F)))
    (f : ℕ → HolomorphicMap U F)
    (hb : ∀ K ⊆ (U : Set E), IsCompact K → ∃ M : ℝ,
      ∀ n, ∀ z ∈ K, ‖openExtension U (f n).val z‖ ≤ M)
    {V : Set E} (hVU : V ⊆ U)
    (hunique : ∀ p q : HolomorphicMap U F,
      EqOn (openExtension U p.val) (openExtension U q.val) V → p = q)
    (hp : ∀ z ∈ V, ∃ y : F,
      Tendsto (fun n ↦ openExtension U (f n).val z) atTop (𝓝 y)) :
    ∃ g : HolomorphicMap U F, Tendsto f atTop (𝓝 g) := by
  have hc : IsCompact (closure (range f)) :=
    isCompact_closure_of_holomorphic_bounded_on_compacts_of_isClosed hclosed (by
      intro K hKU hK
      obtain ⟨M, hM⟩ := hb K hKU hK
      exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩)
  have hm : ∀ᶠ n in atTop, f n ∈ closure (range f) :=
    .of_forall fun n ↦ subset_closure (mem_range_self n)
  obtain ⟨g, _, hg⟩ := hc.exists_mapClusterPt_of_frequently hm.frequently
  refine ⟨g, hc.tendsto_nhds_of_unique_mapClusterPt hm ?_⟩
  intro q _ hq
  have hvalue : ∀ (r : HolomorphicMap U F), MapClusterPt r atTop f →
      ∀ z ∈ V, ∀ y : F,
      Tendsto (fun n ↦ openExtension U (f n).val z) atTop (𝓝 y) →
      openExtension U r.val z = y := by
    intro r hr z hz y hy
    have he := hr.continuousAt_comp
      (continuous_holomorphicMap_eval U ⟨z, hVU hz⟩).continuousAt
    obtain ⟨φ, hφ, hlim⟩ := he.tendsto_subseq
    have hy' : Tendsto (fun n ↦ (f n).val ⟨z, hVU hz⟩) atTop (𝓝 y) := by
      simpa only [openExtension_apply U _ (hVU hz)] using hy
    simpa only [openExtension_apply U _ (hVU hz)] using
      tendsto_nhds_unique hlim (hy'.comp hφ.tendsto_atTop)
  apply hunique q g
  intro z hz
  obtain ⟨y, hy⟩ := hp z hz
  exact (hvalue q hq z hz y hy).trans (hvalue g hg z hz y hy).symm

/-- The sequential Montel conclusion for compact-locally bounded holomorphic maps, with
closedness supplied by a Weierstrass theorem. -/
theorem exists_subseq_tendsto_of_holomorphic_bounded_on_compacts_of_isClosed
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens E}
    (hclosed : IsClosed (holomorphicSubmodule (F := F) U : Set C(U, F)))
    (f : ℕ → HolomorphicMap U F)
    (hb : ∀ K ⊆ (U : Set E), IsCompact K → ∃ M : ℝ,
      ∀ n, ∀ z ∈ K, ‖openExtension U (f n).val z‖ ≤ M) :
    ∃ (g : HolomorphicMap U F) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (f ∘ φ) atTop (𝓝 g) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  have : (uniformity C(U, F)).IsCountablyGenerated := inferInstance
  have : (uniformity (HolomorphicMap U F)).IsCountablyGenerated :=
    Filter.comap.isCountablyGenerated _ _
  have hc : IsCompact (closure (range f)) :=
    isCompact_closure_of_holomorphic_bounded_on_compacts_of_isClosed hclosed (by
      intro K hKU hK
      obtain ⟨M, hM⟩ := hb K hKU hK
      exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩)
  have hm : ∀ᶠ n in atTop, f n ∈ closure (range f) :=
    .of_forall fun n ↦ subset_closure (mem_range_self n)
  obtain ⟨g, _, hg⟩ := hc.exists_mapClusterPt_of_frequently hm.frequently
  obtain ⟨φ, hφ, hlim⟩ := hg.tendsto_subseq
  exact ⟨g, φ, hφ, hlim⟩

end Complex

end
