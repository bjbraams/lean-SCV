/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.Ascoli
public import ToMathlib.Analysis.Holomorphic.LocallyUniformLimit

/-!
# Montel and Vitali theorems

For the one-variable scalar case, we acknowledge Vincent Beffara's
[RMT4 formalization](https://github.com/vbeffara/RMT4), in particular
[RMT4/Montel.lean](https://github.com/vbeffara/RMT4/blob/main/RMT4/Montel.lean).
Related work includes Yury Kudryashov's Riemann mapping theorem development in
[Mathlib PR #33505](https://github.com/leanprover-community/mathlib4/pull/33505)
and TauCeti's normal-family, Montel, and Vitali developments linked below.
Our code will be reviewed upon the anticipated adoption of that PR. These developments
have substantial mathematical overlap; the bundled-map interface and the general-source
conditional and finite-dimensional-vector-valued results require separate comparison.

Compact-local bounds imply equicontinuity by the complex Schwarz estimate. Arzelà–Ascoli
then gives compactness, and convergence on a uniqueness set gives Vitali convergence.
For domains in `ℂ`, closedness follows from the Weierstrass theorem, so the main entry
points need only compact-local bounds and, for Vitali convergence, uniqueness or an
accumulation point. Their statements use values on the domain directly.

The general finite-dimensional source versions retain explicit closedness and uniqueness
hypotheses for use by several-variable developments. Targets must be finite-dimensional
for the bounded-family compactness conclusions; equicontinuity allows arbitrary complex
normed targets.

## Main results

* `Complex.isCompact_closure_of_holomorphic_bounded_on_compacts`: **Montel's theorem**
  for open subsets of `ℂ`, with finite-dimensional targets.
* `Complex.exists_subseq_tendsto_of_holomorphic_bounded_on_compacts`: sequential Montel.
* `Complex.exists_tendsto_of_holomorphic_bounded_on_compacts_of_unique`: Vitali convergence
  from pointwise convergence on a uniqueness set.
* `Complex.exists_tendsto_of_holomorphic_bounded_on_compacts_of_mem_closure`: **Vitali's
  theorem** on a preconnected domain, with an accumulation point inside the domain.
* `Complex.equicontinuous_of_holomorphic_bounded_on_compacts`: equicontinuity for
  finite-dimensional sources and arbitrary complex normed targets.

The variants with `_of_isClosed` take closedness as an explicit hypothesis and allow
arbitrary finite-dimensional complex source spaces.

## References

* [TauCeti normal-family bounds](https://github.com/TauCetiProject/TauCeti/blob/680bd1855971ac82971b9d18f2f85914d62270de/TauCeti/Analysis/Complex/Conformal/NormalFamilies.lean).
* [TauCeti compact-open precompactness](https://github.com/TauCetiProject/TauCeti/blob/680bd1855971ac82971b9d18f2f85914d62270de/TauCeti/Analysis/Complex/Conformal/Montel/Precompact.lean).
* [TauCeti Montel selection](https://github.com/TauCetiProject/TauCeti/blob/680bd1855971ac82971b9d18f2f85914d62270de/TauCeti/Analysis/Complex/Conformal/Montel/Basic.lean).
* [TauCeti Vitali convergence](https://github.com/TauCetiProject/TauCeti/blob/680bd1855971ac82971b9d18f2f85914d62270de/TauCeti/Analysis/Complex/Conformal/Vitali.lean).
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

For the one-variable scalar case, see Vincent Beffara's RMT4 formalization, linked above. -/
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

omit [FiniteDimensional ℂ E] [CompleteSpace F] in
/-- Bounds on compact subsets of the domain give the corresponding bounds for ambient
extensions on compact sets contained in the domain. -/
private theorem bounded_on_compacts_openExtension {U : TopologicalSpace.Opens E}
    {S : Set (HolomorphicMap U F)}
    (hb : ∀ K : Set U, IsCompact K → ∃ M : ℝ, ∀ f ∈ S, ∀ z ∈ K, ‖f z‖ ≤ M) :
    ∀ K ⊆ (U : Set E), IsCompact K → ∃ M : ℝ,
      ∀ f ∈ S, ∀ z ∈ K, ‖openExtension U f.val z‖ ≤ M := by
  intro K hKU hK
  have hK' : IsCompact ((Subtype.val : U → E) ⁻¹' K) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKU)
  obtain ⟨M, hM⟩ := hb _ hK'
  refine ⟨M, fun f hf z hz ↦ ?_⟩
  simpa only [openExtension_apply U _ (hKU hz), HolomorphicMap.coe_val] using
    hM f hf ⟨z, hKU hz⟩ hz

/-- **Montel's theorem** on an open subset of the complex plane: a family of holomorphic
maps into a finite-dimensional space, bounded uniformly on every compact subset of the
domain, has compact closure for the compact-open topology. -/
theorem isCompact_closure_of_holomorphic_bounded_on_compacts
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens ℂ}
    {S : Set (HolomorphicMap U F)}
    (hb : ∀ K : Set U, IsCompact K → ∃ M : ℝ, ∀ f ∈ S, ∀ z ∈ K, ‖f z‖ ≤ M) :
    IsCompact (closure S) :=
  isCompact_closure_of_holomorphic_bounded_on_compacts_of_isClosed
    (isClosed_holomorphicSubmodule U) (bounded_on_compacts_openExtension hb)

/-- **Sequential Montel theorem** on an open subset of the complex plane: every sequence
bounded uniformly on compact subsets has a subsequence converging to a holomorphic map. -/
theorem exists_subseq_tendsto_of_holomorphic_bounded_on_compacts
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens ℂ}
    (f : ℕ → HolomorphicMap U F)
    (hb : ∀ K : Set U, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∃ (g : HolomorphicMap U F) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (f ∘ φ) atTop (𝓝 g) := by
  apply exists_subseq_tendsto_of_holomorphic_bounded_on_compacts_of_isClosed
    (isClosed_holomorphicSubmodule U) f
  have hb' := bounded_on_compacts_openExtension (S := range f) (by
    intro K hK
    obtain ⟨M, hM⟩ := hb K hK
    exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩)
  intro K hKU hK
  obtain ⟨M, hM⟩ := hb' K hKU hK
  exact ⟨M, fun n ↦ hM (f n) (mem_range_self n)⟩

/-- **Vitali convergence on a uniqueness set** in an open subset of the complex plane.
Compact-local bounds and pointwise convergence on a set determining holomorphic maps
uniquely imply convergence in the holomorphic-map space. -/
theorem exists_tendsto_of_holomorphic_bounded_on_compacts_of_unique
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens ℂ}
    (f : ℕ → HolomorphicMap U F)
    (hb : ∀ K : Set U, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    {V : Set U} (hunique : ∀ p q : HolomorphicMap U F, EqOn p q V → p = q)
    (hp : ∀ z ∈ V, ∃ y : F, Tendsto (fun n ↦ f n z) atTop (𝓝 y)) :
    ∃ g : HolomorphicMap U F, Tendsto f atTop (𝓝 g) := by
  have hb' := bounded_on_compacts_openExtension (S := range f) (by
    intro K hK
    obtain ⟨M, hM⟩ := hb K hK
    exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩)
  apply exists_tendsto_of_holomorphic_bounded_on_compacts_of_isClosed_of_unique
    (isClosed_holomorphicSubmodule U) f
    (fun K hKU hK ↦ by
      obtain ⟨M, hM⟩ := hb' K hKU hK
      exact ⟨M, fun n ↦ hM (f n) (mem_range_self n)⟩)
    (V := Subtype.val '' V) (by rintro _ ⟨z, _, rfl⟩; exact z.property)
  · intro p q he
    apply hunique p q
    intro z hz
    simpa using he (mem_image_of_mem Subtype.val hz)
  · rintro _ ⟨z, hz, rfl⟩
    simpa using hp z hz

/-- **Vitali's theorem** on a preconnected open subset of the complex plane. Pointwise
convergence on a set accumulating at a point inside the domain, together with uniform
bounds on compact subsets, implies convergence to a holomorphic map on the whole domain.
The accumulation hypothesis excludes the point itself. -/
theorem exists_tendsto_of_holomorphic_bounded_on_compacts_of_mem_closure
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens ℂ}
    (hconn : IsPreconnected (U : Set ℂ)) (f : ℕ → HolomorphicMap U F)
    (hb : ∀ K : Set U, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    {V : Set U} {z₀ : U} (hacc : (z₀ : ℂ) ∈ closure (Subtype.val '' V \ {(z₀ : ℂ)}))
    (hp : ∀ z ∈ V, ∃ y : F, Tendsto (fun n ↦ f n z) atTop (𝓝 y)) :
    ∃ g : HolomorphicMap U F, Tendsto f atTop (𝓝 g) := by
  apply exists_tendsto_of_holomorphic_bounded_on_compacts_of_unique f hb _ hp
  intro p q he
  have heq := p.property.eqOn_of_preconnected_of_mem_closure q.property hconn z₀.property
    (closure_mono (by
      rintro z ⟨⟨w, hw, rfl⟩, hne⟩
      exact ⟨by simpa using he hw, hne⟩) hacc)
  ext z
  simpa using heq z.property

end Complex

end
