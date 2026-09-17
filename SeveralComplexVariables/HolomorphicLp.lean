/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.LocallyUniform
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Holomorphic Lp spaces

The holomorphic Lp space on an open subset of `ι → ℂ` is the submodule of Lebesgue
Lp classes admitting a holomorphic representative. Such a representative is unique on
the open set. Complex Banach targets and empty coordinate types are allowed.

Jakóbczak–Jarnicki, Lemma 1.4.20 and Corollary 1.4.21, motivate the local Lp estimate
and completeness for `1 ≤ p < ∞`. The local estimate is an explicitly pending proof.
Closedness and completeness below depend on that estimate. For Hilbert targets, the
space at `p = 2` inherits Mathlib's L2 inner product, with its convention of linearity
in the second argument. No boundedness or connectedness of the open set is required.
-/

public section

open Filter Set MeasureTheory
open scoped Classical ENNReal Topology

namespace SeveralComplexVariables

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Lp classes which have a holomorphic representative on the open set. -/
def holomorphicLpSubmodule (U : TopologicalSpace.Opens (ι → ℂ)) (p : ℝ≥0∞) :
    Submodule ℂ (Lp F p (volume.restrict (U : Set (ι → ℂ)))) where
  carrier := {u | ∃ f : (ι → ℂ) → F, DifferentiableOn ℂ f U ∧
    f =ᵐ[volume.restrict (U : Set (ι → ℂ))] u}
  zero_mem' := ⟨0, differentiableOn_const 0, (Lp.coeFn_zero F p _).symm⟩
  add_mem' := by
    rintro u v ⟨f, hf, he⟩ ⟨g, hg, he'⟩
    exact ⟨f + g, hf.add hg, (he.add he').trans (Lp.coeFn_add u v).symm⟩
  smul_mem' := by
    rintro c u ⟨f, hf, he⟩
    exact ⟨c • f, hf.const_smul c, (he.const_smul c).trans (Lp.coeFn_smul c u).symm⟩

/-- Holomorphic Lp functions, represented as a subspace of Mathlib's Lebesgue Lp space.
For `1 ≤ p` the norm and complex normed-space structure are inherited from Lp. -/
abbrev HolomorphicLp (U : TopologicalSpace.Opens (ι → ℂ)) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℂ F] (p : ℝ≥0∞) :=
  ↥(holomorphicLpSubmodule (F := F) U p)

/-- Every element of the holomorphic Lp subspace has a holomorphic representative. -/
theorem HolomorphicLp.exists_representative {U : TopologicalSpace.Opens (ι → ℂ)}
    {p : ℝ≥0∞} (u : HolomorphicLp U F p) :
    ∃ f : (ι → ℂ) → F, DifferentiableOn ℂ f U ∧
      f =ᵐ[volume.restrict (U : Set (ι → ℂ))] (u.val : Lp F p _) := u.property

/-- Holomorphic representatives of the same Lp class agree everywhere on the open set. -/
theorem holomorphicLp_representative_unique {U : TopologicalSpace.Opens (ι → ℂ)}
    {p : ℝ≥0∞} {u : Lp F p (volume.restrict (U : Set (ι → ℂ)))}
    {f g : (ι → ℂ) → F} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (he : f =ᵐ[volume.restrict (U : Set (ι → ℂ))] u)
    (he' : g =ᵐ[volume.restrict (U : Set (ι → ℂ))] u) : EqOn f g U :=
  Measure.eqOn_open_of_ae_eq (he.trans he'.symm) U.isOpen hf.continuousOn hg.continuousOn

variable [CompleteSpace F]

/-- **Local Lp estimate (Jakóbczak–Jarnicki 1.4.20).** On each compact subset of an
open set, values of a holomorphic representative are bounded by a fixed multiple of
the norm of its Lp class. The proof by polydisc mean values and Hölder is pending. -/
theorem exists_norm_le_mul_Lp_norm (U : TopologicalSpace.Opens (ι → ℂ))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {K : Set (ι → ℂ)} (hKU : K ⊆ U) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Lp F p (volume.restrict (U : Set (ι → ℂ))))
      (f : (ι → ℂ) → F), DifferentiableOn ℂ f U →
      f =ᵐ[volume.restrict (U : Set (ι → ℂ))] u →
      ∀ z ∈ K, ‖f z‖ ≤ C * ‖u‖ := by
  sorry

/-- An Lp-convergent sequence of holomorphic representatives converges locally uniformly
on the open set to a holomorphic representative of its Lp limit. This uses the local
Lp estimate; in particular, no global finite-measure hypothesis is needed. -/
theorem exists_holomorphic_representative_of_tendsto_Lp
    {U : TopologicalSpace.Opens (ι → ℂ)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {u : ℕ → Lp F p (volume.restrict (U : Set (ι → ℂ)))}
    {v : Lp F p (volume.restrict (U : Set (ι → ℂ)))}
    {f : ℕ → (ι → ℂ) → F} (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (he : ∀ n, f n =ᵐ[volume.restrict (U : Set (ι → ℂ))] u n)
    (hu : Tendsto u atTop (𝓝 v)) :
    ∃ g : (ι → ℂ) → F, DifferentiableOn ℂ g U ∧
      g =ᵐ[volume.restrict (U : Set (ι → ℂ))] v ∧
      TendstoLocallyUniformlyOn f g atTop U := by
  have hc : ∀ K ⊆ (U : Set (ι → ℂ)), IsCompact K → UniformCauchySeqOn f atTop K := by
    intro K hKU hK
    obtain ⟨C, hC, hbound⟩ := exists_norm_le_mul_Lp_norm (F := F) U p hp hKU hK
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu.cauchySeq (ε / C) (div_pos hε hC)
    refine ⟨N, fun m hm n hn z hz => ?_⟩
    have hb := hbound (u m - u n) (f m - f n) ((hf m).sub (hf n))
      (((he m).sub (he n)).trans (Lp.coeFn_sub _ _).symm) z hz
    rw [dist_eq_norm]
    have hdist := hN m hm n hn
    rw [dist_eq_norm] at hdist
    exact hb.trans_lt ((lt_div_iff₀' hC).mp hdist)
  have hex : ∀ z : U, ∃ y : F, Tendsto (fun n => f n z) atTop (𝓝 y) := by
    intro z
    exact cauchySeq_tendsto_of_complete
      ((hc {z.val} (singleton_subset_iff.mpr z.property) isCompact_singleton).cauchySeq
        (mem_singleton z.val))
  choose g hg using hex
  let G : (ι → ℂ) → F := fun z => if hz : z ∈ U then g ⟨z, hz⟩ else 0
  have hG : ∀ z ∈ U, Tendsto (fun n => f n z) atTop (𝓝 (G z)) := by
    intro z hz
    simpa only [G, dite_eq_left hz] using hg ⟨z, hz⟩
  have hloc : TendstoLocallyUniformlyOn f G atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact U.isOpen]
    intro K hKU hK
    exact (hc K hKU hK).tendstoUniformlyOn_of_tendsto fun z hz => hG z (hKU hz)
  refine ⟨G, (hloc.analyticOnNhd_pi
    (.of_forall fun n => (hf n).analyticOnNhd_finiteDimensional U.isOpen)
    U.isOpen).differentiableOn, ?_, hloc⟩
  obtain ⟨φ, hφ, hv⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  filter_upwards [hv, ae_all_iff.mpr he, ae_restrict_mem U.isOpen.measurableSet] with z hz hez hzU
  have ht : Tendsto (fun n => u (φ n) z) atTop (𝓝 (G z)) := by
    simpa only [Function.comp_def, ← hez] using (hG z hzU).comp hφ.tendsto_atTop
  exact tendsto_nhds_unique ht hz

/-- The holomorphic Lp submodule is closed for `1 ≤ p < ∞`, by the local Lp estimate
and Weierstrass convergence. -/
theorem isClosed_holomorphicLpSubmodule (U : TopologicalSpace.Opens (ι → ℂ))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    IsClosed (holomorphicLpSubmodule (F := F) U p : Set (Lp F p
      (volume.restrict (U : Set (ι → ℂ))))) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu hv
  choose f hf he using hu
  obtain ⟨g, hg, heq, _⟩ := exists_holomorphic_representative_of_tendsto_Lp hp hf he hv
  exact ⟨g, hg, heq⟩

/-- **Jakóbczak–Jarnicki 1.4.21.** Holomorphic Lp is a complex Banach space for
`1 ≤ p < ∞`. Completeness follows from closedness in Mathlib's complete Lp space. -/
instance (U : TopologicalSpace.Opens (ι → ℂ)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (p ≠ ∞)] : CompleteSpace (HolomorphicLp U F p) :=
  (isClosed_holomorphicLpSubmodule (F := F) U p (Fact.out : p ≠ ∞)).isComplete.completeSpace_coe

/-- Holomorphic L2 is complete, in particular without requiring callers to supply
an explicit proof that the exponent `2` is finite. -/
instance holomorphicL2CompleteSpace (U : TopologicalSpace.Opens (ι → ℂ)) :
    CompleteSpace (HolomorphicLp U F 2) :=
  (isClosed_holomorphicLpSubmodule (F := F) U 2 (by norm_num)).isComplete.completeSpace_coe

/-- Holomorphic L2 inherits the integral inner product of Mathlib's L2 space.
Together with completeness this gives Corollary 1.4.21's Hilbert-space assertion,
including Hilbert-valued functions and Mathlib's linear-in-the-second-argument convention. -/
theorem holomorphicL2_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {U : TopologicalSpace.Opens (ι → ℂ)} (f g : HolomorphicLp U H 2) :
    inner ℂ f g = ∫ z, inner ℂ (f.val z) (g.val z)
      ∂volume.restrict (U : Set (ι → ℂ)) :=
  L2.inner_def f.val g.val

end SeveralComplexVariables
