/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Holomorphic.NormalFamily
public import SeveralComplexVariables.FunctionSpace
public import SeveralComplexVariables.IdentityPrinciple

/-!
# Montel's and Vitali's theorems

A family of holomorphic maps which is bounded uniformly on each compact subset of its domain is
equicontinuous. For finite-dimensional targets it has compact closure in the compact-open
topology. Compactness is supplied by Mathlib's Arzelà–Ascoli theorem. For compact-locally bounded
sequences, a subsequence theorem is also provided on arbitrary finite-dimensional complex source
spaces. Vitali convergence follows from compactness and the identity theorem: pointwise
convergence on a nonempty open subset determines every cluster limit uniquely.

The compactness and uniqueness-set arguments are shared with one-variable analysis in
`Analysis.Holomorphic.NormalFamily`. The results here supply several-variable closedness
and the identity theorem.

## Main results

`equicontinuous_of_holomorphic_bounded_on_compacts` is equicontinuity of a family bounded on compact
sets. `isCompact_closure_of_holomorphic_bounded_on_compacts` is Montel's theorem for
finite-dimensional targets. `exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto` is Vitali
convergence from pointwise convergence on a nonempty open subset.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public section

open Complex Filter Function Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

export Complex (equicontinuous_of_holomorphic_bounded_on_compacts)

/-- **Montel's theorem.** A compact-locally bounded family of holomorphic maps into a
finite-dimensional complex normed space has compact closure in the compact-open topology. -/
theorem isCompact_closure_of_holomorphic_bounded_on_compacts
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens E}
    {S : Set (HolomorphicMap U F)}
    (hb : ∀ K ⊆ (U : Set E), IsCompact K → ∃ M : ℝ,
      ∀ f ∈ S, ∀ z ∈ K, ‖openExtension U f.val z‖ ≤ M) : IsCompact (closure S) :=
  Complex.isCompact_closure_of_holomorphic_bounded_on_compacts_of_isClosed
    (isClosed_holomorphicSubmodule U) hb

/-- **Vitali's theorem ([Jakóbczak–Jarnicki][JakobczakJarnicki2021] 1.4.24)** in the compact-open
function space.
A locally bounded sequence converging pointwise on a nonempty open subset of a
preconnected domain converges in the whole holomorphic-map space. -/
theorem exists_tendsto_of_holomorphic_bounded_on_compacts
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens E}
    (hconn : IsPreconnected (U : Set E)) (f : ℕ → HolomorphicMap U F)
    (hb : ∀ K ⊆ (U : Set E), IsCompact K → ∃ M : ℝ,
      ∀ n, ∀ z ∈ K, ‖openExtension U (f n).val z‖ ≤ M)
    {V : Set E} (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U)
    (hp : ∀ z ∈ V, ∃ y : F,
      Tendsto (fun n => openExtension U (f n).val z) atTop (𝓝 y)) :
    ∃ g : HolomorphicMap U F, Tendsto f atTop (𝓝 g) := by
  apply Complex.exists_tendsto_of_holomorphic_bounded_on_compacts_of_isClosed_of_unique
    (isClosed_holomorphicSubmodule U) f hb hVU _ hp
  intro p q he
  have heq := DifferentiableOn.eqOn_of_preconnected_of_eqOn U.isOpen hconn
    p.property.differentiableOn q.property.differentiableOn hV hne hVU he
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  simpa only [openExtension_coe] using heq z.property

/-- **Vitali's theorem** for holomorphic functions on a finite-dimensional complex normed space.
The limit is holomorphic and convergence is locally uniform on the whole domain.
Finite-dimensional complex targets, including scalar-valued functions, are allowed. -/
theorem exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto [FiniteDimensional ℂ F]
    {D V : Set E}
    (hD : IsOpen D) (hconn : IsPreconnected D) {f : ℕ → E → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) D)
    (hb : ∀ K ⊆ D, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hV : IsOpen V) (hne : V.Nonempty) (hVD : V ⊆ D)
    (hp : ∀ z ∈ V, ∃ y : F, Tendsto (fun n => f n z) atTop (𝓝 y)) :
    ∃ g : E → F, DifferentiableOn ℂ g D ∧
      TendstoLocallyUniformlyOn f g atTop D := by
  let U : TopologicalSpace.Opens E := ⟨D, hD⟩
  let s : ℕ → HolomorphicMap U F := fun n =>
    ⟨⟨fun z => f n z, (hf n).continuousOn.domRestrict⟩,
      by
        apply AnalyticOnNhd.congr hD ((hf n).analyticOnNhd_of_finiteDimensional hD)
        intro z hz
        simp [openExtension, U, hz]
        rfl⟩
  have hs : ∀ n, ∀ z ∈ D, openExtension U (s n).val z = f n z := by
    intro n z hz
    exact openExtension_apply U _ hz
  obtain ⟨g, hg⟩ := exists_tendsto_of_holomorphic_bounded_on_compacts hconn s
    (by
      intro K hKD hK
      obtain ⟨M, hM⟩ := hb K hKD hK
      refine ⟨M, fun n z hz => ?_⟩
      rw [hs n z (hKD hz)]
      exact hM n z hz) hV hne hVD (by
      intro z hz
      simpa only [hs _ z (hVD hz)] using hp z hz)
  refine ⟨openExtension U g.val, g.property.differentiableOn, ?_⟩
  exact (holomorphicMap_tendsto_iff.mp hg).congr
    (fun n z hz => hs n z hz)

/-- Sequential Montel for a compact-locally bounded family on a finite-dimensional complex
source space. The proof uses the shared compactness theorem without a coordinate change. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_bounded_on_compacts
    [FiniteDimensional ℂ F] {U : Set E} (hU : IsOpen U) {f : ℕ → E → F}
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∃ (g : E → F) (φ : ℕ → ℕ), StrictMono φ ∧ AnalyticOnNhd ℂ g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U := by
  let V : TopologicalSpace.Opens E := ⟨U, hU⟩
  let s (n : ℕ) := Complex.holomorphicMapOfAnalyticOnNhd V (f n) (hf n)
  obtain ⟨g, φ, hφ, hlim⟩ :=
    Complex.exists_subseq_tendsto_of_holomorphic_bounded_on_compacts_of_isClosed
      (isClosed_holomorphicSubmodule V) s (by
        intro K hKU hK
        obtain ⟨M, hM⟩ := hb K hKU hK
        refine ⟨M, fun n z hz => ?_⟩
        rw [openExtension_apply V _ (hKU hz)]
        exact hM n z hz)
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  refine ⟨openExtension V g.val, φ, hφ, g.property, ?_⟩
  exact (holomorphicMap_tendsto_iff.mp hlim).congr (fun n z hz => by
    rw [openExtension_apply V _ hz]; rfl)

/-- A uniformly bounded holomorphic sequence on a finite-dimensional complex space has a locally
uniformly convergent subsequence, with holomorphic limit. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] {U : Set E} (hU : IsOpen U) {f : ℕ → E → F}
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) {M : ℝ}
    (hM : ∀ n z, z ∈ U → ‖f n z‖ ≤ M) :
    ∃ (g : E → F) (φ : ℕ → ℕ), StrictMono φ ∧ AnalyticOnNhd ℂ g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U :=
  exists_subseq_tendstoLocallyUniformlyOn_of_bounded_on_compacts hU hf
    (fun _ hKU _ => ⟨M, fun n z hz => hM n z (hKU hz)⟩)

end SeveralComplexVariables

end
