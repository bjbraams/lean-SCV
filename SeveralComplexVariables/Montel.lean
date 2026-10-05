/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Holomorphic.NormalFamily
public import SeveralComplexVariables.FunctionSpace
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import SeveralComplexVariables.IdentityPrinciple

/-!
# Montel's and Vitali's theorems

A family of holomorphic maps which is bounded uniformly on each compact subset of its domain is
equicontinuous. For finite-dimensional targets it has compact closure in the compact-open
topology. Compactness is supplied by Mathlib's Arzelà–Ascoli theorem. For compact-locally bounded
sequences, a subsequence theorem is also provided on arbitrary finite-dimensional complex source
spaces. Vitali's theorem holds for Banach targets: testing against norming functionals reduces
uniform Cauchy convergence on compact sets to scalar Montel and the identity theorem.

The compactness and uniqueness-set arguments are shared with one-variable analysis in
`ToMathlib.Analysis.Holomorphic.NormalFamily`. The results here supply several-variable
closedness and the identity theorem.

## Main results

`equicontinuous_of_holomorphic_bounded_on_compacts` is equicontinuity of a family bounded on compact
sets. `isCompact_closure_of_holomorphic_bounded_on_compacts` is Montel's theorem for
finite-dimensional targets. `exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto` is Vitali
convergence from pointwise convergence on a nonempty open subset, for Banach-valued maps.

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

omit [CompleteSpace F] in
/-- **Montel's theorem.** A compact-locally bounded family of holomorphic maps into a
finite-dimensional complex normed space has compact closure in the compact-open topology. -/
theorem isCompact_closure_of_holomorphic_bounded_on_compacts
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens E}
    {S : Set (HolomorphicMap U F)}
    (hb : ∀ K ⊆ (U : Set E), IsCompact K → ∃ M : ℝ,
      ∀ f ∈ S, ∀ z ∈ K, ‖openExtension U f.val z‖ ≤ M) : IsCompact (closure S) :=
  Complex.isCompact_closure_of_holomorphic_bounded_on_compacts_of_isClosed
    (isClosed_holomorphicSubmodule U) hb

omit [CompleteSpace F] in
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

omit [CompleteSpace F] in
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

omit [CompleteSpace F] in
/-- The key step of Vitali's theorem for Banach targets: a compact-locally bounded holomorphic
sequence converging pointwise on a nonempty open subset of a preconnected domain is uniformly
Cauchy on every compact subset. A violating pair at each stage is tested against a norming
functional (Hahn–Banach); scalar Montel gives a locally uniformly convergent subsequence of the
resulting scalar differences, whose limit vanishes on the open subset and hence, by the identity
theorem, everywhere. Completeness of the target is not needed for this step. -/
private theorem uniformCauchySeqOn_of_bounded_of_tendsto
    {D V K : Set E} (hD : IsOpen D) (hconn : IsPreconnected D) {f : ℕ → E → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) D)
    (hb : ∀ K ⊆ D, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hV : IsOpen V) (hne : V.Nonempty) (hVD : V ⊆ D)
    (hp : ∀ z ∈ V, ∃ y : F, Tendsto (fun n => f n z) atTop (𝓝 y))
    (hK : IsCompact K) (hKD : K ⊆ D) : UniformCauchySeqOn f atTop K := by
  rw [Metric.uniformCauchySeqOn_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, hbad⟩ := hcon
  choose m hm n hn x hx hdist using hbad
  have hdist' : ∀ N, ε ≤ ‖f (m N) (x N) - f (n N) (x N)‖ := fun N => by
    simpa only [dist_eq_norm] using hdist N
  choose φ hφn hφ using fun N =>
    exists_dual_vector ℂ (f (m N) (x N) - f (n N) (x N)) (hε.trans_le (hdist' N)).ne'
  let h : ℕ → E → ℂ := fun N z => φ N (f (m N) z - f (n N) z)
  have hle : ∀ N z, ‖h N z‖ ≤ ‖f (m N) z - f (n N) z‖ := fun N z => by
    simpa only [hφn, one_mul] using (φ N).le_opNorm (f (m N) z - f (n N) z)
  have hh : ∀ N, AnalyticOnNhd ℂ (h N) D := fun N =>
    ((φ N).differentiable.comp_differentiableOn
      ((hf (m N)).sub (hf (n N)))).analyticOnNhd_of_finiteDimensional hD
  have hhb : ∀ L ⊆ D, IsCompact L → ∃ M : ℝ, ∀ N, ∀ z ∈ L, ‖h N z‖ ≤ M := by
    intro L hLD hL
    obtain ⟨M, hM⟩ := hb L hLD hL
    exact ⟨M + M, fun N z hz => (hle N z).trans
      ((norm_sub_le _ _).trans (add_le_add (hM _ z hz) (hM _ z hz)))⟩
  obtain ⟨g, ψ, hψ, hg, hlim⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn_of_bounded_on_compacts hD hh hhb
  have hgV : EqOn g 0 V := by
    intro z hz
    obtain ⟨y, hy⟩ := hp z hz
    have hdz : Tendsto (fun N => ‖f (m N) z - f (n N) z‖) atTop (𝓝 0) := by
      simpa using ((hy.comp (tendsto_atTop_mono hm tendsto_id)).sub
        (hy.comp (tendsto_atTop_mono hn tendsto_id))).norm
    exact tendsto_nhds_unique (hlim.tendsto_at (hVD hz))
      (squeeze_zero_norm (fun j => hle (ψ j) z) (hdz.comp hψ.tendsto_atTop))
  have hgD : EqOn g 0 D :=
    hg.differentiableOn.eqOn_zero_of_preconnected_of_eqOn_zero hD hconn hV hne hVD hgV
  obtain ⟨j, hj⟩ := (Metric.tendstoUniformlyOn_iff.mp
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mp hlim K hKD hK) ε hε).exists
  have hlt := hj (x (ψ j)) (hx (ψ j))
  rw [hgD (hKD (hx (ψ j))), Pi.zero_apply, dist_zero_left] at hlt
  have heq : ‖h (ψ j) (x (ψ j))‖ = ‖f (m (ψ j)) (x (ψ j)) - f (n (ψ j)) (x (ψ j))‖ := by
    simp only [h, hφ, RCLike.norm_ofReal, abs_norm]
  exact (hdist' (ψ j)).not_gt (heq ▸ hlt)

/-- **Vitali's theorem ([Jakóbczak–Jarnicki][JakobczakJarnicki2021] 1.4.24)** for holomorphic maps
on a finite-dimensional complex normed space with values in a complex Banach space. A
compact-locally bounded sequence converging pointwise on a nonempty open subset of a preconnected
domain converges locally uniformly on the whole domain, and the limit is holomorphic. Completeness
of the target supplies the limit of the uniformly Cauchy sequence. -/
theorem exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto
    {D V : Set E}
    (hD : IsOpen D) (hconn : IsPreconnected D) {f : ℕ → E → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) D)
    (hb : ∀ K ⊆ D, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hV : IsOpen V) (hne : V.Nonempty) (hVD : V ⊆ D)
    (hp : ∀ z ∈ V, ∃ y : F, Tendsto (fun n => f n z) atTop (𝓝 y)) :
    ∃ g : E → F, DifferentiableOn ℂ g D ∧
      TendstoLocallyUniformlyOn f g atTop D := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hC : ∀ K ⊆ D, IsCompact K → UniformCauchySeqOn f atTop K := fun K hKD hK =>
    uniformCauchySeqOn_of_bounded_of_tendsto hD hconn hf hb hV hne hVD hp hK hKD
  let g : E → F := fun z => limUnder atTop fun n => f n z
  have hlim : TendstoLocallyUniformlyOn f g atTop D :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mpr fun K hKD hK =>
      (hC K hKD hK).tendstoUniformlyOn_of_tendsto fun z hz =>
        ((hC {z} (singleton_subset_iff.mpr (hKD hz)) isCompact_singleton).cauchySeq
          (mem_singleton z)).tendsto_limUnder
  exact ⟨g, (hlim.analyticOnNhd_of_finiteDimensional (Eventually.of_forall fun n =>
    (hf n).analyticOnNhd_of_finiteDimensional hD) hD).differentiableOn, hlim⟩

/-- **Vitali's theorem** in the compact-open function space, with values in a complex Banach space.
A locally bounded sequence converging pointwise on a nonempty open subset of a
preconnected domain converges in the whole holomorphic-map space. -/
theorem exists_tendsto_of_holomorphic_bounded_on_compacts
    {U : TopologicalSpace.Opens E}
    (hconn : IsPreconnected (U : Set E)) (f : ℕ → HolomorphicMap U F)
    (hb : ∀ K ⊆ (U : Set E), IsCompact K → ∃ M : ℝ,
      ∀ n, ∀ z ∈ K, ‖openExtension U (f n).val z‖ ≤ M)
    {V : Set E} (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U)
    (hp : ∀ z ∈ V, ∃ y : F,
      Tendsto (fun n => openExtension U (f n).val z) atTop (𝓝 y)) :
    ∃ g : HolomorphicMap U F, Tendsto f atTop (𝓝 g) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨g, hg, hlim⟩ := exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto U.isOpen hconn
    (fun n => (f n).property.differentiableOn) hb hV hne hVU hp
  let G : HolomorphicMap U F := ⟨⟨fun z => g z, hg.continuousOn.domRestrict⟩, by
    apply AnalyticOnNhd.congr U.isOpen (hg.analyticOnNhd_of_finiteDimensional U.isOpen)
    intro z hz
    rw [openExtension_apply U _ hz]
    rfl⟩
  exact ⟨G, holomorphicMap_tendsto_iff.mpr (hlim.congr_right fun z hz => by
    rw [openExtension_apply U _ hz]
    rfl)⟩

end SeveralComplexVariables

end
