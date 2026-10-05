/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Topology.Algebra.MvPolynomial
public import SeveralComplexVariables.Analyticity
public import Mathlib.Topology.Compactness.SigmaCompact
public import SeveralComplexVariables.HolomorphicConvexity.Thullen
public import SeveralComplexVariables.PolydiscTaylor

/-!
# Runge pairs, Runge domains and polynomial hulls

A pair of sets `U ⊆ V` is a Runge pair if every holomorphic function on `U` is a locally uniform
limit of holomorphic functions on `V`; an open subset of `ℂⁿ` is a Runge domain if every
holomorphic function on it is a locally uniform limit of polynomials. Both notions are stated
through approximation within `ε` on compact subsets, and for open sets this is shown equivalent
to convergence of a sequence locally uniformly.

The polynomial hull of a compact set is the set of points where every polynomial is bounded by
its supremum on the set; it agrees with the hull relative to all entire functions, because
entire functions are locally uniform limits of their Taylor polynomials. Consequently a set is a
Runge domain exactly when it forms a Runge pair with the whole space.

For a Runge domain `U`, the polynomial hull of a compact `K ⊆ U` meets `U` in the holomorphic
hull of `K` relative to `U`, and for a Runge domain of holomorphy this set is compact. These are
the elementary implications of the hull characterization of Runge domains
([Hörmander][Hormander1973], Theorem 2.7.3; [Jakóbczak–Jarnicki][JakobczakJarnicki2021], Theorem
4.3.3). The converse implications constitute the Oka–Weil theorem and are not included.

References: [Hörmander][Hormander1973] (1973), Section 2.7;
[Jakóbczak–Jarnicki][JakobczakJarnicki2021] (2021), Section 4.3;
[Korevaar–Wiegerinck][KorevaarWiegerinck2017] (2017), Section 1.7.

## Main definitions

* `polynomialHull`: The polynomial hull of a set: the points at which every polynomial is bounded by
  each of its bounds on the set.
* `IsPolynomiallyConvex`: A set is polynomially convex if it equals its polynomial hull.
* `IsRungePair`: A **Runge pair**: `U ⊆ V`, and every holomorphic function on `U` is approximated
  within `ε` on every compact subset of `U` by a holomorphic function on `V`.
* `IsRungeDomain`: A **Runge domain** in `ℂ^ι`: every holomorphic function is approximated within `ε`
  on every compact subset by a polynomial.

## Main results

* `exists_mvPolynomial_approx_of_entire`: **Entire functions are locally uniform limits of
  polynomials.** On a compact set, an entire function is approximated within `ε` by a Taylor
  polynomial.
* `polynomialHull_eq_holomorphicHull_univ`: **Polynomial and entire hulls agree** on compact sets,
  since entire functions are locally uniform limits of polynomials.
* `IsRungeDomain.polynomialHull_inter`: **Hull identity for Runge domains.** For a Runge domain `U`
  and a compact `K ⊆ U`, the polynomial hull of `K` meets `U` exactly in the holomorphic hull of `K`
  relative to `U`.
* `IsRungePair.exists_seq_tendstoLocallyUniformlyOn`: **Sequence formulation.** For an open `U`, a
  Runge pair provides, for each holomorphic function on `U`, a sequence of holomorphic functions on
  `V` converging locally uniformly.

## References

* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
-/

public noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace SeveralComplexVariables

section Polynomials

variable {ι : Type*} [Fintype ι]

/-- A finite sum of monomials with complex coefficients, indexed by finitely supported
multi-indices, is the evaluation of a polynomial. -/
theorem exists_mvPolynomial_eval_eq_sum (s : Finset (ι →₀ ℕ)) (c : (ι →₀ ℕ) → ℂ) :
    ∃ P : MvPolynomial ι ℂ, ∀ z : ι → ℂ,
      MvPolynomial.eval z P = ∑ m ∈ s, (∏ i, z i ^ m i) * c m := by
  refine ⟨∑ m ∈ s, MvPolynomial.C (c m) * ∏ i, MvPolynomial.X i ^ (m i), fun z => ?_⟩
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, map_pow, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- A finite sum of monomials with complex coefficients, indexed by functions `ι → ℕ`, is the
evaluation of a polynomial. -/
theorem exists_mvPolynomial_eval_eq_sum' (s : Finset (ι → ℕ)) (c : (ι → ℕ) → ℂ) :
    ∃ P : MvPolynomial ι ℂ, ∀ z : ι → ℂ,
      MvPolynomial.eval z P = ∑ m ∈ s, (∏ i, z i ^ m i) * c m := by
  refine ⟨∑ m ∈ s, MvPolynomial.C (c m) * ∏ i, MvPolynomial.X i ^ (m i), fun z => ?_⟩
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, map_pow, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- Entire functions on `ℂ^{Fin n}` are approximated on compact sets by Taylor polynomials of the
polydisc expansion. -/
private theorem exists_mvPolynomial_approx_of_entire_fin {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g univ) {K : Set (Fin n → ℂ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ z ∈ K, ‖g z - MvPolynomial.eval z P‖ < ε := by
  obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall 0
  set R : Fin n → ℝ := fun _ => max B 0 + 1 with hRdef
  have hR : ∀ i, 0 < R i := fun _ => by positivity
  set s : Fin n → ℝ := fun _ => max B 0 with hsdef
  have hs : ∀ i, 0 ≤ s i := fun _ => le_max_right _ _
  have hsR : ∀ i, s i < R i := fun _ => by simp [hsdef, hRdef]
  have hKs : K ⊆ closedPolydisc 0 s := by
    intro z hz
    rw [mem_closedPolydisc]
    intro i
    have h1 : ‖z i‖ ≤ ‖z‖ := norm_le_pi_norm z i
    have h2 : ‖z‖ ≤ B := mem_closedBall_zero_iff.mp (hB hz)
    rw [Pi.zero_apply, dist_zero_right]
    exact h1.trans (h2.trans (le_max_left _ _))
  have hcont : ContinuousOn g (closedPolydisc 0 R) := hg.continuousOn.mono (subset_univ _)
  have hslice : ∀ z ∈ closedPolydisc 0 R, ∀ i,
      AnalyticAt ℂ (fun v => g (update z i v)) (z i) :=
    fun z _ i => by convert hg.analyticAt_update (mem_univ z) i
  obtain ⟨M, hM⟩ := (isCompact_closedPolydisc 0 R).exists_bound_of_continuousOn hcont
  have hsum := hasSumUniformlyOn_polydiscTaylor hR hs hsR hcont hslice hM
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn, Metric.tendstoUniformlyOn_iff] at hsum
  obtain ⟨t, ht⟩ := (hsum ε hε).exists
  obtain ⟨P, hP⟩ := exists_mvPolynomial_eval_eq_sum' t
    (fun m => polydiscCauchyCoeffWithRadii g 0 R m)
  refine ⟨P, fun z hz => ?_⟩
  have := ht z (hKs hz)
  rw [dist_eq_norm, zero_add] at this
  rw [hP z]
  simpa only [smul_eq_mul] using this

/-- Reindexing the coordinates of `ℂ^κ` along an equivalence is analytic. -/
theorem analyticOnNhd_comp_equiv {κ : Type*} [Fintype κ] (e : ι ≃ κ) :
    AnalyticOnNhd ℂ (fun w : κ → ℂ => w ∘ e) univ := fun w _ =>
  analyticAt_pi_iff.mpr fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : κ => ℂ)
    (e i)).analyticAt w

/-- **Entire functions are locally uniform limits of polynomials.** On a compact set, an entire
function is approximated within `ε` by a Taylor polynomial. The coordinate index type is
reindexed by `Fin n` to apply the polydisc Taylor expansion. -/
theorem exists_mvPolynomial_approx_of_entire {g : (ι → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g univ) {K : Set (ι → ℂ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial ι ℂ, ∀ z ∈ K, ‖g z - MvPolynomial.eval z P‖ < ε := by
  let e := Fintype.equivFin ι
  have hK' : IsCompact ((fun z : ι → ℂ => z ∘ e.symm) '' K) :=
    hK.image (continuous_pi fun _ => continuous_apply _)
  obtain ⟨P, hP⟩ := exists_mvPolynomial_approx_of_entire_fin
    (hg.comp (analyticOnNhd_comp_equiv e) (mapsTo_univ _ _)) hK' hε
  refine ⟨MvPolynomial.rename e.symm P, fun z hz => ?_⟩
  have h := hP _ (mem_image_of_mem _ hz)
  have hz' : (z ∘ e.symm) ∘ e = z := by ext i; simp
  rw [MvPolynomial.eval_rename]
  simpa only [Function.comp_apply, hz'] using h

end Polynomials

section Hull

variable {ι σ : Type*} [Fintype ι]

/-- The polynomial hull of a set: the points at which every polynomial is bounded by each of its
bounds on the set. The variables may be indexed by any type. -/
@[expose] def polynomialHull (K : Set (σ → ℂ)) : Set (σ → ℂ) :=
  {z | ∀ P : MvPolynomial σ ℂ, ∀ M : ℝ,
    (∀ w ∈ K, ‖MvPolynomial.eval w P‖ ≤ M) → ‖MvPolynomial.eval z P‖ ≤ M}

/-- A set is polynomially convex if it equals its polynomial hull. -/
@[expose] def IsPolynomiallyConvex (K : Set (σ → ℂ)) : Prop := polynomialHull K = K

/-- A set lies in its polynomial hull. -/
theorem subset_polynomialHull (K : Set (σ → ℂ)) : K ⊆ polynomialHull K :=
  fun z hz _ _ hM => hM z hz

/-- The polynomial hull is monotone. -/
theorem polynomialHull_mono {K L : Set (σ → ℂ)} (h : K ⊆ L) :
    polynomialHull K ⊆ polynomialHull L :=
  fun _ hz P M hM => hz P M fun w hw => hM w (h hw)

/-- The polynomial hull is closed. -/
theorem isClosed_polynomialHull (K : Set (σ → ℂ)) : IsClosed (polynomialHull K) := by
  have : polynomialHull K = ⋂ P : MvPolynomial σ ℂ, ⋂ M : ℝ,
      ⋂ _ : (∀ w ∈ K, ‖MvPolynomial.eval w P‖ ≤ M), {z | ‖MvPolynomial.eval z P‖ ≤ M} := by
    ext z
    simp only [polynomialHull, mem_ofPred_eq, mem_iInter]
  rw [this]
  exact isClosed_iInter fun P => isClosed_iInter fun M => isClosed_iInter fun _ =>
    isClosed_le (P.continuous_eval).norm continuous_const

/-- The polynomial hull of a bounded set is bounded, by the coordinate polynomials. -/
theorem polynomialHull_subset_closedBall {K : Set (ι → ℂ)} {B : ℝ} (hB0 : 0 ≤ B)
    (hK : K ⊆ closedBall 0 B) : polynomialHull K ⊆ closedBall 0 B := by
  intro z hz
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hB0]
  intro i
  have := hz (MvPolynomial.X i) B fun w hw => by
    rw [MvPolynomial.eval_X]
    exact (norm_le_pi_norm w i).trans (mem_closedBall_zero_iff.mp (hK hw))
  rwa [MvPolynomial.eval_X] at this

/-- The polynomial hull of a compact set is compact. -/
theorem isCompact_polynomialHull {K : Set (ι → ℂ)} (hK : IsCompact K) :
    IsCompact (polynomialHull K) := by
  obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall 0
  have hB' : K ⊆ closedBall 0 (max B 0) :=
    hB.trans (closedBall_subset_closedBall (le_max_left _ _))
  exact isCompact_of_isClosed_isBounded (isClosed_polynomialHull K)
    (isBounded_closedBall.subset (polynomialHull_subset_closedBall (le_max_right _ _) hB'))

/-- **Polynomial and entire hulls agree** on compact sets, since entire functions are locally
uniform limits of polynomials. -/
theorem polynomialHull_eq_holomorphicHull_univ {K : Set (ι → ℂ)} (hK : IsCompact K) :
    polynomialHull K = holomorphicHull univ K := by
  ext z
  constructor
  · intro hz
    refine ⟨mem_univ z, fun f hf M hM => ?_⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨P, hP⟩ := exists_mvPolynomial_approx_of_entire hf (hK.insert z) (half_pos hε)
    have hPK : ∀ w ∈ K, ‖MvPolynomial.eval w P‖ ≤ M + ε / 2 := fun w hw => by
      have h1 := hP w (mem_insert_of_mem z hw)
      have h2 := hM w hw
      calc ‖MvPolynomial.eval w P‖ = ‖f w - (f w - MvPolynomial.eval w P)‖ := by ring_nf
        _ ≤ ‖f w‖ + ‖f w - MvPolynomial.eval w P‖ := norm_sub_le _ _
        _ ≤ M + ε / 2 := by linarith
    have hz' := hz P (M + ε / 2) hPK
    have h3 := hP z (mem_insert z K)
    calc ‖f z‖ = ‖(f z - MvPolynomial.eval z P) + MvPolynomial.eval z P‖ := by ring_nf
      _ ≤ ‖f z - MvPolynomial.eval z P‖ + ‖MvPolynomial.eval z P‖ := norm_add_le _ _
      _ ≤ M + ε := by linarith
  · intro hz P M hM
    exact hz.2 _ (AnalyticOnNhd.eval_mvPolynomial P) M hM

/-- The polynomial hull is polynomially convex. -/
theorem isPolynomiallyConvex_polynomialHull (K : Set (σ → ℂ)) :
    IsPolynomiallyConvex (polynomialHull K) := by
  refine Subset.antisymm (fun z hz P M hM => ?_) (subset_polynomialHull _)
  exact hz P M fun w hw => hw P M hM

end Hull

section Runge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A **Runge pair**: `U ⊆ V`, and every holomorphic function on `U` is approximated within `ε` on
every compact subset of `U` by a holomorphic function on `V`. -/
@[expose] def IsRungePair (U V : Set E) : Prop :=
  U ⊆ V ∧ ∀ f : E → ℂ, AnalyticOnNhd ℂ f U → ∀ K : Set E, IsCompact K → K ⊆ U → ∀ ε > 0,
    ∃ g : E → ℂ, AnalyticOnNhd ℂ g V ∧ ∀ z ∈ K, ‖f z - g z‖ < ε

/-- A Runge pair is an inclusion. -/
theorem IsRungePair.subset {U V : Set E} (h : IsRungePair U V) : U ⊆ V := h.1

/-- Every set forms a Runge pair with itself. -/
theorem isRungePair_refl (U : Set E) : IsRungePair U U :=
  ⟨Subset.rfl, fun f hf _ _ _ ε hε => ⟨f, hf, fun _ _ => by simpa using hε⟩⟩

/-- Runge pairs are transitive. -/
theorem IsRungePair.trans {U V W : Set E} (h₁ : IsRungePair U V) (h₂ : IsRungePair V W) :
    IsRungePair U W := by
  refine ⟨h₁.1.trans h₂.1, fun f hf K hK hKU ε hε => ?_⟩
  obtain ⟨g, hg, hfg⟩ := h₁.2 f hf K hK hKU (ε / 2) (half_pos hε)
  obtain ⟨k, hk, hgk⟩ := h₂.2 g hg K hK (hKU.trans h₁.1) (ε / 2) (half_pos hε)
  refine ⟨k, hk, fun z hz => ?_⟩
  calc ‖f z - k z‖ = ‖(f z - g z) + (g z - k z)‖ := by ring_nf
    _ ≤ ‖f z - g z‖ + ‖g z - k z‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hfg z hz) (hgk z hz)
    _ = ε := add_halves ε

/-- A **Runge domain** in `ℂ^ι`, for a finite index type `ι`: every holomorphic function is
    approximated within `ε` on every
compact subset by a polynomial. Being a domain of holomorphy is not part of the definition. -/
@[expose] def IsRungeDomain {ι : Type*} [Fintype ι] (U : Set (ι → ℂ)) : Prop :=
  ∀ f : (ι → ℂ) → ℂ, AnalyticOnNhd ℂ f U → ∀ K : Set (ι → ℂ), IsCompact K → K ⊆ U →
    ∀ ε > 0, ∃ P : MvPolynomial ι ℂ, ∀ z ∈ K, ‖f z - MvPolynomial.eval z P‖ < ε

variable {ι : Type*} [Fintype ι]

/-- A set is a Runge domain exactly when it forms a Runge pair with the whole space. -/
theorem isRungeDomain_iff_isRungePair_univ (U : Set (ι → ℂ)) :
    IsRungeDomain U ↔ IsRungePair U univ := by
  constructor
  · intro h
    refine ⟨subset_univ U, fun f hf K hK hKU ε hε => ?_⟩
    obtain ⟨P, hP⟩ := h f hf K hK hKU ε hε
    exact ⟨fun z => MvPolynomial.eval z P, AnalyticOnNhd.eval_mvPolynomial P, hP⟩
  · intro h f hf K hK hKU ε hε
    obtain ⟨g, hg, hfg⟩ := h.2 f hf K hK hKU (ε / 2) (half_pos hε)
    obtain ⟨P, hP⟩ := exists_mvPolynomial_approx_of_entire hg hK (half_pos hε)
    refine ⟨P, fun z hz => ?_⟩
    calc ‖f z - MvPolynomial.eval z P‖ = ‖(f z - g z) + (g z - MvPolynomial.eval z P)‖ := by ring_nf
      _ ≤ ‖f z - g z‖ + ‖g z - MvPolynomial.eval z P‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hfg z hz) (hP z hz)
      _ = ε := add_halves ε

/-- The whole space is a Runge domain. -/
theorem isRungeDomain_univ : IsRungeDomain (univ : Set (ι → ℂ)) :=
  (isRungeDomain_iff_isRungePair_univ _).mpr (isRungePair_refl _)

/-- **Hull identity for Runge domains.** For a Runge domain `U` and a compact `K ⊆ U`, the
polynomial hull of `K` meets `U` exactly in the holomorphic hull of `K` relative to `U`. -/
theorem IsRungeDomain.polynomialHull_inter {U : Set (ι → ℂ)} (h : IsRungeDomain U)
    {K : Set (ι → ℂ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    polynomialHull K ∩ U = holomorphicHull U K := by
  ext z
  constructor
  · rintro ⟨hz, hzU⟩
    refine ⟨hzU, fun f hf M hM => ?_⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨P, hP⟩ := h f hf (insert z K) (hK.insert z) (insert_subset hzU hKU) (ε / 2) (half_pos
      hε)
    have hPK : ∀ w ∈ K, ‖MvPolynomial.eval w P‖ ≤ M + ε / 2 := fun w hw => by
      have h1 := hP w (mem_insert_of_mem z hw)
      have h2 := hM w hw
      calc ‖MvPolynomial.eval w P‖ = ‖f w - (f w - MvPolynomial.eval w P)‖ := by ring_nf
        _ ≤ ‖f w‖ + ‖f w - MvPolynomial.eval w P‖ := norm_sub_le _ _
        _ ≤ M + ε / 2 := by linarith
    have hz' := hz P (M + ε / 2) hPK
    have h3 := hP z (mem_insert z K)
    calc ‖f z‖ = ‖(f z - MvPolynomial.eval z P) + MvPolynomial.eval z P‖ := by ring_nf
      _ ≤ ‖f z - MvPolynomial.eval z P‖ + ‖MvPolynomial.eval z P‖ := norm_add_le _ _
      _ ≤ M + ε := by linarith
  · intro hz
    refine ⟨fun P M hM => hz.2 _ ((AnalyticOnNhd.eval_mvPolynomial P).mono (subset_univ U)) M hM,
      hz.1⟩

/-- If the polynomial hull of every compact subset agrees with its holomorphic hull, then in
particular the intersection with `U` does. -/
theorem polynomialHull_inter_eq_of_eq {U K : Set (ι → ℂ)}
    (h : polynomialHull K = holomorphicHull U K) :
    polynomialHull K ∩ U = holomorphicHull U K := by
  rw [h]
  exact inter_eq_left.mpr (holomorphicHull_subset U K)

/-- For a Runge domain of holomorphy, the polynomial hull of a compact subset meets the domain in a
compact set. The converse implications are the Oka–Weil theorem. -/
theorem IsRungeDomain.isCompact_polynomialHull_inter {U : Set (ι → ℂ)} (h : IsRungeDomain U)
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) {K : Set (ι → ℂ)} (hK : IsCompact K)
    (hKU : K ⊆ U) : IsCompact (polynomialHull K ∩ U) := by
  rw [h.polynomialHull_inter hK hKU]
  exact hU.isHolomorphicallyConvex ho K hK hKU

end Runge

section Sequences

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Approximation on compact sets follows from locally uniform convergence of a sequence. -/
theorem isRungePair_of_forall_exists_seq {U V : Set E} (hUV : U ⊆ V)
    (h : ∀ f : E → ℂ, AnalyticOnNhd ℂ f U → ∃ g : ℕ → E → ℂ,
      (∀ k, AnalyticOnNhd ℂ (g k) V) ∧ TendstoLocallyUniformlyOn g f atTop U) :
    IsRungePair U V := by
  refine ⟨hUV, fun f hf K hK hKU ε hε => ?_⟩
  obtain ⟨g, hg, hlim⟩ := h f hf
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hlim.mono hKU)
  rw [Metric.tendstoUniformlyOn_iff] at hu
  obtain ⟨k, hk⟩ := (hu ε hε).exists
  exact ⟨g k, hg k, fun z hz => by rw [← dist_eq_norm]; exact hk z hz⟩

variable [ProperSpace E]

/-- **Sequence formulation.** For an open `U`, a Runge pair provides, for each holomorphic
function on `U`, a sequence of holomorphic functions on `V` converging locally uniformly. -/
theorem IsRungePair.exists_seq_tendstoLocallyUniformlyOn {U V : Set E} (hU : IsOpen U)
    (h : IsRungePair U V) {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    ∃ g : ℕ → E → ℂ, (∀ k, AnalyticOnNhd ℂ (g k) V) ∧ TendstoLocallyUniformlyOn g f atTop U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let B := CompactExhaustion.choice U
  let L (k : ℕ) : Set E := Subtype.val '' B k
  have hchoice : ∀ k : ℕ, ∃ g : E → ℂ, AnalyticOnNhd ℂ g V ∧
      ∀ z ∈ L k, ‖f z - g z‖ < 1 / ((k : ℝ) + 1) :=
    fun k => h.2 f hf (L k) ((B.isCompact k).image continuous_subtype_val)
      (by rintro z ⟨x, _, rfl⟩; exact x.property) _ (by positivity)
  choose g hg using hchoice
  refine ⟨g, fun k => (hg k).1, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  have hpre : IsCompact ((Subtype.val : U → E) ⁻¹' K) := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rwa [image_preimage_eq_of_subset (by simpa using hKU)]
  obtain ⟨k₀, hk₀⟩ := B.exists_superset_of_isCompact hpre
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop (max k₀ N)] with k hk z hz
  have hzk : z ∈ L k :=
    ⟨⟨z, hKU hz⟩, B.subset ((le_max_left _ _).trans hk) (hk₀ hz), rfl⟩
  have h1 := (hg k).2 z hzk
  rw [dist_eq_norm]
  refine h1.trans_le ?_
  have hkN : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_max_right _ _).trans hk
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at hN
  nlinarith

end Sequences

end SeveralComplexVariables
