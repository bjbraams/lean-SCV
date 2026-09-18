/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.HolomorphicConvexity.Thullen
public import SeveralComplexVariables.PolydiscTaylor
public import SeveralComplexVariables.Analyticity
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

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
the elementary implications of the hull characterization of Runge domains (Hörmander, Theorem
2.7.3; Jakóbczak–Jarnicki, Theorem 4.3.3). The converse implications constitute the Oka–Weil
theorem and are not included.

References: Hörmander (1973), Section 2.7; Jakóbczak–Jarnicki (2021), Section 4.3;
Korevaar–Wiegerinck (2017), Section 1.7.
-/

@[expose] public noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace SeveralComplexVariables

section Polynomials

variable {n : ℕ}

/-- Polynomials are entire functions. -/
theorem analyticOnNhd_mvPolynomial (P : MvPolynomial (Fin n) ℂ) :
    AnalyticOnNhd ℂ (fun z : Fin n → ℂ => MvPolynomial.eval z P) univ := by
  intro z _
  have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (z := z)
    (f := fun (x : Fin n → ℂ) (i : Fin n) => x i)
    (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt z) P
  convert h using 2 with x
  rw [← MvPolynomial.coe_aeval_eq_eval]
  rfl

/-- Polynomial evaluation is continuous. -/
theorem continuous_mvPolynomial_eval (P : MvPolynomial (Fin n) ℂ) :
    Continuous fun z : Fin n → ℂ => MvPolynomial.eval z P :=
  continuousOn_univ.mp (analyticOnNhd_mvPolynomial P).continuousOn

/-- A finite sum of monomials with complex coefficients, indexed by finitely supported
multi-indices, is the evaluation of a polynomial. -/
theorem exists_mvPolynomial_eval_eq_sum (s : Finset (Fin n →₀ ℕ)) (c : (Fin n →₀ ℕ) → ℂ) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ z : Fin n → ℂ,
      MvPolynomial.eval z P = ∑ m ∈ s, (∏ i, z i ^ m i) * c m := by
  refine ⟨∑ m ∈ s, MvPolynomial.C (c m) * ∏ i, MvPolynomial.X i ^ (m i), fun z => ?_⟩
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, map_pow, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- The same statement for multi-indices given as functions. -/
theorem exists_mvPolynomial_eval_eq_sum' (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ z : Fin n → ℂ,
      MvPolynomial.eval z P = ∑ m ∈ s, (∏ i, z i ^ m i) * c m := by
  refine ⟨∑ m ∈ s, MvPolynomial.C (c m) * ∏ i, MvPolynomial.X i ^ (m i), fun z => ?_⟩
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, map_pow, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **Entire functions are locally uniform limits of polynomials.** On a compact set, an entire
function is approximated within `ε` by a Taylor polynomial. -/
theorem exists_mvPolynomial_approx_of_entire {g : (Fin n → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g univ) {K : Set (Fin n → ℂ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ z ∈ K, ‖g z - MvPolynomial.eval z P‖ < ε := by
  obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall 0
  set R : Fin n → ℝ := fun _ => max B 0 + 1 with hRdef
  have hR : ∀ i, 0 < R i := fun _ => by positivity
  set s : Fin n → ℝ := fun _ => max B 0 with hsdef
  have hs : ∀ i, 0 ≤ s i := fun _ => le_max_right _ _
  have hsR : ∀ i, s i < R i := fun _ => by simp [hsdef, hRdef]
  have hKs : K ⊆ closedPolydiscWithRadii 0 s := by
    intro z hz
    rw [mem_closedPolydiscWithRadii]
    intro i
    have h1 : ‖z i‖ ≤ ‖z‖ := norm_le_pi_norm z i
    have h2 : ‖z‖ ≤ B := mem_closedBall_zero_iff.mp (hB hz)
    rw [Pi.zero_apply, dist_zero_right]
    exact h1.trans (h2.trans (le_max_left _ _))
  have hcont : ContinuousOn g (closedPolydiscWithRadii 0 R) := hg.continuousOn.mono (subset_univ _)
  have hslice : ∀ z ∈ closedPolydiscWithRadii 0 R, ∀ i,
      AnalyticAt ℂ (fun v => g (update z i v)) (z i) :=
    fun z _ i => by convert hg.analyticAt_update (mem_univ z) i
  obtain ⟨M, hM⟩ := (isCompact_closedPolydiscWithRadii 0 R).exists_bound_of_continuousOn hcont
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

end Polynomials

section Hull

variable {n : ℕ}

/-- The polynomial hull of a set: the points at which every polynomial is bounded by each of its
bounds on the set. -/
def polynomialHull (K : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {z | ∀ P : MvPolynomial (Fin n) ℂ, ∀ M : ℝ,
    (∀ w ∈ K, ‖MvPolynomial.eval w P‖ ≤ M) → ‖MvPolynomial.eval z P‖ ≤ M}

/-- A set is polynomially convex if it equals its polynomial hull. -/
def IsPolynomiallyConvex (K : Set (Fin n → ℂ)) : Prop := polynomialHull K = K

/-- A set lies in its polynomial hull. -/
theorem subset_polynomialHull (K : Set (Fin n → ℂ)) : K ⊆ polynomialHull K :=
  fun z hz _ _ hM => hM z hz

/-- The polynomial hull is monotone. -/
theorem polynomialHull_mono {K L : Set (Fin n → ℂ)} (h : K ⊆ L) :
    polynomialHull K ⊆ polynomialHull L :=
  fun _ hz P M hM => hz P M fun w hw => hM w (h hw)

/-- The polynomial hull is closed. -/
theorem isClosed_polynomialHull (K : Set (Fin n → ℂ)) : IsClosed (polynomialHull K) := by
  have : polynomialHull K = ⋂ P : MvPolynomial (Fin n) ℂ, ⋂ M : ℝ,
      ⋂ _ : (∀ w ∈ K, ‖MvPolynomial.eval w P‖ ≤ M), {z | ‖MvPolynomial.eval z P‖ ≤ M} := by
    ext z
    simp only [polynomialHull, mem_ofPred_eq, mem_iInter]
  rw [this]
  exact isClosed_iInter fun P => isClosed_iInter fun M => isClosed_iInter fun _ =>
    isClosed_le (continuous_mvPolynomial_eval P).norm continuous_const

/-- The polynomial hull of a bounded set is bounded, by the coordinate polynomials. -/
theorem polynomialHull_subset_closedBall {K : Set (Fin n → ℂ)} {B : ℝ} (hB0 : 0 ≤ B)
    (hK : K ⊆ closedBall 0 B) : polynomialHull K ⊆ closedBall 0 B := by
  intro z hz
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hB0]
  intro i
  have := hz (MvPolynomial.X i) B fun w hw => by
    rw [MvPolynomial.eval_X]
    exact (norm_le_pi_norm w i).trans (mem_closedBall_zero_iff.mp (hK hw))
  rwa [MvPolynomial.eval_X] at this

/-- The polynomial hull of a compact set is compact. -/
theorem isCompact_polynomialHull {K : Set (Fin n → ℂ)} (hK : IsCompact K) :
    IsCompact (polynomialHull K) := by
  obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall 0
  have hB' : K ⊆ closedBall 0 (max B 0) :=
    hB.trans (closedBall_subset_closedBall (le_max_left _ _))
  exact isCompact_of_isClosed_isBounded (isClosed_polynomialHull K)
    (isBounded_closedBall.subset (polynomialHull_subset_closedBall (le_max_right _ _) hB'))

/-- **Polynomial and entire hulls agree** on compact sets, since entire functions are locally
uniform limits of polynomials. -/
theorem polynomialHull_eq_holomorphicHull_univ {K : Set (Fin n → ℂ)} (hK : IsCompact K) :
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
    exact hz.2 _ (analyticOnNhd_mvPolynomial P) M hM

/-- The polynomial hull is polynomially convex. -/
theorem isPolynomiallyConvex_polynomialHull (K : Set (Fin n → ℂ)) :
    IsPolynomiallyConvex (polynomialHull K) := by
  refine Subset.antisymm (fun z hz P M hM => ?_) (subset_polynomialHull _)
  exact hz P M fun w hw => hw P M hM

end Hull

section Runge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A **Runge pair**: `U ⊆ V`, and every holomorphic function on `U` is approximated within `ε`
on every compact subset of `U` by a holomorphic function on `V`. -/
def IsRungePair (U V : Set E) : Prop :=
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

/-- A **Runge domain** in `ℂⁿ`: every holomorphic function is approximated within `ε` on every
compact subset by a polynomial. Being a domain of holomorphy is not part of the definition. -/
def IsRungeDomain {n : ℕ} (U : Set (Fin n → ℂ)) : Prop :=
  ∀ f : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ f U → ∀ K : Set (Fin n → ℂ), IsCompact K → K ⊆ U →
    ∀ ε > 0, ∃ P : MvPolynomial (Fin n) ℂ, ∀ z ∈ K, ‖f z - MvPolynomial.eval z P‖ < ε

variable {n : ℕ}

/-- A set is a Runge domain exactly when it forms a Runge pair with the whole space. -/
theorem isRungeDomain_iff_isRungePair_univ (U : Set (Fin n → ℂ)) :
    IsRungeDomain U ↔ IsRungePair U univ := by
  constructor
  · intro h
    refine ⟨subset_univ U, fun f hf K hK hKU ε hε => ?_⟩
    obtain ⟨P, hP⟩ := h f hf K hK hKU ε hε
    exact ⟨fun z => MvPolynomial.eval z P, analyticOnNhd_mvPolynomial P, hP⟩
  · intro h f hf K hK hKU ε hε
    obtain ⟨g, hg, hfg⟩ := h.2 f hf K hK hKU (ε / 2) (half_pos hε)
    obtain ⟨P, hP⟩ := exists_mvPolynomial_approx_of_entire hg hK (half_pos hε)
    refine ⟨P, fun z hz => ?_⟩
    calc ‖f z - MvPolynomial.eval z P‖ = ‖(f z - g z) + (g z - MvPolynomial.eval z P)‖ := by ring_nf
      _ ≤ ‖f z - g z‖ + ‖g z - MvPolynomial.eval z P‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hfg z hz) (hP z hz)
      _ = ε := add_halves ε

/-- The whole space is a Runge domain. -/
theorem isRungeDomain_univ : IsRungeDomain (univ : Set (Fin n → ℂ)) :=
  (isRungeDomain_iff_isRungePair_univ _).mpr (isRungePair_refl _)

/-- **Hull identity for Runge domains.** For a Runge domain `U` and a compact `K ⊆ U`, the
polynomial hull of `K` meets `U` exactly in the holomorphic hull of `K` relative to `U`. -/
theorem IsRungeDomain.polynomialHull_inter {U : Set (Fin n → ℂ)} (h : IsRungeDomain U)
    {K : Set (Fin n → ℂ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    polynomialHull K ∩ U = holomorphicHull U K := by
  ext z
  constructor
  · rintro ⟨hz, hzU⟩
    refine ⟨hzU, fun f hf M hM => ?_⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨P, hP⟩ := h f hf (insert z K) (hK.insert z) (insert_subset hzU hKU) (ε / 2) (half_pos hε)
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
    refine ⟨fun P M hM => hz.2 _ ((analyticOnNhd_mvPolynomial P).mono (subset_univ U)) M hM, hz.1⟩

/-- If the polynomial hull of every compact subset agrees with its holomorphic hull, then in
particular the intersection with `U` does. -/
theorem polynomialHull_inter_eq_of_eq {U K : Set (Fin n → ℂ)}
    (h : polynomialHull K = holomorphicHull U K) :
    polynomialHull K ∩ U = holomorphicHull U K := by
  rw [h]
  exact inter_eq_left.mpr (holomorphicHull_subset U K)

/-- For a Runge domain of holomorphy, the polynomial hull of a compact subset meets the domain
in a compact set. The converse implications are the Oka–Weil theorem. -/
theorem IsRungeDomain.isCompact_polynomialHull_inter {U : Set (Fin n → ℂ)} (h : IsRungeDomain U)
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) {K : Set (Fin n → ℂ)} (hK : IsCompact K)
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

omit [NormedSpace ℂ E] in
/-- An exhaustion of an open set by compact subsets of the form `closedBall 0 k ∩ {infDist ≥ 1/(k+1)}`.
Every compact subset of the open set lies in one of them, and they increase. -/
theorem exists_compact_exhaustion {U : Set E} (hU : IsOpen U) :
    ∃ L : ℕ → Set E, (∀ k, IsCompact (L k)) ∧ (∀ k, L k ⊆ U) ∧ (∀ k, L k ⊆ L (k + 1)) ∧
      ∀ K, IsCompact K → K ⊆ U → ∃ k, K ⊆ L k := by
  rcases eq_empty_or_nonempty Uᶜ with hc | hc
  · have hU' : U = univ := compl_empty_iff.mp hc
    refine ⟨fun k => closedBall 0 k, fun k => isCompact_closedBall 0 k, fun k => by rw [hU']; exact subset_univ _,
      fun k => closedBall_subset_closedBall (by exact_mod_cast Nat.le_succ k), fun K hK _ => ?_⟩
    obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨k, hk⟩ := exists_nat_ge B
    exact ⟨k, hB.trans (closedBall_subset_closedBall hk)⟩
  refine ⟨fun k => closedBall 0 k ∩ {z | 1 / ((k : ℝ) + 1) ≤ infDist z Uᶜ}, fun k => ?_, fun k z hz => ?_,
    fun k z hz => ⟨closedBall_subset_closedBall (by exact_mod_cast Nat.le_succ k) hz.1, ?_⟩,
    fun K hK hKU => ?_⟩
  · exact isCompact_of_isClosed_isBounded (isClosed_closedBall.inter
      (isClosed_le continuous_const (continuous_infDist_pt _))) (isBounded_closedBall.subset inter_subset_left)
  · have hpos : 0 < infDist z Uᶜ := lt_of_lt_of_le (by positivity) hz.2
    by_contra hzU
    rw [infDist_zero_of_mem hzU] at hpos
    exact lt_irrefl _ hpos
  · have h1 : (1 : ℝ) / ((k : ℝ) + 1 + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    show (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) ≤ infDist z Uᶜ
    push_cast
    exact le_trans h1 hz.2
  · obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall 0
    -- positive distance from the complement
    have hd : ∃ δ > 0, ∀ z ∈ K, δ ≤ infDist z Uᶜ := by
      rcases K.eq_empty_or_nonempty with hKe | hKne
      · exact ⟨1, one_pos, fun z hz => by simp [hKe] at hz⟩
      obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne (continuous_infDist_pt Uᶜ).continuousOn
      refine ⟨infDist z₀ Uᶜ, ?_, fun z hz => hmin hz⟩
      exact (infDist_pos_iff_notMem_closure hc).mp (by
        rw [hU.isClosed_compl.closure_eq]
        exact notMem_compl_iff.mpr (hKU hz₀))
    obtain ⟨δ, hδ, hδK⟩ := hd
    obtain ⟨k₁, hk₁⟩ := exists_nat_ge B
    obtain ⟨k₂, hk₂⟩ := exists_nat_ge (1 / δ)
    refine ⟨max k₁ k₂, fun z hz => ⟨closedBall_subset_closedBall ?_ (hB hz), ?_⟩⟩
    · exact hk₁.trans (by exact_mod_cast le_max_left k₁ k₂)
    · have hk₂' : (1 : ℝ) / δ ≤ (max k₁ k₂ : ℕ) + 1 := by
        have : (k₂ : ℝ) ≤ (max k₁ k₂ : ℕ) := by exact_mod_cast le_max_right k₁ k₂
        linarith
      have : (1 : ℝ) / ((max k₁ k₂ : ℕ) + 1) ≤ δ := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hδ] at hk₂'
        linarith
      exact this.trans (hδK z hz)

/-- **Sequence formulation.** For an open `U`, a Runge pair provides, for each holomorphic
function on `U`, a sequence of holomorphic functions on `V` converging locally uniformly. -/
theorem IsRungePair.exists_seq_tendstoLocallyUniformlyOn {U V : Set E} (hU : IsOpen U)
    (h : IsRungePair U V) {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    ∃ g : ℕ → E → ℂ, (∀ k, AnalyticOnNhd ℂ (g k) V) ∧ TendstoLocallyUniformlyOn g f atTop U := by
  obtain ⟨L, hLc, hLU, hLmono, hLex⟩ := exists_compact_exhaustion hU
  have hchoice : ∀ k : ℕ, ∃ g : E → ℂ, AnalyticOnNhd ℂ g V ∧
      ∀ z ∈ L k, ‖f z - g z‖ < 1 / ((k : ℝ) + 1) :=
    fun k => h.2 f hf (L k) (hLc k) (hLU k) _ (by positivity)
  choose g hg using hchoice
  refine ⟨g, fun k => (hg k).1, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  obtain ⟨k₀, hk₀⟩ := hLex K hK hKU
  have hLmono' : ∀ k, k₀ ≤ k → L k₀ ⊆ L k := fun k hk => by
    induction hk with
    | refl => exact Subset.rfl
    | step _ ih => exact ih.trans (hLmono _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop (max k₀ N)] with k hk z hz
  have hzk : z ∈ L k := hLmono' k ((le_max_left _ _).trans hk) (hk₀ hz)
  have h1 := (hg k).2 z hzk
  rw [dist_eq_norm]
  refine h1.trans_le ?_
  have hkN : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_max_right _ _).trans hk
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at hN
  nlinarith

end Sequences

end SeveralComplexVariables
