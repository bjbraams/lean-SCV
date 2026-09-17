/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.HolomorphicConvexity.Hull
public import SeveralComplexVariables.LocallyUniform
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Holomorphically convex exhaustions and escaping sequences

Separation outside a hull can be amplified by powers to make a function arbitrarily
small on the original set and arbitrarily large at the chosen point. This step is proved.
The compact exhaustion is constructed by repeatedly enlarging compact sets and taking
their holomorphic hulls. The escaping-sequence characterization remains pending. Exhaustions use Mathlib's `CompactExhaustion`
on the open subtype, rather than a new topological structure.

References: Range II §3.2; Fritzsche–Grauert II §6; Scheidemann §7.1.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Powers of a separating function give arbitrary smallness on the set and an arbitrary
large value at an exterior hull point. Empty sets are included. -/
theorem exists_small_large_separator {U K : Set E} {a : E}
    (ha : a ∈ U) (hn : a ∉ holomorphicHull U K) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ f : E → ℂ, AnalyticOnNhd ℂ f U ∧ (∀ z ∈ K, ‖f z‖ < ε) ∧ R < ‖f a‖ := by
  let A : ℝ := max R 0 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hRA : R < A := by dsimp [A]; linarith [le_max_left R 0]
  rcases K.eq_empty_or_nonempty with hK | hK
  · subst K
    exact ⟨fun _ => (A : ℂ), analyticOnNhd_const, by simp,
      by simpa only [Complex.norm_of_nonneg hA.le] using hRA⟩
  obtain ⟨f, hf, M, hM, hMa⟩ := exists_separator_of_notMem_holomorphicHull ha hn
  obtain ⟨z₀, hz₀⟩ := hK
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z₀ hz₀)
  have hfa : 0 < ‖f a‖ := hM0.trans_lt hMa
  have hq : M / ‖f a‖ < 1 := (div_lt_one hfa).mpr hMa
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hA) hq
  refine ⟨fun z => (A : ℂ) * (f z / f a) ^ k,
    analyticOnNhd_const.mul (hf.div_const.pow k), ?_, ?_⟩
  · intro z hz
    rw [norm_mul, Complex.norm_of_nonneg hA.le, norm_pow, norm_div]
    calc
      A * (‖f z‖ / ‖f a‖) ^ k ≤ A * (M / ‖f a‖) ^ k := by
        gcongr
        exact hM z hz
      _ < ε := (lt_div_iff₀ hA).mp hk |> (by simpa [mul_comm] using ·)
  · simpa [div_self (norm_pos_iff.mp hfa), Complex.norm_of_nonneg hA.le, abs_of_pos hA] using hRA

variable {ι : Type*} [Fintype ι]

/-- A holomorphically convex open set has a compact exhaustion by sets fixed by the
relative holomorphic hull, by recursive refinement of a compact exhaustion. -/
theorem IsHolomorphicallyConvex.exists_compactExhaustion {U : Set (ι → ℂ)}
    (hU : IsHolomorphicallyConvex U) (ho : IsOpen U) :
    ∃ K : CompactExhaustion U, ∀ j,
      IsHolomorphicallyConvexIn U ((Subtype.val : U → (ι → ℂ)) '' K j) := by
  let : LocallyCompactSpace U := ho.locallyCompactSpace
  let B := CompactExhaustion.choice U
  let H (S : Set U) : Set U :=
    (Subtype.val : U → (ι → ℂ)) ⁻¹' holomorphicHull U (Subtype.val '' S)
  have himage (S : Set U) : Subtype.val '' H S = holomorphicHull U (Subtype.val '' S) := by
    apply image_preimage_eq_of_subset
    intro z hz
    exact ⟨⟨z, hz.1⟩, rfl⟩
  have hcompact (S : Set U) (hS : IsCompact S) : IsCompact (H S) := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [himage]
    exact hU _ (hS.image continuous_subtype_val) (by rintro _ ⟨z, _, rfl⟩; exact z.property)
  have hsubset (S : Set U) : S ⊆ H S := by
    intro z hz
    exact subset_holomorphicHull (by rintro _ ⟨w, _, rfl⟩; exact w.property) ⟨z, hz, rfl⟩
  have hfixed (S : Set U) : IsHolomorphicallyConvexIn U (Subtype.val '' H S) := by
    rw [himage]
    exact isHolomorphicallyConvexIn_holomorphicHull _ _
  let enlarge (S : {S : Set U // IsCompact S}) : {S : Set U // IsCompact S} :=
    ⟨(exists_compact_superset S.property).choose, (exists_compact_superset S.property).choose_spec.1⟩
  have henlarge (S : {S : Set U // IsCompact S}) : S.val ⊆ interior (enlarge S).val :=
    (exists_compact_superset S.property).choose_spec.2
  let K : ℕ → {S : Set U // IsCompact S} := fun j =>
    Nat.recOn j ⟨H (B 0), hcompact _ (B.isCompact 0)⟩ fun j S =>
      ⟨H ((enlarge S).val ∪ B (j + 1)), hcompact _ ((enlarge S).property.union (B.isCompact _))⟩
  have hBK (j : ℕ) : B j ⊆ (K j).val := by
    cases j with
    | zero => exact hsubset _
    | succ j => exact subset_union_right.trans (hsubset _)
  refine ⟨{ toFun := fun j => (K j).val
            isCompact' := fun j => (K j).property
            subset_interior_succ' := ?_
            iUnion_eq' := ?_ }, ?_⟩
  · intro j
    exact (henlarge (K j)).trans (interior_mono (subset_union_left.trans (hsubset _)))
  · apply iUnion_eq_univ_iff.mpr
    intro z
    obtain ⟨j, hj⟩ := B.exists_mem z
    exact ⟨j, hBK j hj⟩
  · intro j
    cases j with
    | zero => exact hfixed _
    | succ j => exact hfixed _

/-- A sequence escapes compact subsets when it eventually leaves every compact set in
the ambient domain. Its membership in the domain is a separate hypothesis. -/
def EscapesCompactSubsets (U : Set E) (p : ℕ → E) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ U → ∀ᶠ j in atTop, p j ∉ K

/-- **Escaping-sequence characterization of holomorphic convexity.** Proof pending:
construct a normally convergent separating series; conversely extract an escaping
sequence from a noncompact hull. -/
theorem isHolomorphicallyConvex_iff_unbounded_on_escaping_sequences
    {U : Set (ι → ℂ)} (ho : IsOpen U) :
    IsHolomorphicallyConvex U ↔
      ∀ p : ℕ → (ι → ℂ), (∀ j, p j ∈ U) → EscapesCompactSubsets U p →
        ∃ f : (ι → ℂ) → ℂ, AnalyticOnNhd ℂ f U ∧
          ¬ BddAbove (Set.range (fun j => ‖f (p j)‖)) := by
  sorry

end SeveralComplexVariables
