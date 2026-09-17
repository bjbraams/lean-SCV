/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.AnalyticSet.Basic
public import SeveralComplexVariables.ImplicitGraph

/-!
# Regular points of analytic subsets

Regularity means that local biholomorphic ambient coordinates identify the subset
with the kernel of a surjective complex linear map. This is intrinsic to the subset:
`z₁² = 0` and `z₁ = 0` define the same regular hyperplane. No manifold structure is used.
The full-rank-equations criterion is proved by a linear right inverse and the
holomorphic inverse mapping theorem. Existence of regular hypersurface points remains pending. Relative openness of the regular
locus and relative closedness of the singular locus are proved from the definition.

Reference: Fritzsche–Grauert I, 8.3–8.4; Range I §3.2.
-/

@[expose] public noncomputable section

open Set

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Intrinsic regularity of codimension `q`: local biholomorphic coordinates flatten
`A` to the kernel of a surjective map to `ℂ^q`. Membership in `A` is included. -/
def IsRegularAnalyticSetAt (A : Set E) (a : E) (q : ℕ) : Prop :=
  a ∈ A ∧ ∃ (e : OpenPartialHomeomorph E E) (L : E →L[ℂ] (Fin q → ℂ)),
    IsBiholomorphic e ∧ a ∈ e.source ∧ Function.Surjective L ∧
      ∀ z ∈ e.source, z ∈ A ↔ L (e z) = 0

/-- The regular locus includes all local codimensions, including codimension zero. -/
def analyticRegularLocus (A : Set E) : Set E := {a | ∃ q, IsRegularAnalyticSetAt A a q}

/-- Singular points are the points of the subset that are not regular. -/
def analyticSingularLocus (A : Set E) : Set E := A \ analyticRegularLocus A

/-- Every regular point belongs to the subset. -/
theorem analyticRegularLocus_subset (A : Set E) : analyticRegularLocus A ⊆ A := by
  rintro a ⟨q, h⟩
  exact h.1

/-- The local codimension of a regular point is bounded by the ambient dimension. -/
theorem IsRegularAnalyticSetAt.le_finrank [FiniteDimensional ℂ E]
    {A : Set E} {a : E} {q : ℕ} (h : IsRegularAnalyticSetAt A a q) :
    q ≤ Module.finrank ℂ E := by
  obtain ⟨_, _, L, _, _, hL, _⟩ := h
  simpa using LinearMap.finrank_le_finrank_of_surjective (f := L.toLinearMap) hL

/-- A flattening chart witnesses the same codimension at every nearby point of the set. -/
theorem IsRegularAnalyticSetAt.exists_open {A : Set E} {a : E} {q : ℕ}
    (h : IsRegularAnalyticSetAt A a q) :
    ∃ V, IsOpen V ∧ a ∈ V ∧ ∀ b ∈ V ∩ A, IsRegularAnalyticSetAt A b q := by
  obtain ⟨_, e, L, he, ha, hL, hEq⟩ := h
  exact ⟨e.source, e.open_source, ha, fun b hb => ⟨hb.2, e, L, he, hb.1, hL, hEq⟩⟩

/-- The regular locus is relatively open in the subset, without any global analyticity assumption. -/
theorem analyticRegularLocus_isOpen_relative (A : Set E) :
    IsOpen {a : A | a.val ∈ analyticRegularLocus A} := by
  rw [isOpen_iff_mem_nhds]
  rintro a ⟨q, hq⟩
  obtain ⟨V, hV, haV, hreg⟩ := hq.exists_open
  apply Filter.mem_of_superset ((hV.preimage continuous_subtype_val).mem_nhds haV)
  intro b hb
  exact ⟨q, hreg b ⟨hb, b.property⟩⟩

/-- The singular locus is relatively closed in the subset. This does not assert that it is analytic. -/
theorem analyticSingularLocus_isClosed_relative (A : Set E) :
    IsClosed {a : A | a.val ∈ analyticSingularLocus A} := by
  have he : {a : A | a.val ∈ analyticSingularLocus A} =
      {a : A | a.val ∈ analyticRegularLocus A}ᶜ := by
    ext a
    simp [analyticSingularLocus]
  rw [he]
  exact (analyticRegularLocus_isOpen_relative A).isClosed_compl

/-- On an analytic subset of `U`, the singular locus is relatively closed also in `U`. -/
theorem IsAnalyticSet.isOpen_sdiff_singularLocus {U A : Set E} (hA : IsAnalyticSet U A) :
    IsOpen (U \ analyticSingularLocus A) := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro a ⟨haU, has⟩
  by_cases haA : a ∈ A
  · have har : a ∈ analyticRegularLocus A := by
      by_contra hn
      exact has ⟨haA, hn⟩
    obtain ⟨q, hq⟩ := har
    obtain ⟨V, hV, haV, hreg⟩ := hq.exists_open
    apply Filter.mem_of_superset ((hA.isOpen_domain.inter hV).mem_nhds ⟨haU, haV⟩)
    intro b hb
    exact ⟨hb.1, fun hbs => hbs.2 ⟨q, hreg b ⟨hb.2, hbs.1⟩⟩⟩
  · exact Filter.mem_of_superset (hA.isOpen_sdiff.mem_nhds ⟨haU, haA⟩)
      (fun b hb => ⟨hb.1, fun hbs => hb.2 hbs.1⟩)

/-- Flattening coordinates supply local defining equations with surjective derivative. -/
theorem IsRegularAnalyticSetAt.exists_equations [FiniteDimensional ℂ E]
    {A : Set E} {a : E} {q : ℕ} (h : IsRegularAnalyticSetAt A a q) :
    ∃ (V : Set E) (f : E → (Fin q → ℂ)), IsOpen V ∧ a ∈ V ∧
      AnalyticOnNhd ℂ f V ∧ (∀ z ∈ V, z ∈ A ↔ f z = 0) ∧
      Function.Surjective (fderiv ℂ f a) := by
  let := FiniteDimensional.complete ℂ E
  obtain ⟨_, e, L, he, ha, hL, hEq⟩ := h
  refine ⟨e.source, L ∘ e, e.open_source, ha, ?_, hEq, ?_⟩
  · intro z hz
    exact (L.analyticAt (e z)).comp
      ((he.1.analyticOnNhd_finiteDimensional e.open_source) z hz)
  · rw [fderiv_comp a L.differentiableAt (he.differentiableAt ha), L.fderiv]
    obtain ⟨M, hM⟩ := he.isInvertible_fderiv ha
    rw [← hM]
    exact hL.comp M.surjective

/-- Full-rank local defining equations admit flattening biholomorphic coordinates.
A linear right inverse corrects the defining map to have identity derivative, so the
holomorphic inverse mapping theorem supplies the required coordinates. -/
theorem isRegularAnalyticSetAt_of_equations [FiniteDimensional ℂ E]
    {A V : Set E} {a : E} {q : ℕ} (haA : a ∈ A) (hV : IsOpen V) (haV : a ∈ V)
    {f : E → (Fin q → ℂ)} (hf : AnalyticOnNhd ℂ f V)
    (hEq : ∀ z ∈ V, z ∈ A ↔ f z = 0) (hs : Function.Surjective (fderiv ℂ f a)) :
    IsRegularAnalyticSetAt A a q := by
  let L := fderiv ℂ f a
  obtain ⟨R, hR⟩ := L.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hs)
  let B : (Fin q → ℂ) →L[ℂ] E := R.toContinuousLinearMap
  have hLB (y : Fin q → ℂ) : L (B y) = y := DFunLike.congr_fun hR y
  let g : E → E := fun x => x + B (f x - L x)
  have hg : DifferentiableOn ℂ g V :=
    differentiableOn_id.add (B.differentiable.comp_differentiableOn
      (hf.differentiableOn.sub L.differentiable.differentiableOn))
  have hd : HasFDerivAt g (ContinuousLinearMap.id ℂ E) a := by
    simpa only [g, L, Pi.add_def, Pi.sub_def, Function.comp_def, id_eq,
      sub_self, ContinuousLinearMap.comp_zero, add_zero] using
      (hasFDerivAt_id a).add (B.hasFDerivAt.comp a
        ((hf a haV).differentiableAt.hasFDerivAt.sub L.hasFDerivAt))
  have hinv : (fderiv ℂ g a).IsInvertible := by
    rw [hd.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℂ E, rfl⟩
  obtain ⟨e, he, hae, heV, heq⟩ := exists_biholomorphic_of_isInvertible_fderiv hV hg haV hinv
  refine ⟨haA, e, L, he, hae, hs, ?_⟩
  intro z hz
  rw [hEq z (heV hz), heq]
  have hLg : L (g z) = f z := by
    dsimp [g]
    rw [map_add, hLB]
    abel
  rw [hLg]

/-- **Local coordinate characterization.** Regularity is equivalent to the existence
of full-rank defining equations, not a rank condition on an arbitrary presentation.
Both directions follow from the holomorphic inverse mapping theorem and the chain rule. -/
theorem isRegularAnalyticSetAt_iff_exists_equations [FiniteDimensional ℂ E]
    {A : Set E} {a : E} {q : ℕ} :
    IsRegularAnalyticSetAt A a q ↔ a ∈ A ∧
      ∃ (V : Set E) (f : E → (Fin q → ℂ)), IsOpen V ∧ a ∈ V ∧
        AnalyticOnNhd ℂ f V ∧ (∀ z ∈ V, z ∈ A ↔ f z = 0) ∧
        Function.Surjective (fderiv ℂ f a) := by
  refine ⟨fun h => ⟨h.1, h.exists_equations⟩, ?_⟩
  rintro ⟨haA, V, f, hV, haV, hf, hEq, hs⟩
  exact isRegularAnalyticSetAt_of_equations haA hV haV hf hEq hs

/-- A surjective linear equation defines a regular linear subspace of the expected codimension. -/
theorem isRegularAnalyticSetAt_linear_zeroSet (q : ℕ) (L : E →L[ℂ] (Fin q → ℂ))
    (hL : Function.Surjective L) {a : E} (ha : L a = 0) :
    IsRegularAnalyticSetAt (L ⁻¹' {0}) a q := by
  exact ⟨ha, OpenPartialHomeomorph.refl E, L, isBiholomorphic_refl,
    Set.mem_univ a, hL, fun _ _ => Iff.rfl⟩

/-- **Regular points of a hypersurface.** A nonempty proper scalar zero set in a
preconnected domain contains a regular point of codimension one. The nonempty zero-set
hypothesis repairs its omission in the printed Fritzsche–Grauert I, Proposition 8.4.
The hypersurface regularity argument remains to be proved. -/
theorem exists_regularPoint_zeroSet [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U) {f : E → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hne : ∃ b ∈ U, f b ≠ 0) (hz : ∃ a ∈ U, f a = 0) :
    ∃ a, IsRegularAnalyticSetAt (U ∩ f ⁻¹' {0}) a 1 := by
  sorry

end SeveralComplexVariables
