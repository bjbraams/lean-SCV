/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.ImplicitMapping

import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Local zero sets as graphs

The implicit mapping theorem supplies a homeomorphism from a regular local zero set to the
parameter neighborhood. This is an elementary statement about subsets of product spaces, without
a manifold or analytic-space structure. Reference: [Scheidemann][Scheidemann2005] (2005),
Corollary 3.1.5.

## Main results

`exists_implicit_zero_homeomorph` identifies a regular local zero set homeomorphically with
its parameter neighborhood. It combines the implicit mapping theorem with Mathlib's
construction of a homeomorphism from a surjective embedding.

## References

* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Topology

namespace SeveralComplexVariables

variable {P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [NormedAddCommGroup R] [NormedSpace ℂ R]

/-- Near a regular zero, projection identifies the zero set homeomorphically with an open parameter
neighborhood. This retains the analytic graph and its explicit projection. -/
theorem exists_implicit_zero_homeomorph [FiniteDimensional ℂ P] [FiniteDimensional ℂ Q]
    [CompleteSpace R] {D : Set (P × Q)} (hD : IsOpen D)
    {f : P × Q → R} (hf : DifferentiableOn ℂ f D) {a : P} {b : Q}
    (hab : (a, b) ∈ D) (hz : f (a, b) = 0)
    (hi : ((fderiv ℂ f (a, b)).comp (ContinuousLinearMap.inr ℂ P Q)).IsInvertible) :
    ∃ (U : Set P) (V : Set Q), IsOpen U ∧ a ∈ U ∧ IsOpen V ∧ b ∈ V ∧ U ×ˢ V ⊆ D ∧
      ∃ e : {p : P × Q // p ∈ U ×ˢ V ∧ f p = 0} ≃ₜ U,
        ∀ p, (e p).val = p.val.1 := by
  obtain ⟨U, V, g, hU, ha, hV, hb, hsub, hg, hm, _, hgraph⟩ :=
    exists_holomorphic_implicit_zero hD hf hab hz hi
  let Z := {p : P × Q // p ∈ U ×ˢ V ∧ f p = 0}
  let π : Z → U := fun p ↦ ⟨p.val.1, p.property.1.1⟩
  let γ : U → P × Q := fun x ↦ (x.val, g x)
  have hcomp : γ ∘ π = Subtype.val := by
    funext p
    apply Prod.ext
    · rfl
    · exact ((hgraph p.val.1 p.property.1.1 p.val.2 p.property.1.2).mp p.property.2).symm
  have he : IsEmbedding π := .of_comp (g := γ)
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _)
    (continuous_subtype_val.prodMk hg.continuousOn.domRestrict)
    (by rw [hcomp]; exact .subtypeVal)
  have hs : Function.Surjective π := fun x ↦
    ⟨⟨(x.val, g x), ⟨⟨x.property, hm x.property⟩,
      (hgraph x x.property (g x) (hm x.property)).mpr rfl⟩⟩, rfl⟩
  exact ⟨U, V, hU, ha, hV, hb, hsub, he.toHomeomorphOfSurjective hs, fun _ ↦ rfl⟩

end SeveralComplexVariables
