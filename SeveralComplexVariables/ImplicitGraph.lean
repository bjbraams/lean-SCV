/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.ImplicitMapping

/-!
# Local zero sets as graphs

The implicit mapping theorem supplies a homeomorphism from a regular local zero set
to the parameter neighborhood. This is an elementary statement about subsets of product
spaces, without a manifold or analytic-space structure.
Reference: Scheidemann (2005), Corollary 3.1.5.
-/

public noncomputable section

open Set

namespace SeveralComplexVariables

variable {P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [NormedAddCommGroup R] [NormedSpace ℂ R]

/-- A continuous graph characterization makes projection a homeomorphism. -/
def implicitGraphHomeomorph {U : Set P} {V : Set Q} {f : P × Q → R} {g : P → Q}
    (hg : ContinuousOn g U) (hm : MapsTo g U V)
    (hgraph : ∀ x ∈ U, ∀ y ∈ V, f (x, y) = 0 ↔ y = g x) :
    {p : P × Q // p ∈ U ×ˢ V ∧ f p = 0} ≃ₜ U where
  toFun p := ⟨p.val.1, p.property.1.1⟩
  invFun x := ⟨(x.val, g x), ⟨⟨x.property, hm x.property⟩,
    (hgraph x x.property (g x) (hm x.property)).mpr rfl⟩⟩
  left_inv p := by
    apply Subtype.ext
    change (p.val.1, g p.val.1) = p.val
    apply Prod.ext
    · rfl
    · exact ((hgraph p.val.1 p.property.1.1 p.val.2 p.property.1.2).mp p.property.2).symm
  right_inv x := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.prodMk hg.domRestrict).subtype_mk _

/-- Near a regular zero, projection identifies the zero set homeomorphically with an
open parameter neighborhood. This retains the analytic graph and its explicit projection. -/
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
  exact ⟨U, V, hU, ha, hV, hb, hsub, implicitGraphHomeomorph hg.continuousOn hm hgraph,
    fun _ => rfl⟩

end SeveralComplexVariables
