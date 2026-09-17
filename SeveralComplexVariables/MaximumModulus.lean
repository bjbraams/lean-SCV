/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.IdentityPrinciple
public import Mathlib.Analysis.Complex.AbsMax

/-!
# The maximum modulus principle in several variables

If the modulus of a scalar holomorphic function on an open, preconnected set has a local
maximum at an interior point, then the function is constant on the set. This is
Fritzsche–Grauert (2002), I.4.11, p. 22. A local maximum suffices; a maximum over the whole
domain is not required. The proof combines Mathlib's local maximum modulus principle
with the holomorphic identity theorem.

The source is any finite-dimensional complex normed space, including `ι → ℂ` for any finite
index type (also empty). The supporting norm theorem permits strictly convex complex Banach
targets. Strict convexity cannot be dropped for constancy of the map: on the unit disc,
`z ↦ (1, z)` is nonconstant but has constant supremum norm.
-/

public section

open Set Filter Function
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A holomorphic map into a strictly convex complex Banach space is constant on an
open, preconnected domain if its norm has a local maximum at an interior point. -/
theorem eqOn_const_of_holomorphic_of_isLocalMax_norm
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [StrictConvexSpace ℝ F] {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) {a : E} (ha : a ∈ U)
    (hmax : IsLocalMax (norm ∘ f) a) : EqOn f (const E (f a)) U :=
  eqOn_of_holomorphic_of_eventuallyEq hU hconn hf (differentiableOn_const (f a)) ha
    (Complex.eventually_eq_of_isLocalMax_norm
      (hf.eventually_differentiableAt (hU.mem_nhds ha)) hmax)

/-- **Maximum principle (Fritzsche–Grauert I.4.11).** A scalar holomorphic function
on an open, preconnected domain whose modulus has a local maximum is constant. -/
theorem maximum_modulus_principle {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected U) {f : E → ℂ} (hf : DifferentiableOn ℂ f U)
    {a : E} (ha : a ∈ U) (hmax : IsLocalMax (norm ∘ f) a) :
    EqOn f (const E (f a)) U :=
  eqOn_const_of_holomorphic_of_isLocalMax_norm hU hconn hf ha hmax

/-- The maximum principle with the local maximum expressed relative to the domain.
Since the point is interior, this agrees with the ambient local-maximum formulation. -/
theorem maximum_modulus_principle_on {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected U) {f : E → ℂ} (hf : DifferentiableOn ℂ f U)
    {a : E} (ha : a ∈ U) (hmax : IsLocalMaxOn (norm ∘ f) U a) :
    EqOn f (const E (f a)) U :=
  maximum_modulus_principle hU hconn hf ha (hmax.isLocalMax (hU.mem_nhds ha))

/-- The scalar maximum principle on `ι → ℂ`, in particular on `Fin n → ℂ`.
No positive dimension assumption is required. -/
theorem maximum_modulus_principle_pi {ι : Type*} [Fintype ι] {U : Set (ι → ℂ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) {f : (ι → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f U) {a : ι → ℂ} (ha : a ∈ U)
    (hmax : IsLocalMax (norm ∘ f) a) : EqOn f (const (ι → ℂ) (f a)) U :=
  maximum_modulus_principle hU hconn hf ha hmax

end SeveralComplexVariables
