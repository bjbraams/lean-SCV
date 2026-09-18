/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.Analyticity

/-!
# The identity theorem for holomorphic functions in several variables

Holomorphic maps on a preconnected open subset of a finite-dimensional complex normed
space agree everywhere if they agree near one point, equivalently on a nonempty open
subset. The target may be a complex Banach space. The proofs use the project's
holomorphic–analytic equivalence and Mathlib's analytic identity principle.

`identity_theorem` is Fritzsche–Grauert (2002), I.4.10, p. 22, with Banach-valued targets.
`identity_theorem_pi` makes the specialization to finite complex coordinate spaces explicit.
Empty coordinate types are allowed. The agreement set must be nonempty; agreement merely
on a set with a cluster point does not suffice in several variables.
-/

public section

open Set Filter
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The holomorphic identity principle from equality near one point of an open,
preconnected set. The target may be any complex Banach space. -/
theorem eqOn_of_holomorphic_of_eventuallyEq {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected U) {f g : E → F}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {a : E} (ha : a ∈ U) (heq : f =ᶠ[𝓝 a] g) : EqOn f g U :=
  (hf.analyticOnNhd_finiteDimensional hU).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd_finiteDimensional hU) hconn ha heq

/-- **Identity theorem (Fritzsche–Grauert I.4.10).** Two holomorphic maps on an open,
preconnected set agree everywhere if they agree on a nonempty open subset. -/
theorem identity_theorem {U V : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {f g : E → F} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) (heq : EqOn f g V) :
    EqOn f g U := by
  obtain ⟨a, ha⟩ := hne
  exact eqOn_of_holomorphic_of_eventuallyEq hU hconn hf hg (hVU ha)
    (Filter.mem_of_superset (hV.mem_nhds ha) (fun _ hx => heq hx))

/-- A holomorphic map vanishing on a nonempty open subset vanishes throughout the
open, preconnected domain. -/
theorem identity_theorem_zero {U V : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {f : E → F} (hf : DifferentiableOn ℂ f U)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) (heq : EqOn f 0 V) :
    EqOn f 0 U :=
  identity_theorem hU hconn hf (differentiableOn_const 0) hV hne hVU heq

/-- The identity theorem on `ι → ℂ`, in particular on `Fin n → ℂ`. This includes
zero-dimensional coordinate spaces and retains complex Banach-valued targets. -/
theorem identity_theorem_pi {ι : Type*} [Fintype ι] {U V : Set (ι → ℂ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) {f g : (ι → ℂ) → F}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) (heq : EqOn f g V) :
    EqOn f g U :=
  identity_theorem hU hconn hf hg hV hne hVU heq

end SeveralComplexVariables
