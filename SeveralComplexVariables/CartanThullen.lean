/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.HolomorphicConvexity.Thullen
public import SeveralComplexVariables.HolomorphicConvexity.Exhaustion

/-!
# The Cartan–Thullen characterizations

The core equivalences relate holomorphic convexity, obstruction to common local
continuation, a single function's domain of existence, and hull boundary distance.
They apply to open subsets of finite complex coordinate spaces; connectedness is not
required. They include the empty set, the whole space, and dimension zero.

The two central analytic inputs remain pending: Thullen's Taylor continuation lemma,
and the construction here of one function detecting every continuation patch. The latter
requires a countable choice of boundary approaches and a normally convergent separating
series, not merely a function unbounded somewhere near each boundary point.

References: Range II §3.6; Fritzsche–Grauert II §§5–6; Scheidemann §7.3;
Jakóbczak–Jarnicki §2.7; Hörmander §2.5.
-/

public section

namespace SeveralComplexVariables

variable {n : ℕ} {U : Set (Fin n → ℂ)}

/-- **Existence of a completely nonextendable function.** Proof pending: construct a
normally convergent series with values tending to infinity along a sequence detecting
every possible local continuation patch. Disconnected open sets are allowed. -/
theorem IsHolomorphicallyConvex.exists_domainOfExistence
    (hU : IsHolomorphicallyConvex U) (ho : IsOpen U) :
    ∃ f : (Fin n → ℂ) → ℂ, IsDomainOfExistence U f := by
  sorry

/-- **Cartan–Thullen, reverse implication.** Depends on the pending construction of a
single function with no local continuation beyond the open set. -/
theorem IsHolomorphicallyConvex.isDomainOfHolomorphy
    (hU : IsHolomorphicallyConvex U) (ho : IsOpen U) : IsDomainOfHolomorphy U := by
  obtain ⟨f, hf⟩ := hU.exists_domainOfExistence ho
  exact hf.isDomainOfHolomorphy

/-- **Cartan–Thullen.** Holomorphic convexity is equivalent to the domain-of-holomorphy
property. Conditional on the two pending analytic inputs described in the module header. -/
theorem isDomainOfHolomorphy_iff_isHolomorphicallyConvex (ho : IsOpen U) :
    IsDomainOfHolomorphy U ↔ IsHolomorphicallyConvex U :=
  ⟨fun h => h.isHolomorphicallyConvex ho, fun h => h.isDomainOfHolomorphy ho⟩

/-- A domain of holomorphy is the domain of existence of a single scalar function.
This equivalence depends on both pending Cartan–Thullen analytic inputs. -/
theorem isDomainOfHolomorphy_iff_exists_domainOfExistence (ho : IsOpen U) :
    IsDomainOfHolomorphy U ↔ ∃ f : (Fin n → ℂ) → ℂ, IsDomainOfExistence U f :=
  ⟨fun h => (h.isHolomorphicallyConvex ho).exists_domainOfExistence ho,
    fun ⟨_, hf⟩ => hf.isDomainOfHolomorphy⟩

/-- Exact preservation of compact hull boundary distance characterizes domains of
holomorphy. This equivalence depends on the pending Cartan–Thullen inputs. -/
theorem isDomainOfHolomorphy_iff_hullDistanceProperty (ho : IsOpen U) :
    IsDomainOfHolomorphy U ↔ HasHolomorphicHullDistanceProperty U :=
  ⟨fun h => h.hullDistanceProperty ho,
    fun h => (h.isHolomorphicallyConvex ho).isDomainOfHolomorphy ho⟩

/-- The uniform polydisc-radius formulation is another Cartan–Thullen characterization,
conditional on the same pending analytic inputs. -/
theorem isDomainOfHolomorphy_iff_hullRadiusProperty (ho : IsOpen U) :
    IsDomainOfHolomorphy U ↔ HasHolomorphicHullRadiusProperty U :=
  ⟨fun h => h.hullRadiusProperty ho,
    fun h => (h.isHolomorphicallyConvex ho).isDomainOfHolomorphy ho⟩

/-- Convex open coordinate domains are holomorphically convex. This deduction uses the
proved separating-hyperplane example and the pending Thullen lemma. -/
theorem isHolomorphicallyConvex_of_convex (hU : Convex ℝ U) (ho : IsOpen U) :
    IsHolomorphicallyConvex U := (isDomainOfHolomorphy_of_convex hU ho).isHolomorphicallyConvex ho

end SeveralComplexVariables
