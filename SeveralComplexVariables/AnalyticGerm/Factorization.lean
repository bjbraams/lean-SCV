/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.AnalyticGerm.Noetherian
public import SeveralComplexVariables.AnalyticGerm.Polynomial
public import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Elementary factorization of analytic germs

Jakóbczak–Jarnicki, Proposition 1.8.4: scalar analytic germ rings in finite dimension
are unique factorization domains. The pending analytic ingredient is that an
irreducible germ is prime. Together with Noetherianity this supplies Mathlib's
`UniqueFactorizationMonoid` instance and its usual existence and uniqueness results.

The source's “relatively prime” is expressed as `IsRelPrime`, meaning that common
divisors are units. It is not `IsCoprime`: two germs vanishing at the base point
cannot generate the unit ideal. No geometric conclusions from §1.8.5 are included.
-/

@[expose] public noncomputable section

namespace SeveralComplexVariables.AnalyticGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}

/-- Two germs vanishing at the base point cannot generate the unit ideal.
This does not prevent them from being relatively prime in the factorization sense. -/
theorem not_isCoprime_of_eval_eq_zero {f g : AnalyticGerm x}
    (hf : eval x f = 0) (hg : eval x g = 0) : ¬ IsCoprime f g := by
  rintro ⟨a, b, h⟩
  have he := congrArg (eval x) h
  simp [hf, hg] at he

/-- Irreducible analytic germs are prime in finite dimension. Pending proof:
induction on dimension, coordinate normalization, Weierstrass preparation, and
comparison with factorization of polynomials over the lower-dimensional germ ring. -/
theorem prime_of_irreducible [FiniteDimensional ℂ E] {f : AnalyticGerm x}
    (hf : Irreducible f) : Prime f := by
  sorry

/-- The finite-dimensional analytic germ ring is a unique factorization domain.
This instance depends on the pending Noetherian induction step and prime-germ lemma. -/
instance [FiniteDimensional ℂ E] : UniqueFactorizationMonoid (AnalyticGerm x) where
  irreducible_iff_prime := ⟨prime_of_irreducible, Prime.irreducible⟩

/-- Every nonzero analytic germ is associated to a finite product of prime germs.
The empty product accounts for units, including all nonzero zero-dimensional germs. -/
theorem exists_prime_factors [FiniteDimensional ℂ E] (f : AnalyticGerm x) (hf : f ≠ 0) :
    ∃ s : Multiset (AnalyticGerm x), (∀ p ∈ s, Prime p) ∧ Associated s.prod f :=
  UniqueFactorizationMonoid.exists_prime_factors f hf

/-- Irreducible factorizations agree up to reordering and multiplication by units. -/
theorem factors_unique [FiniteDimensional ℂ E] {s t : Multiset (AnalyticGerm x)}
    (hs : ∀ p ∈ s, Irreducible p) (ht : ∀ p ∈ t, Irreducible p)
    (h : Associated s.prod t.prod) : Multiset.Rel Associated s t :=
  UniqueFactorizationMonoid.factors_unique hs ht h

/-- Relative primality of germs means that every common divisor is a unit. -/
theorem isRelPrime_iff_common_divisors {f g : AnalyticGerm x} :
    IsRelPrime f g ↔ ∀ d, d ∣ f → d ∣ g → IsUnit d := by
  rfl

end SeveralComplexVariables.AnalyticGerm
