/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.RealUniqueness
public import SeveralComplexVariables.AnalyticGerm
public import SeveralComplexVariables.AnalyticSet
public import SeveralComplexVariables.AnalyticGerm.CoordinateChange
public import SeveralComplexVariables.AnalyticGerm.Polynomial
public import SeveralComplexVariables.AnalyticGerm.Noetherian
public import SeveralComplexVariables.AnalyticGerm.Factorization
public import SeveralComplexVariables.AnalyticGerm.Order
public import SeveralComplexVariables.AnalyticGerm.Units
public import SeveralComplexVariables.AnalyticGerm.Weierstrass
public import SeveralComplexVariables.AnalyticGerm.RelativePrimality
public import SeveralComplexVariables.Basic
public import SeveralComplexVariables.Biholomorphic
public import SeveralComplexVariables.CartanUniqueness
public import SeveralComplexVariables.Circular
public import SeveralComplexVariables.CircularContinuation
public import SeveralComplexVariables.BiholomorphicRigidity
public import SeveralComplexVariables.FunctionSpace.Extension
public import SeveralComplexVariables.LaurentApproximation
public import SeveralComplexVariables.ImplicitGraph
public import SeveralComplexVariables.InjectiveMapping
public import SeveralComplexVariables.BallAutomorphisms
public import SeveralComplexVariables.IsolatedSingularity
public import SeveralComplexVariables.Reinhardt.PartialHull
public import SeveralComplexVariables.CauchyCoefficients
public import SeveralComplexVariables.CauchyDerivatives
public import SeveralComplexVariables.CauchyEstimates
public import SeveralComplexVariables.CauchyIntegral
public import SeveralComplexVariables.CauchyRiemann
public import SeveralComplexVariables.CauchySeries
public import SeveralComplexVariables.ContourIntegral
public import SeveralComplexVariables.CommonExtension
public import SeveralComplexVariables.DomainOfHolomorphy
public import SeveralComplexVariables.HolomorphicConvexity.Hull
public import SeveralComplexVariables.HolomorphicConvexity.Maps
public import SeveralComplexVariables.HolomorphicConvexity.Exhaustion
public import SeveralComplexVariables.HolomorphicConvexity.BoundaryDistance
public import SeveralComplexVariables.HolomorphicConvexity.Thullen
public import SeveralComplexVariables.CartanThullen
public import SeveralComplexVariables.TubeDomain
public import SeveralComplexVariables.LaurentSeries
public import SeveralComplexVariables.Derivatives
public import SeveralComplexVariables.PolynomialDerivatives
public import SeveralComplexVariables.DominatedIntegral
public import SeveralComplexVariables.FunctionSpace
public import SeveralComplexVariables.Hartogs
public import SeveralComplexVariables.HolomorphicLp
public import SeveralComplexVariables.IdentityPrinciple
public import SeveralComplexVariables.ImplicitMapping
public import SeveralComplexVariables.LocallyBounded
public import SeveralComplexVariables.LocallyUniform
public import SeveralComplexVariables.MaximumModulus
public import SeveralComplexVariables.Montel
public import SeveralComplexVariables.Osgood
public import SeveralComplexVariables.ParametricIntegral
public import SeveralComplexVariables.Polydisc
public import SeveralComplexVariables.PowerSeriesConvergence
public import SeveralComplexVariables.PowerSeriesConvergence.Analytic
public import SeveralComplexVariables.PolydiscTaylor
public import SeveralComplexVariables.Reindex
public import SeveralComplexVariables.Reinhardt
public import SeveralComplexVariables.Reinhardt.Extension
public import SeveralComplexVariables.RemovableSingularity
public import SeveralComplexVariables.RemovableSingularity.ExceptionalSet
public import SeveralComplexVariables.WeierstrassDivision
public import SeveralComplexVariables.WeierstrassPreparation
public import SeveralComplexVariables.ZeroSets
public import SeveralComplexVariables.ZeroSets.Connected

/-!
# Several-complex-variables infrastructure

This umbrella imports finite-dimensional complex analyticity, polydisc Cauchy formulas and
series, locally bounded Osgood, coordinate derivatives and Cauchy–Riemann equations, locally
uniform limits and their derivatives, compact-open holomorphic function spaces, Montel's and Vitali's theorems,
and analytic parameter-dependent integrals. Taylor coefficients, convergence and remainder
estimates allow separate radii in each coordinate. Scalar analytic germs form a local integral
domain, with residue field `ℂ` and pullback along analytic maps.
Analytic coordinate changes give germ-ring isomorphisms; finite-family linear normalization
and roots of unit germs are proved. Total germ order uses Mathlib multivariate Taylor-series
order, with proved zero-order and sum rules, Taylor uniqueness, and the infinite-order
criterion. Order multiplication,
coordinate invariance, exact-order normalization, and three polynomial Weierstrass
interfaces are pending. Nearby relative primality is pending, with openness derived from it.
Riemann extension across scalar zero sets and locally contained relatively closed exceptional
sets is proved for Banach-valued functions, together with uniqueness and connectedness of
the complement. Elementary polynomial comparison, Noetherianity and unique factorization in
finite dimension are included, with five explicitly pending algebraic/analytic lemmas.
Normalization of distinguished-polynomial factors is proved by reduction modulo the maximal ideal.
The Noetherian and unique-factorization instances depend on these pending proofs.
Continuous removal across countable sets and density of nonvanishing loci are proved.
The holomorphic identity theorem and the maximum modulus principle from an interior local
maximum are provided explicitly, with specializations to finite complex coordinate spaces.
Holomorphic Lp spaces are submodules of Lebesgue Lp, with unique holomorphic representatives.
Their closedness and Banach completeness, and Hilbert completeness at exponent two, depend
on one explicitly pending local Lp estimate.
Biholomorphic maps, the holomorphic inverse and implicit mapping theorems, derivative
formulas, determinant criteria and local injectivity from an injective derivative are proved.
Regular local zero sets are homeomorphic to their parameter neighborhoods by projection.
Analytic subsets have local finite equations, proved closure properties, interior rigidity,
dense connected complements, and locally bounded Banach-valued removal. Regular and singular
loci are defined intrinsically, with relative openness and closedness proved. Full-rank
flattening is proved; regular-point existence on nonempty hypersurfaces remains pending. Nonsingularity
of injective holomorphic maps in equal dimensions is pending; biholomorphy onto the open image
is derived from it. Slice codimension supplies dimension bounds and empty interior. Removal
across coordinate subspaces of codimension two is proved directly by Hartogs continuation.
General codimension-two removal and the holomorphic restriction algebra equivalence depend
on one pending automatic-local-boundedness theorem; uniqueness is proved independently.
Circular symmetry reuses Mathlib's balanced hull; homogeneous expansion and continuation to
that hull are pending, while homogeneity and uniqueness of extension are proved.
Partial Reinhardt hulls have proved minimality, openness, monotonicity and idempotence;
their mixed Taylor–Laurent extension theorem is pending. Finite Laurent approximation is
derived from Laurent expansion; continuous coefficient projections remain pending.
Restriction operators and scalar holomorphic algebras are constructed. Continuity of inverse
restriction uses a pending Fréchet open-mapping step. First-jet rigidity reduces to Cartan;
circular-domain linearity and ball–polydisc inequivalence remain pending. Explicit ball
involutions, their metric identity, and transitivity of ball automorphisms are proved.
Reinhardt and complete Reinhardt sets provide coordinate geometry independently of openness;
nonempty complete Reinhardt sets are path connected, and origin-centred polydiscs are examples.
Geometric logarithmic convexity includes zero coordinates and agrees with positive-logarithmic
convexity on open complete Reinhardt sets. Geometric and Reinhardt hulls have proved minimality
properties. Power-series convergence domains are complete Reinhardt and geometrically convex
in moduli; arbitrary Banach-valued series converge locally uniformly and have analytic sums.
Taylor extension from complete Reinhardt domains to their logarithmic hulls is proved.
The converse scalar existence theorem remains pending. Multivariable Laurent expansion is
pending; its consequences include hull extension for domains meeting each coordinate hyperplane.
Openness of the logarithmic hull and its inclusion of the complete hull for open Reinhardt
sets containing zero are proved. Common extension domains preserve scalar ranges
and lie in the real convex hull of the original domain.
Holomorphic hulls have proved closure, boundedness, separation, product, and biholomorphic
transport properties. Holomorphically convex open sets admit compact exhaustions by sets
fixed by their hulls. The escaping-sequence characterization remains pending. Domains of
holomorphy and domains of existence use local continuation through a nonempty open overlap;
planar and real-convex open domains are proved examples. Extended boundary distance handles
empty sets and the whole ambient space. Cartan–Thullen equivalences are deduced from two
pending analytic inputs: Thullen's Taylor continuation lemma and the construction of a
single completely nonextendable function. Bochner's Banach-valued tube extension is pending;
tube geometry and uniqueness are proved, and its domain-of-holomorphy characterization is
conditional on extension.
Hartogs geometry separates fiber symmetry, completeness and fiber preconnectedness.
Banach-valued Hartogs–Taylor and Hartogs–Laurent expansions are explicitly pending targets;
the Laurent statement requires preconnected fibers for global coefficients on the base.
Hartogs continuation over connected bases and punctured-polydisc removal are proved without
boundedness assumptions. Removal at arbitrary isolated points and absence of isolated scalar
zeros are proved. Finite shells and exteriors of closed balls extend by the pending compact-hole
theorem. Unrestricted separate analyticity and Cartan uniqueness remain pending.
Analytic Weierstrass division is stated on fixed polydiscs with a uniform quotient bound;
coordinate-power division with its estimate and general division are pending proofs.
Local division, preparation with uniqueness, and their analytic-germ identities are derived
from the general division statement. Degree zero and empty parameter types are included.
See `SeveralComplexVariablesCoverage.md` for the Mathlib inventory, proved textbook
coverage, and remaining work.
-/
