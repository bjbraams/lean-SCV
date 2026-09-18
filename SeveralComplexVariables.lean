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
public import SeveralComplexVariables.Analyticity
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
public import SeveralComplexVariables.CauchyPompeiu
public import SeveralComplexVariables.CauchyTransform
public import SeveralComplexVariables.CompactHole
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
public import SeveralComplexVariables.Subharmonic
public import SeveralComplexVariables.Subharmonic.Majorant
public import SeveralComplexVariables.Subharmonic.SmoothCriterion
public import SeveralComplexVariables.Plurisubharmonic
public import SeveralComplexVariables.LeviForm
public import SeveralComplexVariables.Pseudoconvexity
public import SeveralComplexVariables.LeviForm.Holomorphic
public import SeveralComplexVariables.LeviConvexity
public import SeveralComplexVariables.LeviConvexity.Necessity
public import SeveralComplexVariables.LeviConvexity.Invariance
public import SeveralComplexVariables.LeviConvexity.Independence
public import SeveralComplexVariables.LeviConvexity.Peak
public import SeveralComplexVariables.Runge
public import SeveralComplexVariables.Runge.Examples
public import SeveralComplexVariables.TubeDomain
public import SeveralComplexVariables.TubeDomain.Basic
public import SeveralComplexVariables.TubeDomain.Disc
public import SeveralComplexVariables.TubeDomain.Gluing
public import SeveralComplexVariables.TubeDomain.StarConvex
public import SeveralComplexVariables.TubeDomain.Bochner
public import SeveralComplexVariables.HolomorphicConvexity.ThullenBanach
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
public import SeveralComplexVariables.PolydiscMeanValue
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
criterion. Taylor series preserve multiplication, giving the order product rule.
Coordinate invariance and exact-order normalization remain pending. Polynomial
Weierstrass interfaces are proved. Nearby relative primality is pending, with openness derived from it.
Riemann extension across scalar zero sets and locally contained relatively closed exceptional
sets is proved for Banach-valued functions, together with uniqueness and connectedness of
the complement. Elementary polynomial comparison, Noetherianity and unique factorization in
finite dimension are proved.
Normalization of distinguished-polynomial factors is proved by reduction modulo the maximal ideal.
The Noetherian and unique-factorization instances have complete proofs.
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
circular-domain linearity is conditional on Cartan uniqueness. Ball–polydisc inequivalence
is proved independently of Cartan uniqueness. Explicit ball
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
single completely nonextendable function. Bochner's Banach-valued tube extension is proved by
Hörmander's argument: a Banach-valued Thullen continuation lemma, hull membership of parabolic
analytic discs by the planar maximum principle, gluing of local continuations along convex
sets, convexity of the maximal star-convex extension tube, and a path argument for connected
bases; tube geometry, uniqueness and the domain-of-holomorphy characterization follow. Subharmonic and plurisubharmonic functions use the local submean
definition; the Levi form gives the `C²` criterion; on domains of holomorphy the negative
logarithm of the boundary distance is plurisubharmonic, giving pseudoconvexity, the affine
continuity principle and Hartogs convexity for cylinder figures. Levi convex boundaries use
local `C²` defining functions and the Levi condition for every defining function; convex open
sets and domains of holomorphy in `ℂⁿ` with `C²` boundary are proved Levi pseudoconvex. The Levi
form obeys the chain rule under holomorphic maps, so `C²` plurisubharmonic functions compose
with holomorphic maps and the Levi condition is invariant under local biholomorphisms; domains
of holomorphy satisfy the continuity principle for holomorphic disc families. Two defining
functions have positively proportional first derivatives and tangential second derivatives, so
the Levi condition is checked on one defining function; at strictly Levi convex boundary points
the Levi polynomial is a local peak function. Runge pairs and Runge domains are defined by
approximation on compact sets, equivalently by locally uniform sequences on open sets; the
polynomial hull of a compact set is compact and agrees with its entire hull, a Runge domain
forms a Runge pair with the whole space, its polynomial hulls meet it in the holomorphic hulls,
and complete Reinhardt and circular open sets containing the origin are Runge domains, with
transport under polynomial automorphisms. The Oka–Weil theorem is not included.
Hartogs geometry separates fiber symmetry, completeness and fiber preconnectedness.
Banach-valued Hartogs–Taylor expansion is proved with holomorphic coefficients and locally
uniform convergence. Hartogs–Laurent expansion remains pending; its statement requires
preconnected fibers for global coefficients on the base.
Hartogs continuation over connected bases and punctured-polydisc removal are proved without
boundedness assumptions. Removal at arbitrary isolated points and absence of isolated scalar
zeros are proved. Hartogs' compact-hole extension theorem is proved by Ehrenpreis' method, from
the Cauchy–Pompeiu identity in polar coordinates and the Cauchy transform in one variable with
parameters; finite shells and exteriors of closed balls extend by it. Unrestricted separate
analyticity and Cartan uniqueness are proved.
Analytic Weierstrass division is proved on fixed polydiscs with a uniform quotient bound;
coordinate-power division and its estimate are also proved.
Local division, preparation with uniqueness, and their analytic-germ identities are derived
from the general division statement. Degree zero and empty parameter types are included.
See `SeveralComplexVariablesCoverage.md` for the Mathlib inventory, proved textbook
coverage, and remaining work.
-/
