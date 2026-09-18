/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.Analysis.Connected
public import SeveralComplexVariables.Analysis.LinearFunctional
public import SeveralComplexVariables.Analysis.OpenMapping
public import SeveralComplexVariables.Analysis.TaylorBounds
public import SeveralComplexVariables.AnalyticGerm
public import SeveralComplexVariables.AnalyticGerm.CoefficientPolynomial
public import SeveralComplexVariables.AnalyticGerm.CoordinateChange
public import SeveralComplexVariables.AnalyticGerm.Elimination
public import SeveralComplexVariables.AnalyticGerm.Factorization
public import SeveralComplexVariables.AnalyticGerm.Fiber
public import SeveralComplexVariables.AnalyticGerm.IntrinsicOrder
public import SeveralComplexVariables.AnalyticGerm.Noetherian
public import SeveralComplexVariables.AnalyticGerm.Order
public import SeveralComplexVariables.AnalyticGerm.Polynomial
public import SeveralComplexVariables.AnalyticGerm.RelativePrimality
public import SeveralComplexVariables.AnalyticGerm.Units
public import SeveralComplexVariables.AnalyticGerm.Weierstrass
public import SeveralComplexVariables.AnalyticSet.Basic
public import SeveralComplexVariables.AnalyticSet.Codimension
public import SeveralComplexVariables.AnalyticSet.CoordinatePlane
public import SeveralComplexVariables.AnalyticSet.FunctionSpace
public import SeveralComplexVariables.AnalyticSet.Hartogs
public import SeveralComplexVariables.AnalyticSet.Holomorphic
public import SeveralComplexVariables.AnalyticSet.Regular
public import SeveralComplexVariables.AnalyticSet.Removable
public import SeveralComplexVariables.Analyticity
public import SeveralComplexVariables.BallAutomorphisms
public import SeveralComplexVariables.Biholomorphic
public import SeveralComplexVariables.BiholomorphicRigidity
public import SeveralComplexVariables.CartanThullen
public import SeveralComplexVariables.CartanUniqueness
public import SeveralComplexVariables.CauchyCoefficients
public import SeveralComplexVariables.CauchyDerivatives
public import SeveralComplexVariables.CauchyEstimates
public import SeveralComplexVariables.CauchyIntegral
public import SeveralComplexVariables.CauchyPompeiu
public import SeveralComplexVariables.CauchyRiemann
public import SeveralComplexVariables.CauchySeries
public import SeveralComplexVariables.CauchyTransform
public import SeveralComplexVariables.Circular
public import SeveralComplexVariables.CircularContinuation
public import SeveralComplexVariables.CommonExtension
public import SeveralComplexVariables.CompactHole
public import SeveralComplexVariables.ContourIntegral
public import SeveralComplexVariables.Derivatives
public import SeveralComplexVariables.DomainOfHolomorphy
public import SeveralComplexVariables.DominatedIntegral
public import SeveralComplexVariables.FunctionSpace
public import SeveralComplexVariables.FunctionSpace.Extension
public import SeveralComplexVariables.HartogsContinuation
public import SeveralComplexVariables.HartogsDomain
public import SeveralComplexVariables.HartogsExtension
public import SeveralComplexVariables.HartogsLaurent
public import SeveralComplexVariables.HartogsSeries
public import SeveralComplexVariables.HolomorphicConvexity.BoundaryDistance
public import SeveralComplexVariables.HolomorphicConvexity.Exhaustion
public import SeveralComplexVariables.HolomorphicConvexity.Hull
public import SeveralComplexVariables.HolomorphicConvexity.Thullen
public import SeveralComplexVariables.HolomorphicConvexity.Transport
public import SeveralComplexVariables.HolomorphicLp
public import SeveralComplexVariables.IdentityPrinciple
public import SeveralComplexVariables.ImplicitGraph
public import SeveralComplexVariables.ImplicitMapping
public import SeveralComplexVariables.InjectiveMapping
public import SeveralComplexVariables.InjectiveMapping.CorankOne
public import SeveralComplexVariables.InjectiveMapping.CriticalSet
public import SeveralComplexVariables.InjectiveMapping.Immersion
public import SeveralComplexVariables.InjectiveMapping.OneVariable
public import SeveralComplexVariables.Integral.Circle
public import SeveralComplexVariables.IsolatedSingularity
public import SeveralComplexVariables.LaurentApproximation
public import SeveralComplexVariables.LaurentSeries
public import SeveralComplexVariables.LaurentSeries.Annulus
public import SeveralComplexVariables.LaurentSeries.Basic
public import SeveralComplexVariables.LaurentSeries.Coefficients
public import SeveralComplexVariables.LaurentSeries.Convergence
public import SeveralComplexVariables.LaurentSeries.Iterated
public import SeveralComplexVariables.LaurentSeries.Neighborhoods
public import SeveralComplexVariables.LaurentSeries.OneVariable
public import SeveralComplexVariables.LaurentSeries.ProductCoefficients
public import SeveralComplexVariables.LaurentSeries.ProductExpansion
public import SeveralComplexVariables.LaurentSeries.Uniqueness
public import SeveralComplexVariables.LeviConvexity
public import SeveralComplexVariables.LeviConvexity.Independence
public import SeveralComplexVariables.LeviConvexity.Invariance
public import SeveralComplexVariables.LeviConvexity.Necessity
public import SeveralComplexVariables.LeviConvexity.Peak
public import SeveralComplexVariables.LeviForm
public import SeveralComplexVariables.LeviForm.Holomorphic
public import SeveralComplexVariables.LocallyBounded
public import SeveralComplexVariables.LocallyUniform
public import SeveralComplexVariables.MaximumModulus
public import SeveralComplexVariables.Montel
public import SeveralComplexVariables.Osgood
public import SeveralComplexVariables.ParametricIntegral
public import SeveralComplexVariables.Plurisubharmonic
public import SeveralComplexVariables.Polydisc
public import SeveralComplexVariables.PolydiscMeanValue
public import SeveralComplexVariables.PolydiscTaylor
public import SeveralComplexVariables.PolynomialDerivatives
public import SeveralComplexVariables.PowerSeriesConvergence
public import SeveralComplexVariables.PowerSeriesConvergence.Analytic
public import SeveralComplexVariables.PowerSeriesConvergence.Basic
public import SeveralComplexVariables.Pseudoconvexity
public import SeveralComplexVariables.RealUniqueness
public import SeveralComplexVariables.Reindex
public import SeveralComplexVariables.Reinhardt
public import SeveralComplexVariables.Reinhardt.Extension
public import SeveralComplexVariables.Reinhardt.GeometricConvexity
public import SeveralComplexVariables.Reinhardt.HolomorphicConvexity
public import SeveralComplexVariables.Reinhardt.Hull
public import SeveralComplexVariables.Reinhardt.MonomialSeparation
public import SeveralComplexVariables.Reinhardt.PartialHull
public import SeveralComplexVariables.RemovableSingularity
public import SeveralComplexVariables.RemovableSingularity.Cauchy
public import SeveralComplexVariables.RemovableSingularity.ExceptionalSet
public import SeveralComplexVariables.RemovableSingularity.Geometry
public import SeveralComplexVariables.RemovableSingularity.Gluing
public import SeveralComplexVariables.RemovableSingularity.Local
public import SeveralComplexVariables.RemovableSingularity.OneVariable
public import SeveralComplexVariables.Runge
public import SeveralComplexVariables.Runge.Examples
public import SeveralComplexVariables.SeparateAnalytic
public import SeveralComplexVariables.SeparateAnalytic.Baire
public import SeveralComplexVariables.SeparateAnalytic.FiberExtension
public import SeveralComplexVariables.SeparateAnalytic.HartogsLemma
public import SeveralComplexVariables.SeparateAnalytic.MeanValue
public import SeveralComplexVariables.SeparateAnalytic.Submean
public import SeveralComplexVariables.SphericalShell
public import SeveralComplexVariables.Subharmonic
public import SeveralComplexVariables.Subharmonic.Majorant
public import SeveralComplexVariables.Subharmonic.SmoothCriterion
public import SeveralComplexVariables.Topology.CompactExhaustion
public import SeveralComplexVariables.Topology.Frontier
public import SeveralComplexVariables.Topology.Graph
public import SeveralComplexVariables.Topology.Path
public import SeveralComplexVariables.Topology.UpperSemicontinuous
public import SeveralComplexVariables.TubeDomain
public import SeveralComplexVariables.TubeDomain.Basic
public import SeveralComplexVariables.TubeDomain.Bochner
public import SeveralComplexVariables.TubeDomain.Disc
public import SeveralComplexVariables.TubeDomain.Gluing
public import SeveralComplexVariables.TubeDomain.StarConvex
public import SeveralComplexVariables.WeierstrassDivision
public import SeveralComplexVariables.WeierstrassDivision.Basic
public import SeveralComplexVariables.WeierstrassDivision.CoordinatePower
public import SeveralComplexVariables.WeierstrassDivision.Picard
public import SeveralComplexVariables.WeierstrassPreparation
public import SeveralComplexVariables.ZeroSets
public import SeveralComplexVariables.ZeroSets.Basic
public import SeveralComplexVariables.ZeroSets.Connected
public import SeveralComplexVariables.ZeroSets.Local
public import SeveralComplexVariables.ZeroSets.Persistence

/-!
# Several complex variables

This umbrella imports the classical function theory of open subsets of finite-dimensional
complex normed spaces. Analytic maps use Mathlib's `AnalyticOnNhd ℂ`; holomorphic maps on open
sets use `DifferentiableOn ℂ`. Banach-valued targets are retained where appropriate. Finite
coordinate spaces carry the supremum norm, so their balls are polydiscs; Euclidean ball geometry
uses the inner-product norm explicitly.

## Local analysis and function spaces

The library provides polydisc Cauchy and Taylor formulas with separate radii, mixed derivative
estimates, the Cauchy–Riemann equations, the identity and maximum principles, analytic parameter
integrals, and the Cauchy–Pompeiu identity. Locally uniform convergence preserves analyticity
and derivatives. Holomorphic maps form compact-open function spaces, with continuous evaluation,
restriction, and coordinate differentiation. Montel and Vitali theorems use finite-dimensional
targets for compactness. Holomorphic `Lp` spaces are complete, including exponent infinity.

## Mapping theory and continuation

Inverse and implicit mapping theorems, regular zero-set graphs, injective holomorphic maps,
Cartan uniqueness, circular rigidity, and explicit ball automorphisms are included. Reinhardt,
circular, and Hartogs geometry support Taylor and Laurent continuation, unrestricted separate
holomorphy, and removable singularities. Hartogs' compact-hole theorem follows from Ehrenpreis'
argument with real derivatives and the Cauchy transform, without differential forms.

## Germs and analytic sets

Analytic germs form local integral domains with residue field `ℂ`. Weierstrass division and
preparation, Taylor uniqueness, coordinate-independent total order, Noetherianity, and unique
factorization support zero-set and relative-primality results. Analytic subsets have local
finite equations, interior rigidity, dense connected complements, and regular and singular loci.
The Riemann extension theorems include Banach-valued removal and the holomorphic restriction
algebra equivalence across sets of slice codimension at least two.

## Convexity, boundary geometry, and approximation

Holomorphic hulls, compact exhaustions, and escaping sequences lead to the Cartan–Thullen
equivalences on finite-dimensional complex normed spaces. Thullen's Banach-valued Taylor
continuation lemma gives the coordinate hull-radius statements and Bochner's tube theorem.
Subharmonicity and plurisubharmonicity use the local submean property; the Laplacian and Levi
form give their `C²` criteria. Domains of holomorphy are pseudoconvex and satisfy continuity
principles. Levi's necessary condition, independence of the defining function, holomorphic
supporting polynomials, normalized local peak functions, and local holomorphic blow-up are
proved. Runge pairs and domains use approximation on compact sets; polynomial hulls and
Reinhardt and circular examples are included.

The Oka–Weil theorem, the Levi sufficiency problem, and abstract envelopes of holomorphy remain
outside this library's scope. `SCVMainTheorems.md` gives the precise mathematical catalogue;
`SeveralComplexVariablesCoverage.md` records the development ledger.
-/
