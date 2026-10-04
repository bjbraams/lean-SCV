# TauCeti reuse review — 4 October 2026

TauCeti is now an explicit dependency of lean-SCV. The preference is **Mathlib, then the
pinned TauCeti, then local project code**, with hypotheses and conclusions preserved.
The four concrete replacements below have now been implemented, preserving their theorem
statements and assumptions. Most of the several-variable
library still supplies theory not supplied by the inspected TauCeti modules.

This review inventories all 133 files in `SeveralComplexVariables`, 20 copied files in
`ComplexAnalysis`, and 18 files in `ToMathlib` (including its three umbrellas). Module and
declaration searches covered that inventory and the pinned TauCeti source tree; promising
matches received statement/proof inspection and the four candidates below received compile
checks. This is a reuse review, not a new line-by-line audit of every existing proof or an
exhaustive proof that no alternative formulation exists upstream. Findings refer to the pinned
sources, not to TauCeti's latest branch or unfinished roadmap projects.

## Dependency setup and policy

- Lean: `v4.35.0-rc3`.
- Mathlib: `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`.
- TauCeti: [`a780c7ad6beb23f60a17351a492d177878020ad5`][tau].
- `lakefile.toml` and `lake-manifest.json` register TauCeti directly. Existing dependency
  revisions and the toolchain are unchanged from the start of this review.
- `.lake` remains the shared local-disk symlink. SCV outputs remain in `.lake/build-SCV`.
- Import the particular module providing a result. `import TauCeti` is not a library umbrella.
- `AGENTS.md` now permits suitable TauCeti imports in each layer, states the reuse hierarchy,
  requires attribution at use, and preserves the shared-source rules.

All 20 copied `ComplexAnalysis` files and all six shared `ToMathlib` implementation files
currently match lean-CA byte for byte. The three project-specific `ToMathlib` umbrellas are
exempt from synchronization. Shared proof changes must originate in lean-CA and be copied here,
with both projects checked. All four replacements below are now installed. The two shared
modules were changed in lean-CA first and copied here. A transitive import-graph check confirms
that all 20 `ComplexAnalysis` files here are used by the SCV library; none needed to be removed
or added.

## Implemented replacements

### 1. Injectivity implies nonzero derivative — coordinate with lean-CA

[ComplexAnalysis/Injective.lean](ComplexAnalysis/Injective.lean) proves
`Complex.deriv_ne_zero_of_injOn` by constructing an inverse and removing its singularity.
TauCeti exports the same conclusion and hypotheses as `TauCeti.deriv_ne_zero_of_injOn` in
[Conformal.LocalDegree][tau-degree]. The existing statement has the checked replacement:

```lean
  TauCeti.deriv_ne_zero_of_injOn hf hU hi ha
```

The direct SCV consumer is
[InjectiveMapping/CorankOne.lean](SeveralComplexVariables/InjectiveMapping/CorankOne.lean).
This implements the shared injectivity replacement deferred in the lean-CA review. The local
interface is preserved. The derivative-vanishing helper was removed after checking both projects.
The nonconstancy helper remains because lean-CA's `HolomorphicInverse` and
`UnivalentDisk.Geometry` still use it. The logarithmic-derivative circle-integral lemmas and
the higher-dimensional injective-mapping proof remain local.

### 2. Connectedness of the exterior of a closed ball — SCV-local change

[ToMathlib/Analysis/Connected.lean](ToMathlib/Analysis/Connected.lean) contains
`isPreconnected_compl_closedBall`. [Ball.Exterior][tau-exterior] supplies
`TauCeti.isPreconnected_compl_closedBall` with the same real normed-space assumptions,
`1 < Module.rank ℝ E`, arbitrary center, and arbitrary real radius. The checked adapter is:

```lean
  TauCeti.isPreconnected_compl_closedBall hdim c ρ
```

This replaces the local exterior proof and removes its private zero-centered exterior helper.
The annulus preconnectedness and path-connectedness results and their radial helper remain: they have
separate uses and are not replaced by the exterior theorem. In particular, preserve empty
annuli and negative radii. [SphericalShell.lean](SeveralComplexVariables/SphericalShell.lean)
uses both the annulus and exterior results. This support file is not shared with lean-CA.

### 3. Laplacian of squared distance — coordinate with lean-CA

[Subharmonic/SmoothCriterion.lean](ComplexAnalysis/Subharmonic/SmoothCriterion.lean) contains
`Complex.laplacian_normSq_sub`, currently a direct two-derivative calculation.
[Laplacian.Basic][tau-laplacian] supplies `TauCeti.laplacian_norm_sq` in every finite-dimensional
real inner product space and `TauCeti.laplacian_comp_add_right` for translations. Together they
prove the existing statement `Δ (fun z : ℂ ↦ ‖z - a‖ ^ 2) t = 4` with no added assumptions.
The adapter was compiled successfully.

The calculation has been replaced in lean-CA and synchronized to SCV. The surrounding
submean and smooth-criterion development remains local. TauCeti's smooth maximum principles do not replace
the project's upper-semicontinuous, locally submean definition of `SubharmonicOn`.

### 4. Local biholomorphic inverse — SCV-local simplification

[SeveralComplexVariables/Biholomorphic.lean](SeveralComplexVariables/Biholomorphic.lean)
proves `exists_biholomorphic_of_isInvertible_fderiv` by shrinking a Mathlib inverse chart until
its inverse is analytic throughout the target. TauCeti's
`TauCeti.ContDiffOn.exists_openPartialHomeomorph` in
[Calculus.InverseFunctionTheorem][tau-inverse] already supplies such a chart with a `C^n`
inverse on its whole target.

The installed adapter uses the existing finite-dimensional holomorphy-to-analyticity theorem,
then `AnalyticOnNhd.contDiffOn hU.uniqueDiffOn` at regularity `ω`, invokes TauCeti, and packages
forward and inverse differentiability as `IsBiholomorphic`. The source restriction, membership
of the base point, and global equality of the forward representative to the original function
are preserved. No assumptions are strengthened, including in dimension zero.

Keep the project's general `IsBiholomorphic` predicate and its algebra/derivative API. TauCeti's
conformal `Biholomorph` packaging is for maps `ℂ → ℂ`, and does not replace this SCV structure.
The existing implicit mapping theorem already invokes Mathlib at regularity `ω`; the additional
TauCeti complemented-kernel machinery is not needed there.

## Inventory of the remaining theory

| Project area | Assessment at this pin |
| --- | --- |
| `Analyticity`, `IdentityPrinciple`, `MaximumModulus`, `RealUniqueness`, `Derivatives`, `PolynomialDerivatives`, `Reindex` | Retain the finite-dimensional-source and Banach/normed-target interfaces. TauCeti's isolated-zero and analytic-order results concern a one-dimensional scalar source; their names alone do not identify replacements. |
| `Polydisc`, `CauchyIntegral`, `CauchyCoefficients`, `CauchySeries`, `CauchyEstimates`, `PolydiscTaylor`, `PolydiscMeanValue`, `PowerSeriesConvergence/*` | Retain the polydisc and multivariate expansion theory. TauCeti's one-variable normal-family estimates are useful inputs for future scalar slices, but no replacement of the present multivariate theorems was identified. |
| `LocallyUniform`, `FunctionSpace/*`, `Montel`, `HolomorphicLp`, shared `Holomorphic/*` support | Retain higher-dimensional Weierstrass convergence, compact-open spaces, continuous coordinate differentiation, and SCV Montel/Vitali. TauCeti's Montel allows vector targets but still fixes the source to `ℂ`. Its Vitali uniqueness-set criterion is one-variable; the SCV nonempty-open-set criterion must be preserved. Its `IsLocallyBoundedOn` predicate has an arbitrary topological source and could abbreviate repeated bounds, but that would be optional API cleanup rather than a proof replacement. |
| `Biholomorphic`, `ImplicitMapping`, `ImplicitGraph`, `InjectiveMapping/*` | Replacements 1 and 4 are implemented. Retain the Banach analytic implicit mapping theorem, graph packaging, and higher-dimensional injectivity/immersion arguments. Mathlib already supplies the implicit-function and graph tools used here. |
| `CartanUniqueness`, `BiholomorphicRigidity`, `BallAutomorphisms` | Retain: these include higher-dimensional rigidity and ball/polydisc distinctions. TauCeti's unit-disc automorphisms and Schwarz–Pick theory do not replace them. |
| `LocallyBounded`, `Osgood`, `SeparateAnalytic/*`, `HartogsSeries` | Retain the separately holomorphic and Baire arguments. No matching unrestricted SCV separate-holomorphy theorem was located in TauCeti. |
| `Reinhardt/*`, `Circular`, `CircularContinuation`, `HartogsContinuation`, `CommonExtension`, `LaurentSeries/*`, `LaurentApproximation`, `HartogsLaurent`, `HartogsDomain` | Retain multivariate continuation and convergent Laurent expansions. TauCeti's meromorphic Laurent data describe scalar finite principal parts near a point, not Banach-valued annular or Reinhardt-domain expansions. |
| `RemovableSingularity/*`, `IsolatedSingularity`, `HartogsExtension`, `CompactHole`, `SphericalShell` | Replacement 2 updates the supporting exterior lemma. Retain Hartogs/removability and compact-hole proofs. TauCeti's conformal removability results treat planar scalar functions and particular exceptional sets, not this SCV extension theory. |
| `ZeroSets/*`, `AnalyticSet/*` | Retain. One-variable isolated-zero counting does not replace higher-dimensional zero loci, regularity, isolated slices, or extension across analytic sets. |
| `AnalyticGerm/*`, `WeierstrassDivision/*`, `WeierstrassPreparation` | Retain convergent complex germ algebra and analytic division/preparation. TauCeti's `RingTheory.PowerSeries.Weierstrass` existence theorems require a complete nonarchimedean coefficient field. They cannot be specialized to the usual norm on `ℂ`. Its planar holomorphic sheaf/continuation API is likewise not this multivariate local-ring interface. |
| `DomainOfHolomorphy`, `HolomorphicConvexity/*`, `CartanThullen`, `TubeDomain/*` | Retain. No matching Cartan–Thullen, Thullen extension, or Bochner tube theorem was located. TauCeti's planar filled-hull results do not supply several-variable holomorphic convexity. |
| `Plurisubharmonic`, `Pseudoconvexity`, `LeviForm/*`, `LeviConvexity/*` | Retain. Replacement 3 simplifies shared support only. Smooth real Laplacian estimates and harmonic mean-value theorems do not replace complex-line subharmonicity, the Levi form, defining-function independence, or Levi's necessary condition. |
| `Runge/*` | Retain polynomial hulls, Runge pairs/domains, and examples. TauCeti's contour homology is possible infrastructure for later one-variable approximation, not a checked replacement of these results or an Oka–Weil theorem. The current deferred scope is unchanged. |
| `ContourIntegral`, `CauchyRiemann`, `DominatedIntegral`, `ParametricIntegral` | Retain iterated circle integrals and Banach-valued parameter differentiation. TauCeti's contour API uses a different path representation and many principal formulas are scalar; its compact-interval smooth parameter integration is not the current dominated holomorphic-parameter statement. |

### Copied one-variable and general support

The one-variable `Injective` and `Subharmonic/SmoothCriterion` replacements are described above.
Keep `CauchyDerivatives`, `CauchySeries`, `CauchyEstimates`, the three `LaurentSeries` files,
`LocallyUniform`, `ParametricIntegral`, `RealUniqueness`, and `RemovableSingularity` where they
supply Banach-valued, arbitrary-filter, or annular interfaces not supplied by the inspected
TauCeti counterparts. `CauchyPompeiu` and `CauchyTransform` provide the parameter-dependent
`∂̄` solution used in compact-hole extension; no matching replacement was located.

Keep the remaining subharmonic files and `Integral/Circle`: TauCeti's harmonic and smooth
Laplacian theory is adjacent but does not establish the nonsmooth statements. `ZeroPersistence`
works with differentiability on a closed disc and topological parameters. TauCeti's Rouché
statements use analyticity on a neighborhood of that disc, so they are not a direct
same-hypothesis replacement of the boundary-norm lemma. A later refactor of individual callers
could be assessed separately.

For `ToMathlib`, replacement 2 concerns `Analysis/Connected` only. The following were also screened:

- `Analysis/OpenMapping`: TauCeti's Henkel theorem requires a nonarchimedean additive source;
  it does not replace this complete metrizable complex-vector-space theorem. Continue tracking
  the separate Mathlib open-mapping work discussed previously.
- `Analysis/Holomorphic/{FunctionSpace,LocallyUniformLimit,NormalFamily}`: preserve shared
  general-source APIs, as above. A planar Montel replacement does not remove this SCV dependency.
- `Analysis/TaylorBounds`: preserves a vector-valued uniform second-order remainder in
  arbitrary real normed spaces. TauCeti's scalar Taylor remainder-sign and integral-remainder
  results are not direct replacements.
- `Analysis/Integral/CompactSupport`: no matching replacement of its current generic
  integrability interfaces was identified.
- `Topology/{Frontier,Path,SeparateContinuous,Baire/Bounded,MetricSpace/Pi,Order/IntermediateValue}`:
  no direct replacement identified. TauCeti's frontier-straddling lemma gives a frontier
  intersection, not the first-exit time and the prefix staying inside required here.
- `Algebra/{Polynomial/OfFn,LinearMap/Ordered}`: no direct replacement identified for the
  polynomial-vector reconstruction or positive proportionality lemmas.

The Riemann-mapping, Hurwitz, and ambient one-variable Montel modules recently simplified in
lean-CA are absent from SCV's copied subset. They therefore require no corresponding migration
here. Of the other deferred CA themes, injectivity is the immediate shared dependency; its
Schwarz–Pick, Harnack, reflection, and half-plane modules are not copied into SCV.

## Initial review validation

The following checks record the dependency-setup review before production proof replacements.
The implementation validation is recorded below.

- `lake update TauCeti`: passed; only TauCeti was added to the starting manifest's package set,
  with every existing dependency revision preserved.
- `lake build > /tmp/SCV-build.log 2>&1`: passed, 3,491 jobs.
- `lake build Challenge Solution`: passed, 9,131 jobs; the existing 67 intentional
  `Challenge.lean` placeholders were reported.
- `lake build ToMathlib`: passed, 2,869 jobs; the support umbrellas are checked separately
  from the main SCV target.
- `git diff --check`: passed.
- The four candidate TauCeti modules build. A temporary file outside the repository imports
  the full SCV library together with them and proves adapters for all four existing interfaces.
  `lake env lean /tmp/SCVTauCetiReview.lean` passes; each adapter's `#print axioms` lists only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Shared-source comparison passes for all 20 CA copies and six shared support implementations.
- All project Lean sources are unchanged during this review. No existing theorem was modified,
  no assumptions changed, and no false theorem was identified. The only project `sorry`s remain
  the 67 intentional Challenge placeholders. No full export-comparator replay was performed.

## Implementation validation

The four production theorems now import the Tau Ceti contributors' proofs, with attribution
in their module headers and declaration docstrings. Their statements and assumptions match
the pre-change sources. Only the two unused helpers identified above were removed. All other
implementation Lean files are unchanged from the start of this implementation batch.

The shared-source check confirms byte-for-byte agreement for all 20 `ComplexAnalysis` copies
and six shared `ToMathlib` implementations. Every copied CA module is transitively reachable
from `SeveralComplexVariables.lean`; the differing project-specific umbrellas remain exempt.
No dependency pins or build-directory settings were changed.

Validation passed: full builds (CA: 3,659 jobs; SCV: 3,552 jobs), submission builds
(CA: 9,169 jobs; SCV: 9,189 jobs), direct Lean checks of every changed file in both projects,
the admission scan, and `git diff --check`. SCV's submission build also reports two
unused-section-variable warnings in the unchanged `Solution.lean`, for `SCV.common_extension`
and `SCV.isDomainOfHolomorphy_of_convex_and_pi`; these do not affect proof acceptance.
The only remaining admissions are the existing Challenge placeholders (45 in CA, 67 in SCV).
The implementation theorem axiom checks use only `propext`, `Classical.choice`, and `Quot.sound`.
No new assumptions, axioms, or suspected false statements were introduced.

The linked source headers credit the Tau Ceti contributors. lean-CA's `CREDITS.md` records
adoption of the two shared proofs as well.

[tau]: https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5
[tau-degree]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/Complex/Conformal/LocalDegree.lean
[tau-exterior]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/Normed/Module/Ball/Exterior.lean
[tau-laplacian]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean
[tau-inverse]: https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/Calculus/InverseFunctionTheorem.lean
