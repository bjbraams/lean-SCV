# Several Complex Variables

A Lean 4 formalization of the classical theory of several complex variables, built on
Mathlib and intended as a contribution to it. The subject is function theory on open subsets
of finite-dimensional complex normed spaces, in particular domains in ℂⁿ: Cauchy and Taylor
theory, convergence and function spaces, local holomorphic mappings, Reinhardt and Laurent
continuation, the Hartogs phenomena and removable singularities, analytic sets, analytic germs
with Weierstrass theory, holomorphic convexity with the Cartan–Thullen theorem and Bochner's
tube theorem, plurisubharmonic functions and Levi convexity, and the elementary theory of
Runge domains. Statements are Banach-valued wherever the arguments allow.

The mathematical content is described in **[SCVMainTheorems.md](SCVMainTheorems.md)**: the
definitions and conventions, the catalogue of 65 principal results with proof sketches, and
the extent and limits of the theory. Every catalogued result is proved; the project contains
no admitted statements.

## Organization

- `SeveralComplexVariables.lean` is the root module. It imports every file of the library
  and its docstring summarizes the contents topic by topic.
- `SeveralComplexVariables/` holds the library: 143 files in 64 top-level modules and 17
  subdirectories, grouped by topic (`AnalyticGerm`, `AnalyticSet`, `HolomorphicConvexity`,
  `LaurentSeries`, `LeviConvexity`, `Reinhardt`, `RemovableSingularity`, `Runge`,
  `SeparateAnalytic`, `Subharmonic`, `TubeDomain`, `WeierstrassDivision`, `ZeroSets`, and
  others). Every file has a documentation header and every declaration a docstring.
- `Main.lean` is the executable stub required by the Lake configuration; it only imports the
  library.
- `References/` contains the texts that guided the selection of material; see below.

## Building

The project uses Lean and Mathlib at version `v4.34.0` (see `lean-toolchain` and
`lakefile.toml`). From the repository root:

    lake build

Documentation can be generated with the `doc-gen4` dependency declared in the lakefile.

## Documentation

- [SCVMainTheorems.md](SCVMainTheorems.md): definitions, conventions, and the catalogue of
  principal results with their proof status. This is the mathematical description of the
  project.
- [SeveralComplexVariablesCoverage.md](SeveralComplexVariablesCoverage.md): the dated ledger
  of changes, listing the declarations added in each session and the assessments of
  deferred targets.
- [AGENTS.md](AGENTS.md): instructions for contributors and for automated assistants, with
  the build topology, proof requirements, mathematical conventions, scope, and source
  material.

## Conventions in brief

Holomorphic means `DifferentiableOn ℂ` on an open set and analytic means `AnalyticOnNhd ℂ`;
their equivalence is proved in the setting used. The norm on `ι → ℂ` is the supremum norm,
so its balls are polydiscs; Euclidean balls are identified explicitly. Hulls are defined by
all real upper bounds, subharmonicity by the local submean property, and the Cauchy–Riemann
operator by the antiholomorphic part of a real derivative, without differential forms. The
deferred targets are the Oka–Weil approximation theorem, the one-variable Runge theorem for
rational approximation, and the Levi problem in the sufficiency direction.

## References

The formalization follows classical introductory treatments, especially:

- H. Alexander and J. Wermer, *Several Complex Variables and Banach Algebras*, 3rd ed.,
  Springer GTM 135, 1998.
- H. P. Boas, *Lecture Notes on Several Complex Variables*, manuscript, 2013.
- K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex Manifolds*, Springer
  GTM 213, 2002.
- L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 2nd ed.,
  North-Holland, 1973.
- P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*, manuscript, 2021.
- J. Korevaar and J. Wiegerinck, *Lecture Notes on Several Complex Variables*, 1997,
  revised 2021.
- S. G. Krantz, *Function Theory of Several Complex Variables*, 2nd ed., 1992.
- J. Lebl, *Tasty Bits of Several Complex Variables*, 2026.
- P. Lelong and L. Gruman, *Entire Functions of Several Complex Variables*, Springer, 1986.
- J. Merker and E. Porten, *A Morse-theoretical proof of the Hartogs extension theorem*,
  J. Geom. Anal. 17 (2007).
- R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*, Springer GTM 108, 1986.
- V. Scheidemann, *Introduction to Complex Analysis in Several Variables*, Birkhäuser, 2005.
- B. V. Shabat, *Introduction to Complex Analysis, Part II: Functions of Several Variables*,
  1991.
- T. Suwa, *Complex Analytic Geometry: From the Localization Viewpoint*, World Scientific,
  2024.

## License

Apache License 2.0; see [LICENSE](LICENSE).
