# Project instructions — lean-SCV

Before working, read and follow [the shared Lean instructions](../lean-codes/AGENTS.common.md),
then apply the project-specific rules below. Resolve that path relative to this file.
Local rules take precedence over the shared defaults. If the shared file is unavailable,
report that fact rather than proceeding without it.

## Build settings

- Lake root: the directory containing this `AGENTS.md`.
- Build output: `.lake/build-SCV`; preserve the matching `buildDir` in `lakefile.toml`.
- Ordinary build command: `lake build > /tmp/SCV-build.log 2>&1`.
- Active work: SeveralComplexVariables.

## Project

The objective is to formalize basic theory of Several Complex Variables (SCV) using Mathlib.
The work is meant as a contribution to Mathlib.
Subdirectory References contains PDF files for several basic texts in the area of SCV. These
references provide guidance for material to be included in the formalization. See the Section
"Source material" below for more precision.

## Dependencies and import layers

Mathlib and TauCeti are allowed in `ToMathlib`, `ComplexAnalysis`, and
`SeveralComplexVariables`. `ToMathlib` must not import either complex-analysis layer;
`ComplexAnalysis` must not import `SeveralComplexVariables`.
Make shared-source changes in lean-CA first and copy them here, checking both projects.
Compare upstream hypotheses against SCV callers, especially Banach targets and
higher-dimensional sources; a one-variable theorem need not replace an SCV theorem.

## Project-specific editing

- Files use the Lean module system: `module`, `public import`, and
  `public section` (or `public noncomputable section` when needed). A definition
  that downstream files must unfold, or about which they prove `rfl` lemmas, must be
  exposed; a `public` theorem proved by `rfl` about an unexposed definition fails at
  build time even though `lake env lean` accepts it.
- Project-specific declarations live in `namespace SeveralComplexVariables`. Lemmas about
  project structures or predicates use dotted names; the large `AnalyticGerm` API uses
  nested namespace blocks. Reusable extensions of existing Mathlib APIs belong in their
  original namespaces (use `_root_` from inside a project namespace). Generic results
  belong at the root or in their natural Mathlib namespace, in suitable supporting modules.
- Supporting code lives outside `SeveralComplexVariables/`: single-variable complex analysis
  in `ComplexAnalysis/`, general analysis and topology in `ToMathlib/Analysis` and
  `ToMathlib/Topology`, and algebra (if any) in `ToMathlib/Algebra`. The files in
  `ComplexAnalysis/` are exact copies of a subset of `../lean-CA/ComplexAnalysis`, restricted to
  modules this project imports; do not edit them here, but change them in lean-CA and copy
  them back. A `ToMathlib` file that also exists in lean-CA must have identical content and
  path in both projects. The umbrella modules `ToMathlib.lean`, `ToMathlib/Analysis.lean`,
  `ToMathlib/Topology.lean` and `ToMathlib/Algebra.lean` are exempt: each project's umbrella
  imports its own inventory.
- Expose definitions whose formulas downstream modules need to unfold, either individually
  with `@[expose]` or in a suitably scoped exposed section. Theorem-only sections and
  private implementation details do not need blanket exposure.

## Documentation files

File README.md is intended as public documentation; it points to SCVMainTheorems.md for
the mathematical content and to SeveralComplexVariablesCoverage.md for the dated ledger.

## Mathematical conventions

This project relies on multiple literature sources (textbooks, monographs, lecture notes)
that do not all share the same terminology or conventions. For this project, Mathlib
style and Mathlib conventions are to be followed whenever possible.

- Use **Holomorphic** to mean complex Fréchet-differentiable on an open set and use
  **Analytic** to mean locally representable by a convergent power series.

- Use Mathlib's existing predicates and structures whenever suitable.
  On open sets, express holomorphy using `DifferentiableOn ℂ` and analyticity using
  `AnalyticOnNhd ℂ`. Use the proved equivalence under its applicable hypotheses; do not
  identify these notions without checking the domain and codomain assumptions.

- In mathematical prose, a domain means a nonempty connected open set. In Lean
  statements, require openness, connectedness, and nonemptiness only when needed.
  Prefer `IsPreconnected` when nonemptiness is unnecessary.

- Distinguish Euclidean balls from polydiscs. Mathlib's usual norm on a finite function
  space `ι → ℂ` is the supremum norm, so its balls are equal-radius polydiscs.
  Use an appropriate Euclidean space when the Euclidean norm or Hermitian geometry matters.

- Prefer arbitrary finite coordinate index types when natural.
  Use `Fin n` when dimension, induction, or coordinate ordering makes it useful.
  Include the empty index type unless the result needs positive dimension; state
  dimension restrictions explicitly.

- Prefer Banach-valued formulations when the argument supports them.
  Keep scalar or finite-dimensional target assumptions when essential, for example in
  zero-set theory, scalar open mapping, and Montel compactness. Generality should
  preserve the intended mathematical content and useful estimates. Where a Banach-valued
  version of a scalar hull argument is needed, obtain it through norming functionals
  (Hahn–Banach), as in the Banach-valued Thullen lemma.

- Formulate hulls and bounds with all real upper bounds rather than a supremum, so that
  empty sets and unbounded functions need no special cases. The domain-of-holomorphy
  property requires agreement on a fixed nonempty open overlap, not on all components of
  the intersection. Boundary distance takes values in `[0, ∞]`.

- Define subharmonicity by upper semicontinuity and the local circle submean property,
  and plurisubharmonicity by subharmonicity on every complex line. Assume no smoothness
  in definitions; the `C²` criteria by the Laplacian and by the Levi form are theorems.

- Quantify Levi conditions over all local `C²` defining functions, so that independence
  of the defining function is a theorem rather than part of the definition.

- Express the Cauchy–Riemann operator through the antiholomorphic part of a real
  derivative along a direction (`dbarAlong`), not through differential forms. The project
  uses no differential forms, currents, or Stokes theorems; stay with this convention
  unless forms become essential.

- Represent polynomials as `MvPolynomial (Fin n) ℂ` evaluated by `MvPolynomial.eval`.
  State approximation results as approximation within `ε` on compact sets, and derive
  locally uniform sequence formulations as consequences.

- Tubes and other coordinate constructions use the supremum norm on `ι → ℂ`. Prove
  results on `Fin n` where polydisc Cauchy theory is needed, and transport them to a
  general finite index type by reindexing.

- A theorem that is a special case of a more general project theorem may keep its own
  proof when the general theorem is proved from it; the docstring should say so. Do not
  keep independent proofs of specializations that could be derived in one line.

## Mathematical scope and exclusions

The primary objective is classical analytic theory of functions and maps on open
subsets of finite-dimensional complex normed spaces, especially domains in ℂⁿ.
Retain Banach-valued formulations where appropriate.

Prioritize function-theoretic results: integral representations, power series,
holomorphic mappings, analytic continuation, removable singularities, approximation,
and convexity notions relevant to holomorphy.

The following objectives are complete, formulated for open subsets of ℂⁿ or of
finite-dimensional complex normed spaces: Cauchy and Taylor theory, locally uniform
convergence and function spaces, the inverse and implicit mapping theorems, Reinhardt and
circular continuation, Hartogs–Taylor and Hartogs–Laurent expansion, Hartogs' unrestricted
separate-holomorphy theorem, removable singularities including Hartogs' compact-hole
theorem, the Riemann extension theorems, analytic germs with Weierstrass division and
preparation, Noetherianity and unique factorization, Cartan uniqueness and circular
rigidity, holomorphic convexity with Thullen's lemma and the Cartan–Thullen equivalences,
Bochner's tube theorem, subharmonic and plurisubharmonic functions, pseudoconvexity, Levi
convexity with Levi's necessary condition and local peak functions, and the elementary
theory of Runge pairs, Runge domains, and polynomial hulls. None of this required general
Riemann domains or abstract envelopes of holomorphy. The catalogue in SCVMainTheorems.md
records the exact statements.

The following are deferred targets, with the missing infrastructure noted:

- The Oka–Weil theorem and the one-variable Runge theorem for rational approximation,
  which need either solution theory for the Cauchy–Riemann equation on polynomially
  convex compact sets or Cauchy integrals over general cycles.
- The Levi problem in the sufficiency direction, that pseudoconvex open sets are domains
  of holomorphy, which needs `L²` or Hörmander-type `∂̄` theory. The necessary direction
  and Levi convexity are complete.
- Strictly convex local coordinates at strictly Levi pseudoconvex boundary points, and
  the passage from local peak functions to local domains of holomorphy.
- For analytic sets: irreducible components, analyticity of the singular locus, and
  local dimension theory.

Do not independently develop general manifolds, bundles, sheaves, sheaf cohomology,
schemes, or general complex analytic spaces.

Elementary zero-set theory, analytic germs, Weierstrass division and preparation, and
algebraic tools are permitted when they directly support classical analytic results.
Systematic local algebra and algebraic geometry are not independent project objectives.

Smooth boundaries are in use through local `C²` defining functions. Differential forms
and embedded submanifolds are permitted when needed for analysis on Euclidean domains,
but so far the `∂̄` arguments (Ehrenpreis' proof of the compact-hole theorem) were carried
out with real derivatives and the Cauchy–Pompeiu identity in polar coordinates, without
forms; see the conventions above.

General Riemann domains and abstract envelopes of holomorphy are deferred; prioritize
extension results between domains in ℂⁿ.

These scope rules take precedence over the reference chapter list. A listed chapter is
a source of candidate results, not a commitment to formalize all its material.

These exclusions concern development objectives. Reuse appropriate Mathlib abstractions
and theorems without imposing blanket import bans.

## Source material

The References directory contains PDF files for several books and other publications.
There is no hierarchy among these references. They serve as a guide for statements worth
including in this project, but not every statement from any source needs to be included.
The ranges below identify candidate material, not completed coverage or a requirement
to reproduce each source's proof apparatus. Use chapter-level ranges unless a section
boundary clarifies the intended selection. Current statements and proof status are
described in SCVMainTheorems.md and SeveralComplexVariablesCoverage.md.

- Alexander and Wermer (1998) SCV. Chapters 1 through 6. Not yet drawn on.
- Boas (2013) Lecture Notes. Chapters 1 through 3 and Sections 4.1–4.2, selectively.
  Section 2.4 was used for Hartogs' compact-hole theorem. Section 3.4 (the Jacobian
  conjecture) is background only; Section 4.3 (the Levi problem) is deferred.
- Fritzsche and Grauert (2002) Holomorphic. Chapter I; Chapter II, Sections 1–6
  and selected examples from Section 7; Chapter III, Sections 1–3.
  Chapter II, Section 6 supplied singular functions for Cartan–Thullen theory, and
  Chapter II, Sections 3–4 were used for Levi convexity. Sections 8–9 on Riemann domains
  and abstract envelopes remain deferred.
- Hörmander (1973) Introduction. The directory contains separate PDF files for
  Chapters I–IV and VII. Chapter II was used: Section 2.3 for Ehrenpreis' proof of the
  compact-hole theorem, Section 2.5 for Thullen's lemma and Bochner's tube theorem
  (Theorem 2.5.10), and Section 2.7 for Runge domains. Chapter IV (`L²` estimates for `∂̄`)
  is the natural source if the Levi problem or the Oka–Weil theorem is attempted.
- Jakóbczak and Jarnicki (2021) Lectures. Chapters 1 and 2; Sections 4.2–4.3 were used
  for the `∂̄` proof of Hartogs' extension theorem and for Runge domains.
- Korevaar and Wiegerinck (2017) Lectures. The local PDF is named 1997/revised-2021,
  but its title page identifies the version of 23 August 2017. Chapters 1 through 6,
  selectively. Section 1.7 was used for Runge theory and Exercise 6.28 (the prism lemma)
  for the parabolic analytic discs in Bochner's theorem. The general-manifold and
  projective-space material in Sections 5.7–5.8 is outside the present objectives;
  Section 2.9 on envelopes beyond ℂⁿ is background only.
- Krantz (1992) Function Theory. Chapters 1 and 2.
- Lebl (2026) Tasty Bits. Chapters 1 and 2.
- LeLong and Gruman (1986) Entire Functions. Not used at present.
- Merker and Porten (2007) Morse. Not used; the compact-hole theorem was proved by the
  `∂̄` method instead of by analytic discs.
- Range (1986) Holomorphic. Chapters I and II, selectively, with particular emphasis
  on Chapter II, Sections 1–3. Section II.2 was used for Levi convexity and the Levi
  polynomial peak function.
- Scheidemann (2005) Introduction. Chapters 1 through 7 and Chapter 8, Sections 1–3.
  Chapter 6 (tube domains) was used for Bochner's theorem. The differential-form and `∂̄`
  methods of Chapter 5 have not been needed and are available if `∂̄` theory is developed.
  Section 8.4 (the Nullstellensatz) is deferred.
- Shabat (1991) Introduction. Chapter 1.
- Suwa (2024) Complex Analytic Geometry. Chapter 1.

The listed ranges also contain plurisubharmonic functions, pseudoconvexity, and
additional convexity notions; these are now included at the level described in
SCVMainTheorems.md. The same ranges are the sources for the Levi problem and for the
Oka–Weil theorem, which are not objectives; listing them does not commit the project to
their machinery.
