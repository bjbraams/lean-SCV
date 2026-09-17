/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.AnalyticSet.Basic
public import SeveralComplexVariables.AnalyticSet.Removable
public import SeveralComplexVariables.AnalyticSet.Regular
public import SeveralComplexVariables.AnalyticSet.Codimension
public import SeveralComplexVariables.AnalyticSet.CoordinatePlane
public import SeveralComplexVariables.AnalyticSet.FunctionSpace

/-!
# Elementary analytic subsets of complex domains

Local finite equations, elementary set operations, regular points, and slice codimension
support classical extension theory. The first Riemann theorem and coordinate-subspace
removal and full-rank flattening are proved. Regular points on nonempty hypersurfaces and
automatic local boundedness in codimension two remain pending; the general second Riemann
theorem and its algebraic restriction formulation depend on the latter.

Sources: Range I §3.2; Fritzsche–Grauert I §8; Scheidemann Chapter 4.
Irreducible decomposition, arbitrary infinite systems of equations, sheaf methods, and
abstract analytic spaces are deferred. Injective holomorphic maps are treated separately
in `SeveralComplexVariables.InjectiveMapping`.
-/
