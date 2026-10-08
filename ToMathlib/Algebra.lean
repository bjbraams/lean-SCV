/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Algebra.LinearMap.Ordered
public import ToMathlib.Algebra.Polynomial.OfFn

/-!
# General algebra support

Reconstruction of polynomials from finite coefficient vectors. Declarations extend the existing
Mathlib APIs. This library depends only on Mathlib.

Ordered-field linear functionals and inclusion of their negative half-spaces are also included.

## Main results

This module re-exports the following developments:

* `ToMathlib.Algebra.LinearMap.Ordered`: Half-space inclusion and proportionality of linear
  functionals.

* `ToMathlib.Algebra.Polynomial.OfFn`: Reconstruction of polynomials from finite coefficient
  vectors.
-/
