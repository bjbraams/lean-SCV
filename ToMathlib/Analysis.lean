/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Connected
public import ToMathlib.Analysis.GeometricBounds
public import ToMathlib.Analysis.Holomorphic.FunctionSpace
public import ToMathlib.Analysis.Holomorphic.NormalFamily
public import ToMathlib.Analysis.Integral.CompactSupport
public import ToMathlib.Analysis.LinearFunctional
public import ToMathlib.Analysis.OpenMapping
public import ToMathlib.Analysis.TaylorBounds

/-!
# General analysis support

Connectedness of shells, real root limits and geometric bounds, spaces of holomorphic maps with
the compact-open topology and the shared Montel and Vitali arguments, integration of compactly
supported and weighted functions, continuous linear functionals, the open mapping theorem for
complete metrizable vector spaces, and elementary real Taylor-remainder bounds. Declarations use
the namespaces of their underlying Mathlib APIs. This library depends only on Mathlib.

## Main results

This module re-exports the following developments:

* `ToMathlib.Analysis.Connected`: Connectedness of shells and exteriors of balls.
* `ToMathlib.Analysis.GeometricBounds`: Real root limits and geometric bounds.
* `ToMathlib.Analysis.Holomorphic.FunctionSpace`: Shared spaces of holomorphic maps.
* `ToMathlib.Analysis.Holomorphic.NormalFamily`: Shared Montel and Vitali arguments.
* `ToMathlib.Analysis.Integral.CompactSupport`: Integration helpers for compactly supported
  and weighted functions.
* `ToMathlib.Analysis.LinearFunctional`: Scalar actions and continuous linear functionals.
* `ToMathlib.Analysis.OpenMapping`: Open mapping for complete metrizable real or complex vector
  spaces.
* `ToMathlib.Analysis.TaylorBounds`: Elementary bounds for Taylor remainders.
-/
