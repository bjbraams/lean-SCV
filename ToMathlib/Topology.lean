/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Topology.CompactExhaustion
public import ToMathlib.Topology.Frontier
public import ToMathlib.Topology.Graph
public import ToMathlib.Topology.MetricSpace.Pi
public import ToMathlib.Topology.Path
public import ToMathlib.Topology.SeparateContinuous
public import ToMathlib.Topology.UpperSemicontinuous

/-!
# General topology support

Compact exhaustions, frontier and complementary-component lemmas, graphs characterized by
equations, coordinate updates in finite products of pseudometric spaces, first exit of paths from
open sets, uniform bounds for separately continuous maps, and semicontinuity. Declarations
extend the existing Mathlib APIs. This library has no dependency on project analysis or complex
function theory.

## Main results

This module re-exports the following developments:

* `ToMathlib.Topology.CompactExhaustion`: Compact exhaustions of open subsets.
* `ToMathlib.Topology.Frontier`: Frontiers and complementary components.
* `ToMathlib.Topology.Graph`: Graphs characterized by equations.
* `ToMathlib.Topology.MetricSpace.Pi`: Coordinate updates in finite products of pseudometric
  spaces.
* `ToMathlib.Topology.Path`: First exit of a path from an open set.
* `ToMathlib.Topology.SeparateContinuous`: Uniform bounds for separately continuous maps.
* `ToMathlib.Topology.UpperSemicontinuous`: Nonnegative multiples of upper semicontinuous
  functions.
-/
