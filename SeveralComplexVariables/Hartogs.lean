/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.SeparateAnalytic
public import SeveralComplexVariables.HartogsExtension
public import SeveralComplexVariables.HartogsSeries
public import SeveralComplexVariables.HartogsConsequences

/-!
# Hartogs theorems

This umbrella exports the geometry of Hartogs sets and their fibers from `HartogsDomain`,
Taylor and Laurent expansion targets from `HartogsSeries`, separate analyticity from
`SeparateAnalytic`, and extension from Hartogs figures and across compact holes from
`HartogsExtension`. It also exports proved continuation over an arbitrary connected base,
punctured-polydisc removability, and spherical-shell extension (the latter depends on
the pending compact-hole theorem). Fiber preconnectedness is a separate geometric property.
-/
