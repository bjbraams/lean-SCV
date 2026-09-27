/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Coordinate updates in finite products of pseudometric spaces

A finite product of pseudometric spaces carries the supremum distance. Changing one coordinate
of a point of a closed ball, within the closed ball of the same radius around the matching
coordinate of the center, stays in the ball. Coordinatewise distance bounds for a map on a
product of sets telescope to a joint bound, by changing the coordinates one at a time.

## Main results

* `Metric.update_mem_closedBall`: coordinate updates preserve closed balls in a finite product.
* `dist_le_sum_of_dist_update_le`: coordinatewise bounds telescope to a joint bound.
-/

public section

open Function Metric Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]

namespace Metric

/-- Updating one coordinate of a point of a closed ball in a finite product, within the closed
ball of the same radius around the matching coordinate of the center, stays in the closed
ball. -/
theorem update_mem_closedBall {c z : ∀ i, X i} {r : ℝ} (hr : 0 ≤ r) (hz : z ∈ closedBall c r)
    (i : ι) {w : X i} (hw : w ∈ closedBall (c i) r) : update z i w ∈ closedBall c r := by
  rw [mem_closedBall, dist_pi_le_iff hr] at hz ⊢
  intro j
  by_cases hji : j = i
  · subst hji
    simpa using hw
  · simpa [hji] using hz j

end Metric

/-- **Telescoping coordinatewise bounds.** If changing the `i`-th coordinate of a point of the
product set `Set.pi univ s` within `s i` moves `f` by at most `C i` times the distance moved,
then `f` moves by at most `∑ i, C i * dist (y i) (x i)` between any two points of the product
set. This includes the empty index type, where every function is constant. -/
theorem dist_le_sum_of_dist_update_le {Y : Type*} [PseudoMetricSpace Y] {s : ∀ i, Set (X i)}
    {f : (∀ i, X i) → Y} {C : ι → ℝ}
    (hf : ∀ z ∈ Set.pi univ s, ∀ i, ∀ w ∈ s i, dist (f (update z i w)) (f z) ≤ C i * dist w (z i))
    {x y : ∀ i, X i} (hx : x ∈ Set.pi univ s) (hy : y ∈ Set.pi univ s) :
    dist (f y) (f x) ≤ ∑ i, C i * dist (y i) (x i) := by
  have hmem (t : Finset ι) : (fun i ↦ if i ∈ t then y i else x i) ∈ Set.pi univ s := by
    intro i hi
    dsimp only
    split_ifs <;> [exact hy i hi; exact hx i hi]
  suffices hstep : ∀ t : Finset ι,
      dist (f fun i ↦ if i ∈ t then y i else x i) (f x) ≤ ∑ i ∈ t, C i * dist (y i) (x i) by
    simpa using hstep Finset.univ
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    have heq : (fun j ↦ if j ∈ insert i t then y j else x j) =
        update (fun j ↦ if j ∈ t then y j else x j) i (y i) := by
      funext j
      by_cases hji : j = i
      · subst hji
        simp
      · simp [hji]
    rw [heq, Finset.sum_insert hi]
    refine (dist_triangle _ (f fun j ↦ if j ∈ t then y j else x j) _).trans (add_le_add ?_ ih)
    simpa [hi] using hf _ (hmem t) i (y i) (hy i (mem_univ i))
