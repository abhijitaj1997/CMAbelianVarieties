/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
## Test file

The negation of a continuous function `ℝ → ℝ` is continuous, proved directly from the
`ε`-`δ` characterisation of continuity (without using `Continuous.neg`).
-/

public section

theorem continuous_neg_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun x => -f x) := by
  rw [Metric.continuous_iff] at hf ⊢
  intro x ε hε
  obtain ⟨δ, hδ, h⟩ := hf x ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  rw [Real.dist_eq, neg_sub_neg, abs_sub_comm, ← Real.dist_eq]
  exact h y hy

end
