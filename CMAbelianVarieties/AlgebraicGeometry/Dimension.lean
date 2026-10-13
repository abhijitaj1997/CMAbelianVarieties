/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension

/-!
## Dimension of a group scheme

Need to fill in the details some day.

-/

@[expose] public section

open AlgebraicGeometry Order

/-- The dimension of a scheme is the supremum of the dimensions of its stalks. -/
lemma topologicalKrullDim_eq_iSup_ringKrullDim_stalk (X : Scheme) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  simp_rw [ringKrullDim_stalk_eq_coheight]
  rw [← krullDim_eq_iSup_coheight, topologicalKrullDim]
  exact krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
