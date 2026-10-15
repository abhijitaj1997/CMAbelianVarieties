/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib
public import CMAbelianVarieties.ForMathlib.Endomorphism

/-!
## Goal

In this section we show that if `G` and `H` are commutative
Group objects such that `G ≅ H`, then we have an equivalence
`End G ≃+* End H`.

-/

@[expose] public section

open CategoryTheory AddGrp End

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {G : AddGrp C} [IsCommAddMonObj G.X] {H : AddGrp C} [IsCommAddMonObj H.X]
variable (φ : G ≅ H)

#check CategoryTheory.Iso.conj -- conj because `f ↦ φ.hom ≫ f ≫ φ.inv`
def CategoryTheory.Iso.conjRingEquiv : (End G) ≃+* (End H) := sorry
