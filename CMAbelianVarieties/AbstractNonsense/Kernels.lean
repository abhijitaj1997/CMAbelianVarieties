/-
Copyright (c) 2025 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

/-
## Needs to be updated

This page needs to be updated to additive notation
-/

public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
## Goal

In this file we will define the ker of a homomorphism
-/

@[expose] public noncomputable section


section WHAT
open CategoryTheory Limits AddMon AddMonObj MonoidalCategory CartesianMonoidalCategory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C] [HasPullbacks C]

-- Needs to be fixed in mathlib
#synth HasPullbacks (Grp C)
instance : HasPullbacks (AddGrp C) := sorry


def AddGrp.ker {A B : AddGrp C} [IsCommAddMonObj B.X] (f : A ⟶ B) : AddGrp C
    where
      X := pullback f.hom.hom ζ[B.X]
      addGrp := sorry

#min_imports
