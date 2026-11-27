/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
## Goal

The goal of this file is to show that group structure of objects descend to
a Rational model

-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped BaseChange
open Algebra (IsAlgebraic)

namespace GroupStructure

universe u

variable {K Kₐ : Type u} [Field K] [Field Kₐ] [Algebra K Kₐ] [IsAlgebraic K Kₐ]
variable {G : Over (Spec ↧K)} [AddGrpObj (G ⊗ₛ Kₐ)]

def fieldOfDefintion (G : Over (Spec ↧K)) (Kₐ : Type u) [Field Kₐ] [Algebra K Kₐ]
    [IsAlgebraic K Kₐ] [AddGrpObj (G ⊗ₛ Kₐ)] : IntermediateField K Kₐ := sorry

instance FiniteDimensional_ofFieldOfDefintion (G : Over (Spec ↧K)) (Kₐ : Type u) [Field Kₐ]
    [Algebra K Kₐ] [IsAlgebraic K Kₐ] [AddGrpObj (G ⊗ₛ Kₐ)] :
    FiniteDimensional K (fieldOfDefintion G Kₐ) := sorry

instance AddGroupObj_overFieldOfDefintion (G : Over (Spec ↧K)) (Kₐ : Type u) [Field Kₐ]
    [Algebra K Kₐ] [IsAlgebraic K Kₐ] [AddGrpObj (G ⊗ₛ Kₐ)] :
    AddGrpObj (G ⊗ₛ (fieldOfDefintion G Kₐ)) := sorry

open AddGrp in
def AddGroupObj_overFieldOfDefintion_Iso (G : Over (Spec ↧K)) (Kₐ : Type u) [Field Kₐ]
    [Algebra K Kₐ] [IsAlgebraic K Kₐ] [AddGrpObj (G ⊗ₛ Kₐ)] :
    letI := AddGroupObj_overFieldOfDefintion G Kₐ
    mk ((G ⊗ₛ (fieldOfDefintion G Kₐ)) ⊗ₛ Kₐ) ≅ mk (G ⊗ₛ Kₐ) := by
  sorry

end GroupStructure
