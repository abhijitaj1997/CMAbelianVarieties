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
open Algebra (IsAlgebraic)

namespace GroupStructure

universe u

variable {K Kₐ : Type u} [Field K] [Field Kₐ] [Algebra K Kₐ] [IsAlgebraic K Kₐ]
variable {G : Over (Spec ↧K)} [AddGrpObj (G _ Kₐ)]

def fieldOfDefintion (G : Over (Spec ↧K)) (Kₐ : Type u) [Field Kₐ] [Algebra K Kₐ]
    [IsAlgebraic K Kₐ] [AddGrpObj (G _ Kₐ)] : IntermediateField K Kₐ := sorry

instance FiniteDimensional_ofFieldOfDefintion (G : Over (Spec ↧K)) (Kₐ : Type u) [Field Kₐ]
    [Algebra K Kₐ] [IsAlgebraic K Kₐ] [AddGrpObj (G _ Kₐ)] :
    FiniteDimensional K (fieldOfDefintion G Kₐ) := sorry

instance AddGroupObj_overFieldOfDefintion (G : Over (Spec ↧K)) (Kₐ : Type u) [Field Kₐ]
    [Algebra K Kₐ] [IsAlgebraic K Kₐ] [AddGrpObj (G _ Kₐ)] :
    AddGrpObj (G _ (fieldOfDefintion G Kₐ)) := sorry

end GroupStructure
