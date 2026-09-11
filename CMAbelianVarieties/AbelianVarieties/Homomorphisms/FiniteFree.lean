/-
Copyright (c) 2025 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

--import Mathlib
public import CMAbelianVarieties.ForMathlib.Endomorphism
public import Mathlib.AlgebraicGeometry.Group.Abelian

/-!
## Main goal
The main goal of this section is to show that the homomorphisms between abelian
varieties give a finite free module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AddMon Limits

variable {K} [Field K]
variable {A : Over (Spec (.of K))} {B : Over (Spec (.of K))}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable [IsProper B.hom] [GeometricallyIntegral B.hom] [AddGrpObj B]

-- this instance does not exist
instance : IsCommAddMonObj A := sorry




/-
instance hom_torsion_free : NoZeroSMulDivisors ℤ (Hom (mk A) (mk B)) where
  eq_zero_or_eq_zero_of_smul_eq_zero := by
    rintro n ⟨φ, isnt⟩ h
    simp at φ
    by_cases hn : n = 0
    · left; assumption
    · right

      sorry-/


#min_imports
