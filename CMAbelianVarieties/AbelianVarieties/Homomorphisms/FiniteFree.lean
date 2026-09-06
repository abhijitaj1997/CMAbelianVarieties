module

--import Mathlib
public import CMAbelianVarieties.AbstractNonsense.EndomorphismRing
public import Mathlib.AlgebraicGeometry.Group.Abelian

@[expose] public section

open CategoryTheory AlgebraicGeometry Mon Limits

variable {K} [Field K]
variable {A : Over (Spec (.of K))} {B : Over (Spec (.of K))}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [GrpObj A]
variable [IsProper B.hom] [GeometricallyIntegral B.hom] [GrpObj B]

instance : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A

/-
## Main goal
The main goal of this section is to show that the homomorphisms between abelian
varieties give a finite free module.
-/




instance hom_torsion_free : NoZeroSMulDivisors ℤ (Hom (mk A) (mk B)) where
  eq_zero_or_eq_zero_of_smul_eq_zero := by
    rintro n ⟨φ, isnt⟩ h
    simp at φ
    by_cases hn : n = 0
    · left; assumption
    · right

      sorry


#min_imports
