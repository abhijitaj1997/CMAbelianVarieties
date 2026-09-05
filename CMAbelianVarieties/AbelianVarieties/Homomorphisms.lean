module

--import Mathlib
public import CMAbelianVarieties.AbstractNonsense.Kernels
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


noncomputable def int_hom (n : ℤ) (A₀ : Over (Spec (.of K)))
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [GrpObj A₀]
    : Hom (mk A₀) (mk A₀) := n • 1

noncomputable def ker_int (A₀ : Over (Spec (.of K))) (n : ℤ)
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [GrpObj A₀]
    : Over (Spec (.of K)) := GrpHom_ker (int_hom n A)


notation:50 n:51 "[" A:51 "]" => int_hom n A
notation:50 A:51 "[" n:51 "]" => ker_int A n


instance hom_torsion_free : NoZeroSMulDivisors ℤ (Hom (mk A) (mk B)) where
  eq_zero_or_eq_zero_of_smul_eq_zero := by
    rintro n ⟨φ, isnt⟩ h
    simp at φ
    by_cases hn : n = 0
    · left; assumption
    · right

      sorry


#min_imports
