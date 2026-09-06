module

--public import Mathlib
public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.FiniteFree
public import CMAbelianVarieties.AbstractNonsense.Kernels

@[expose] public section

open CategoryTheory AlgebraicGeometry Mon Limits

variable {K} [Field K]
variable {A : Over (Spec (.of K))} {B : Over (Spec (.of K))}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [GrpObj A]
variable [IsProper B.hom] [GeometricallyIntegral B.hom] [GrpObj B]

noncomputable def int_hom (n : ℤ) (A₀ : Over (Spec (.of K)))
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [GrpObj A₀]
    : Hom (mk A₀) (mk A₀) := n • 1

noncomputable def ker_int (A₀ : Over (Spec (.of K))) (n : ℤ)
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [GrpObj A₀]
    : Over (Spec (.of K)) := GrpHom_ker (int_hom n A)


notation:50 n:51 "[" A:51 "]" => int_hom n A
notation:50 A:51 "[" n:51 "]" => ker_int A n


#min_imports
