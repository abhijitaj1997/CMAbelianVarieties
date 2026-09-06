module

--import Mathlib
public import CMAbelianVarieties.AbelianVarieties.Homomorphisms


open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {A : C} [GrpObj A] [IsCommMonObj A]

variable (f g : (EndRing A))
variable (F G : Hom (mk A) (mk A))

#check f * g
#check F + G
#check F * G

#check Ring




section
open CategoryTheory AlgebraicGeometry Mon Limits

variable {K} [Field K]
variable {A : Over (Spec (.of K))} {B : Over (Spec (.of K))}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [GrpObj A]
variable (n : ℤ)

#check ((5[A]).hom : A ⟶ A)
#check n[A]
#check A[n]

#check pullback A.hom A.hom


end

#min_imports
