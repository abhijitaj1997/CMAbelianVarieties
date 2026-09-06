module

--public import Mathlib
public import CMAbelianVarieties.AbstractNonsense.Basic
public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits


public noncomputable section






section
open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {A : C} [GrpObj A] [IsCommMonObj A]

variable (f g : (EndRing A))
variable (F G : Hom (mk A) (mk A))

#check f * g
#check F + G
#check F * G

#check Ring
end









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








section
open CategoryTheory Limits

variable [Category C] [CartesianMonoidalCategory C]
variable {A B X : C} [GrpObj A] [GrpObj B] [GrpObj X]
variable {f : A ⟶ X} {g : B ⟶ X} [HasPullback f g]
variable [IsMonHom f] [IsMonHom g]

#check pullback f g
--#synth GrpObj (pullback f g) --ERROR
end











section
open AlgebraicGeometry Scheme Hom CategoryTheory

variable {K} [Field K]
variable {A : Over (Spec (.of K))} {B : Over (Spec (.of K))}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [GrpObj A]
variable (F : EndRing A) (n : ℤ)

variable {X Y : Scheme} (f : X ⟶ Y)

#check f.app
--#check f⁻¹ᵁ

#check IsFinite


instance : IsAffineHom f where
  isAffine_preimage := by
    intro U _
    simp only [IsAffineOpen]
    sorry

instance : IsFinite f where
  isAffine_preimage := sorry
  finite_app := sorry

#check GrpHom_ker (n[A])

end










#min_imports
