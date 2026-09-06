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

open AlgebraicGeometry Scheme Hom


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

end



section
open AlgebraicGeometry CategoryTheory Limits Mon MonObj MonoidalCategory CartesianMonoidalCategory

variable (X : Scheme)

#check Over X

#check Scheme

#synth Limits.HasPullbacks (Over X)
#synth Category (Over X)
#synth CartesianMonoidalCategory (Over X)


open CategoryTheory Limits

variable {A B X : C} [GrpObj A] [GrpObj B] [GrpObj X]
variable {f : A ⟶ X} {g : B ⟶ X}
variable [IsMonHom f] [IsMonHom g]
variable (F : Hom (mk A) (mk X))
variable [HasPullbacks C]

#check pullback f g
#check (pullback (Grp.ofHom F.hom) (Grp.ofHom η[X]))

#check Grp.ofHom
instance :  GrpObj (pullback (Grp.ofHom f) (Grp.ofHom g)).X := by
  infer_instance

end


#min_imports
