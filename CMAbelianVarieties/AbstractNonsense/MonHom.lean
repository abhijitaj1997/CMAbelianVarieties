--import Mathlib
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mon

open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable (A : C) [MonObj A] [IsCommMonObj A]
variable (B : C) [MonObj B] [IsCommMonObj B]

instance : IsMonHom (toUnit A) where
  one_hom := sorry
  mul_hom := sorry

instance : IsMonHom (η[A]) where
  one_hom := by simp only [MonObj.one_def, Category.id_comp]
  mul_hom := by

    sorry

def zero_hom : (Hom (mk A) (mk B)) where
  hom := (toUnit A) ≫ (MonObj.one : 𝟙_ C ⟶ B)
  isMonHom_hom := instIsMonHomComp (toUnit A) η[B]

#min_imports
