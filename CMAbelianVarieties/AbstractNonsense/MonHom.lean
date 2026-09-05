--import Mathlib
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mon

open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable (A : C) [MonObj A] [IsCommMonObj A]
variable (B : C) [MonObj B] [IsCommMonObj B]

instance : IsMonHom (toUnit A) where
  one_hom := by simp only [comp_toUnit, toUnit_unit, MonObj.one_def]
  mul_hom := SemiCartesianMonoidalCategory.toUnit_unique_iff.mpr _root_.trivial

instance : IsMonHom (η[A]) where
  one_hom := by simp only [MonObj.one_def, Category.id_comp]
  mul_hom := by
    simp only [MonObj.mul_def, mul_one_hom]
    have : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
      exact SemiCartesianMonoidalCategory.toUnit_unique_iff.mpr _root_.trivial
    rw[this]

def zero_hom : (Hom (mk A) (mk B)) where
  hom := (toUnit A) ≫ (MonObj.one : 𝟙_ C ⟶ B)
  isMonHom_hom := instIsMonHomComp (toUnit A) η[B]

#min_imports
