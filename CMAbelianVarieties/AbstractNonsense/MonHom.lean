module

--import Mathlib
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

@[expose] public section

open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable (G : C) [MonObj G] [IsCommMonObj G]
variable (H : C) [MonObj H] [IsCommMonObj H]
variable {A : C} [GrpObj A] [IsCommMonObj A]
variable {B : C} [GrpObj B] [IsCommMonObj B]

instance : IsMonHom (toUnit G) where
  one_hom := by simp only [comp_toUnit, toUnit_unit, MonObj.one_def]
  mul_hom := SemiCartesianMonoidalCategory.toUnit_unique_iff.mpr _root_.trivial

instance : IsMonHom (η[G]) where
  one_hom := by simp only [MonObj.one_def, Category.id_comp]
  mul_hom := by
    simp only [MonObj.mul_def, mul_one_hom]
    have : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
      exact SemiCartesianMonoidalCategory.toUnit_unique_iff.mpr _root_.trivial
    rw[this]

def zero_hom : (Hom (mk G) (mk H)) where
  hom := (toUnit G) ≫ (MonObj.one : 𝟙_ C ⟶ H)
  isMonHom_hom := instIsMonHomComp (toUnit G) η[H]

--instance [GrpObj A] : IsMonHom (ι : A ⟶ A) := by infer_instance

def comp_inv (f : A ⟶ B) [IsMonHom f] := ι ≫ f
def inv_comp (f : A ⟶ B) [IsMonHom f] := f ≫ ι

instance comp_inv_hom (f : A ⟶ B) [IsMonHom f] : IsMonHom (comp_inv f) := instIsMonHomComp ι f
instance inv_comp_hom (f : A ⟶ B) [IsMonHom f] : IsMonHom (inv_comp f) := instIsMonHomComp f ι

/-
lemma eq_of_inv_comp_comp_inv (f : A ⟶ B) [IsMonHom f] :
    comp_inv f = (inv_comp f) := by
  sorry
-/

#min_imports
