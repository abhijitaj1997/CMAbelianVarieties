module

--import Mathlib
public import CMAbelianVarieties.AbstractNonsense.MonHom

@[expose] public section

open CategoryTheory Limits Mon MonObj MonoidalCategory CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {A : C} [GrpObj A]
variable {B : C} [GrpObj B]

noncomputable def GrpHom_ker (f : Hom (mk A) (mk B)) [HasPullback (f.hom) η[B]]
  := pullback (f.hom) η[B]



noncomputable instance {f : Hom (mk A) (mk B)} [HasPullback (f.hom) η]
    : GrpObj (GrpHom_ker f) where
      one := by
        have : η[A] ≫ f.hom = (𝟙 (𝟙_C)) ≫ η[B] := by
          simp only [IsMonHom.one_hom, Category.id_comp]
        exact @pullback.lift _ _ _ _ _ _ (f.hom) η[B] _ η[A] (𝟙 (𝟙_ C)) this
      mul := by
        let p₁ := (pullback.fst (f.hom) η) ⊗ₘ (pullback.fst (f.hom) η)
        let p₂ := (pullback.snd (f.hom) η) ⊗ₘ (pullback.snd (f.hom) η)
        have : (p₁ ≫ μ) ≫ f.hom = (p₂ ≫ μ) ≫ η := by
          simp only [Category.assoc, IsMonHom.mul_hom]
          have : (p₁ ≫ (f.hom ⊗ₘ f.hom)) = (p₂ ≫ (η ⊗ₘ η)) := by
            have fst : ((pullback.fst (f.hom) η) ≫
                f.hom) ⊗ₘ ((pullback.fst (f.hom) η) ≫ f.hom) = (p₁ ≫ (f.hom ⊗ₘ f.hom))
                := by
              ext <;> simp only [tensorHom_fst_assoc, tensorHom_fst, Category.assoc, p₁,
              tensorHom_snd, tensorHom_snd_assoc]
            have snd : ((pullback.snd (f.hom) η) ≫
                η[B]) ⊗ₘ ((pullback.snd (f.hom) η) ≫ η[B]) = (p₂ ≫ (η ⊗ₘ η))
                := by
              ext <;> simp only [tensorHom_fst_assoc, tensorHom_fst, Category.assoc, p₂,
              tensorHom_snd, tensorHom_snd_assoc]
            rw [← fst, ←  snd]
            have : pullback.fst f.hom η ≫ f.hom = pullback.snd f.hom η ≫ η := by
              exact pullback.condition
            ext <;> simp only [tensorHom_fst, tensorHom_snd, pullback.condition]
          simp only [← Category.assoc, this]
        exact @pullback.lift _ _ _ _ _ _ (f.hom) η[B] _ (p₁ ≫ μ) (p₂ ≫ μ) this
      one_mul := sorry
      mul_one := sorry
      mul_assoc := sorry
      inv := sorry
      left_inv := sorry
      right_inv := sorry


#min_imports
