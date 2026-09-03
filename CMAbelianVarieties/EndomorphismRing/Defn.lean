--import Mathlib
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mon


open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable (A : C) [MonObj A] [IsCommMonObj A]


def EndRing := Hom (mk A) (mk A)

/-
I have only assumed that the object is monoidal, and not a group object
this might give a semiring, and I guess the group structure will make it a
ring
.
.
.
I haven't given this much thought. So, I could easily be wrong
-/

instance : Add (EndRing A) where
  add f g := {
    hom := (lift f.hom g.hom) ≫ μ[A]
    isMonHom_hom := {
      one_hom := by
        rw[← Category.assoc]
        have : (η[A] ≫ (lift f.hom g.hom)) = (lift η[A] η[A]) := by
          ext
          · simp[@IsMonHom.one_hom _ _ _ _ _ _ _ f.hom (f.isMonHom_hom)]
          · simp[@IsMonHom.one_hom _ _ _ _ _ _ _ g.hom (g.isMonHom_hom)]
        rw[this]
        have this₀ : (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ η[A]) ≫ (λ_ A).hom = η[A] := by
          simp
        have this₁ : (𝟙 (𝟙_ C) ⊗ₘ η[A]) ≫ (η[A] ⊗ₘ 𝟙 A) = η[A] ⊗ₘ η[A] := by
          ext
          · have : (η[A] ⊗ₘ (𝟙 A)) ≫ fst A A = (fst (𝟙_ C) A) ≫ η[A] :=
              tensorHom_fst η (𝟙 A)
            rw[Category.assoc, this, ← Category.assoc]
            have : ((𝟙 (𝟙_ C) ⊗ₘ η[A]) ≫ fst (𝟙_ C) A)
                = (fst (𝟙_ C) (𝟙_ C)) ≫ 𝟙 (𝟙_ C) :=
              tensorHom_fst (𝟙 (𝟙_ C)) η
            rw[this, Category.assoc]
            simp
          · have : (η[A] ⊗ₘ (𝟙 A)) ≫ snd A A = (snd (𝟙_ C) A) ≫ 𝟙 A :=
              tensorHom_snd η (𝟙 A)
            rw[Category.assoc, this, ← Category.assoc]
            have : ((𝟙 (𝟙_ C) ⊗ₘ η[A]) ≫ snd (𝟙_ C) A)
                = (snd (𝟙_ C) (𝟙_ C)) ≫ η[A] :=
              tensorHom_snd (𝟙 (𝟙_ C)) η
            rw[this, Category.assoc]
            simp
        have : (λ_ (𝟙_ C)).inv ≫ (η[A] ⊗ₘ η[A]) = lift η[A] η[A] := by
          ext <;> simp
        rw[← this, ← this₁, ← Category.assoc, Category.assoc, ← this₀]
        simp

      mul_hom := by
        sorry
    }
  }


#min_imports
