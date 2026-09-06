module

--import Mathlib
public import CMAbelianVarieties.AbstractNonsense.EndomorphismRing

@[expose] public noncomputable section

open CategoryTheory Limits Mon MonObj MonoidalCategory CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {A : C} [GrpObj A] [IsCommMonObj A]
variable {B : C} [GrpObj B] [IsCommMonObj B]

def GrpHom_ker (f : Hom (mk A) (mk B)) [HasPullback (f.hom) η[B]]
  := pullback (f.hom) η[B]

namespace GrpHom_ker

def one (f : Hom (mk A) (mk B)) [HasPullback (f.hom) η]
    : 𝟙_ C ⟶ (GrpHom_ker f) := by
  have : η[A] ≫ f.hom = (η[𝟙_C]) ≫ η[B] := by
    simp only [IsMonHom.one_hom]
  exact @pullback.lift _ _ _ _ _ _ (f.hom) η[B] _ η[A] (η[𝟙_ C]) this

def p₁ (f : Hom (mk A) (mk B)) [HasPullback (f.hom) η]
  := (pullback.fst (f.hom) η) ⊗ₘ (pullback.fst (f.hom) η)

def p₂ (f : Hom (mk A) (mk B)) [HasPullback (f.hom) η]
  := (pullback.snd (f.hom) η) ⊗ₘ (pullback.snd (f.hom) η)

lemma pre_mul_comm_sq (f : Hom (mk A) (mk B)) [HasPullback (f.hom) η] : (p₁ f ≫ μ) ≫ f.hom
    = (p₂ f≫ μ) ≫ η := by
  simp only [Category.assoc, IsMonHom.mul_hom]
  have : (p₁ f ≫ (f.hom ⊗ₘ f.hom)) = (p₂ f ≫ (η ⊗ₘ η)) := by
    have fst : ((pullback.fst (f.hom) η) ≫
        f.hom) ⊗ₘ ((pullback.fst (f.hom) η) ≫ f.hom) = (p₁ f ≫ (f.hom ⊗ₘ f.hom))
        := by
      ext <;> simp only [tensorHom_fst_assoc, tensorHom_fst, Category.assoc, p₁,
        tensorHom_snd, tensorHom_snd_assoc]
    have snd : ((pullback.snd (f.hom) η) ≫
        η[B]) ⊗ₘ ((pullback.snd (f.hom) η) ≫ η[B]) = (p₂ f ≫ (η ⊗ₘ η))
        := by
      ext <;> simp only [tensorHom_fst_assoc, tensorHom_fst, Category.assoc, p₂,
      tensorHom_snd, tensorHom_snd_assoc]
    rw [← fst, ←  snd]
    have : pullback.fst f.hom η ≫ f.hom = pullback.snd f.hom η ≫ η := by
        exact pullback.condition
    ext <;> simp only [tensorHom_fst, tensorHom_snd, pullback.condition]
  simp only [← Category.assoc, this]


def mul (f : Hom (mk A) (mk B)) [HasPullback (f.hom) η]
    : (GrpHom_ker f) ⊗ (GrpHom_ker f) ⟶ (GrpHom_ker f) := by
  exact @pullback.lift _ _ _ _ _ _ (f.hom) η[B] _ ((p₁ f) ≫ μ) ((p₂ f) ≫ μ) (pre_mul_comm_sq f)


lemma mul_fst (f : Hom (mk A) (mk B)) [HasPullback (f.hom) η] : (mul f) ≫ (pullback.fst f.hom η)
    = ((pullback.fst f.hom η) ⊗ₘ (pullback.fst f.hom η)) ≫ μ := by
  simp
  sorry

instance {f : Hom (mk A) (mk B)} [HasPullback (f.hom) η]
    : GrpObj (GrpHom_ker f) where
      one := one f
      mul := mul f
      one_mul := by
        #check (one f ▷ GrpHom_ker f ≫ mul f) ≫ pullback.fst f.hom η
        #check (λ_ (GrpHom_ker f)).hom ≫ pullback.snd f.hom η
        have h₁ : (one f ▷ GrpHom_ker f ≫ mul f) ≫ pullback.fst f.hom η
            = (λ_ (GrpHom_ker f)).hom ≫ pullback.fst f.hom η := by

          sorry
        have h₂ : (one f ▷ GrpHom_ker f ≫ mul f) ≫ pullback.snd f.hom η
            = (λ_ (GrpHom_ker f)).hom ≫ pullback.snd f.hom η := sorry
        exact pullback.hom_ext h₁ h₂
      mul_one := sorry
      mul_assoc := sorry
      inv := sorry
      left_inv := sorry
      right_inv := sorry

section
variable {X Y : C} {f : A ⟶ X} {g : B ⟶ X} [HasPullback f g]
variable {φ₁ φ₂ : Y ⟶ pullback f g}
variable {ψ₁ : Y ⟶ A} {ψ₂ : Y ⟶ B}

#check pullback.fst f g

example (h₁ : φ₁ ≫ (pullback.fst f g) = φ₂ ≫ (pullback.fst f g))
    (h₂ : φ₁ ≫ (pullback.snd f g) = φ₂ ≫ (pullback.snd f g)) : φ₁ = φ₂ := by
  exact pullback.hom_ext h₁ h₂

#check @pullback.lift _ _ _ _ _ _ f g _

#check Grp.ofHom

end

def factor_map_of_comp_eq_zero {G : C} [GrpObj G] [IsCommMonObj G] {g : Hom (mk G) (mk A)}
    {f : Hom (mk A) (mk B)} [HasPullback f.hom η] (h : g.hom ≫ f.hom = (0 : Hom (mk G) (mk B)).hom)
    : G ⟶ (GrpHom_ker f) := by
  have : g.hom ≫ f.hom = (toUnit G) ≫ η[B] := by
    simp [h]; rfl
  exact @pullback.lift _ _ _ _ _ _ (f.hom) η[B] _ g.hom (toUnit G) this

def factor_of_comp_eq_zero {G : C} [GrpObj G] [IsCommMonObj G] {g : Hom (mk G) (mk A)}
    {f : Hom (mk A) (mk B)} [HasPullback f.hom η] (h : g.hom ≫ f.hom = (0 : Hom (mk G) (mk B)).hom)
    : Hom (mk G) (mk (GrpHom_ker f)) where
      hom := factor_map_of_comp_eq_zero h
      isMonHom_hom := {
        one_hom := by
          #check IsMonHom.one_hom
          sorry
        mul_hom := sorry
      }

#check HasPullbacks

#min_imports
