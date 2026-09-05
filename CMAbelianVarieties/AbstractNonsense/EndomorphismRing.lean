import Mathlib
import CMAbelianVarieties.AbstractNonsense.MonHom


open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable (A : C) [MonObj A] [IsCommMonObj A]
variable (B : C) [MonObj B] [IsCommMonObj B]


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

/-
## Addition
-/

instance : Add (Hom (mk A) (mk B)) where
  add f g := {
    hom := (lift f.hom g.hom) ≫ μ[B]
    isMonHom_hom := {
      one_hom := by
        rw[← Category.assoc]
        have : (η[A] ≫ (lift f.hom g.hom)) = (lift η[B] η[B]) := by
          ext
          · simp[@IsMonHom.one_hom _ _ _ _ _ _ _ f.hom (f.isMonHom_hom)]
          · simp[@IsMonHom.one_hom _ _ _ _ _ _ _ g.hom (g.isMonHom_hom)]
        rw[this]
        have this₀ : (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ η[B]) ≫ (λ_ B).hom = η[B] := by
          simp
        have this₁ : (𝟙 (𝟙_ C) ⊗ₘ η[B]) ≫ (η[B] ⊗ₘ 𝟙 B) = η[B] ⊗ₘ η[B] := by
          ext
          · have : (η[B] ⊗ₘ (𝟙 B)) ≫ fst B B = (fst (𝟙_ C) B) ≫ η[B] :=
              tensorHom_fst η (𝟙 B)
            rw[Category.assoc, this, ← Category.assoc]
            have : ((𝟙 (𝟙_ C) ⊗ₘ η[B]) ≫ fst (𝟙_ C) B)
                = (fst (𝟙_ C) (𝟙_ C)) ≫ 𝟙 (𝟙_ C) :=
              tensorHom_fst (𝟙 (𝟙_ C)) η
            rw[this, Category.assoc]
            simp
          · have : (η[B] ⊗ₘ (𝟙 B)) ≫ snd B B = (snd (𝟙_ C) B) ≫ 𝟙 B :=
              tensorHom_snd η (𝟙 B)
            rw[Category.assoc, this, ← Category.assoc]
            have : ((𝟙 (𝟙_ C) ⊗ₘ η[B]) ≫ snd (𝟙_ C) B)
                = (snd (𝟙_ C) (𝟙_ C)) ≫ η[B] :=
              tensorHom_snd (𝟙 (𝟙_ C)) η
            rw[this, Category.assoc]
            simp
        have : (λ_ (𝟙_ C)).inv ≫ (η[B] ⊗ₘ η[B]) = lift η[B] η[B] := by
          ext <;> simp
        rw[← this, ← this₁, ← Category.assoc, Category.assoc, ← this₀]
        simp

      mul_hom := by
        have : μ[A] ≫ lift f.hom g.hom = lift (μ[A] ≫ f.hom) (μ[A] ≫ g.hom) := by
          ext <;> simp
        rw[← Category.assoc, this, f.isMonHom_hom.mul_hom, g.isMonHom_hom.mul_hom]
        have this₀ : lift ((f.hom ⊗ₘ f.hom) ≫ μ) ((g.hom ⊗ₘ g.hom) ≫ μ)
            = lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (μ ⊗ₘ μ) := by
          ext <;> simp
        have this₀₀ : ((lift (f.hom) (g.hom)) ⊗ₘ (lift (f.hom) (g.hom))) ≫ (μ ⊗ₘ μ)
            = (lift f.hom g.hom ≫ μ ⊗ₘ lift f.hom g.hom ≫ μ) := by
          ext <;> simp
        have big_this : (α_ B B (B ⊗ B)).hom ≫ ((𝟙 B) ⊗ₘ (α_ B B B).inv) ≫
            ((𝟙 B) ⊗ₘ μ ⊗ₘ (𝟙 B)) ≫ ((𝟙 B) ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by
          have : (α_ B B (B ⊗ B)).hom ≫ (𝟙 B ⊗ₘ (α_ B B B).inv) ≫
              (𝟙 B ⊗ₘ μ ⊗ₘ 𝟙 B) ≫ (𝟙 B ⊗ₘ μ) ≫ μ
              = (α_ B B (B ⊗ B)).hom ≫ ((𝟙 B ⊗ₘ (α_ B B B).inv) ≫
              (𝟙 B ⊗ₘ μ ⊗ₘ 𝟙 B) ≫ (𝟙 B ⊗ₘ μ)) ≫ μ := by simp
          rw[this]
          have : ((𝟙 B) ⊗ₘ (α_ B B B).inv) ≫ ((𝟙 B) ⊗ₘ μ[B] ⊗ₘ (𝟙 B)) ≫
              ((𝟙 B) ⊗ₘ μ[B])
              = B ◁ ((α_ B B B).inv ≫ (μ ⊗ₘ (𝟙 B)) ≫ μ) := by
            ext <;> simp
          rw[this]
          simp only [tensorHom_id, MonObj.mul_assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp,
            Category.assoc]
          have : B ◁ μ ≫ μ = (α_ B B B).inv ≫ (μ ▷ B) ≫ μ := by simp
          rw[this]
          have : (α_ B B (B ⊗ B)).hom ≫ B ◁ B ◁ μ ≫ (α_ B B B).inv ≫ μ ▷ B ≫ μ
              = ((α_ B B (B ⊗ B)).hom ≫ B ◁ B ◁ μ ≫ (α_ B B B).inv ≫ μ ▷ B) ≫ μ := by simp
          rw[this]
          have : ((α_ B B (B ⊗ B)).hom ≫ B ◁ B ◁ μ ≫ (α_ B B B).inv ≫ μ ▷ B) = μ ⊗ₘ μ := by
            ext
            · have : ((α_ B B (B ⊗ B)).hom ≫ B ◁ B ◁ μ ≫
                  (α_ B B B).inv ≫ μ ▷ B) ≫ fst B B
                  = (((α_ B B (B ⊗ B)).hom ≫ B ◁ B ◁ μ ≫ (α_ B B B).inv) ≫
                  μ ▷ B) ≫ fst B B := by simp
              rw[this]
              have : ((α_ B B (B ⊗ B)).hom ≫ B ◁ B ◁ μ ≫ (α_ B B B).inv)
                  = ((B ⊗ B) ◁ μ[B]) := by simp
              rw[this]
              have : ((B ⊗ B) ◁ μ ≫ μ ▷ B) = μ ⊗ₘ μ := by
                have : ((B ⊗ B) ◁ μ ≫ μ ▷ B) = ((𝟙 (B ⊗ B)) ≫ μ) ⊗ₘ (μ ≫ (𝟙 (B))) := by
                  --simp [comm_square (𝟙 (B ⊗ B)) μ[B] μ[B] (𝟙 B)]
                  have LHS : ((B ⊗ B) ◁ μ ≫ μ ▷ B)
                      = ((𝟙 (B ⊗ B)) ⊗ₘ μ[B]) ≫ (μ[B] ⊗ₘ (𝟙 B)) := by simp
                  have {A B W X Y Z : C} (φ₁ : A ⟶ W) (φ₂ : B ⟶ X) (ψ₁ : W ⟶ Y)
                      (ψ₂ : X ⟶ Z) : (φ₁ ⊗ₘ φ₂) ≫ (ψ₁ ⊗ₘ ψ₂) = (φ₁ ≫ ψ₁) ⊗ₘ (φ₂ ≫ ψ₂) := by
                    ext <;> simp
                  rw[LHS, this (𝟙 (B ⊗ B)) μ[B] μ[B] (𝟙 B)]
                rw[this]
                simp
              rw[this]
            · simp
          rw[this]
        have this₁ : ((𝟙 B) ⊗ₘ ((β_ B B).hom ≫ μ) ⊗ₘ (𝟙 B)) = ((𝟙 B) ⊗ₘ μ[B] ⊗ₘ (𝟙 B)) := by
          rw[IsCommMonObj.mul_comm]
        have THIS : lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫
            ((α_ B B (B ⊗ B)).hom ≫ ((𝟙 B) ⊗ₘ (α_ B B B).inv) ≫
            ((𝟙 B) ⊗ₘ μ[B] ⊗ₘ (𝟙 B)))
            = ((lift (f.hom) (g.hom)) ⊗ₘ (lift (f.hom) (g.hom))) ≫
            (α_ B B (B ⊗ B)).hom ≫ ((𝟙 B) ⊗ₘ (α_ B B B).inv) ≫
            ((𝟙 B) ⊗ₘ ((β_ B B).hom ≫ μ) ⊗ₘ (𝟙 B)) := by
          ext
          · simp
          · simp only [id_tensorHom, tensorHom_id, Category.assoc, whiskerLeft_snd,
            whiskerLeft_snd_assoc, whiskerRight_fst]
            have : lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (α_ B B (B ⊗ B)).hom ≫
                snd B (B ⊗ B ⊗ B) ≫ (α_ B B B).inv ≫ fst (B ⊗ B) B ≫ μ
                = (lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (α_ B B (B ⊗ B)).hom ≫
                snd B (B ⊗ B ⊗ B) ≫ (α_ B B B).inv ≫ fst (B ⊗ B) B) ≫ μ
                := by simp
            rw[this]
            have : lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫
                (α_ B B (B ⊗ B)).hom ≫ snd B (B ⊗ B ⊗ B) ≫ (α_ B B B).inv ≫ fst (B ⊗ B) B
                = (lift f.hom g.hom ⊗ₘ lift f.hom g.hom) ≫ (α_ B B (B ⊗ B)).hom ≫
                snd B (B ⊗ B ⊗ B) ≫ (α_ B B B).inv ≫ fst (B ⊗ B) B ≫ (β_ B B).hom := by
              ext <;> simp
            simp[this]
          · simp
        rw[← this₀₀]
        have : ((lift f.hom g.hom ⊗ₘ lift f.hom g.hom) ≫ (μ ⊗ₘ μ)) ≫ μ
            = ((lift f.hom g.hom ⊗ₘ lift f.hom g.hom) ≫ ((μ ⊗ₘ μ)) ≫ μ) := by simp
        rw[this, ← big_this, ← this₁]
        have : (lift f.hom g.hom ⊗ₘ lift f.hom g.hom) ≫
            (α_ B B (B ⊗ B)).hom ≫ (𝟙 B ⊗ₘ (α_ B B B).inv) ≫ (𝟙 B ⊗ₘ (β_ B B).hom ≫
            μ ⊗ₘ 𝟙 B) ≫ (𝟙 B ⊗ₘ μ) ≫ μ = (((lift (f.hom) (g.hom)) ⊗ₘ (lift (f.hom) (g.hom))) ≫
            (α_ B B (B ⊗ B)).hom ≫ ((𝟙 B) ⊗ₘ (α_ B B B).inv) ≫
            ((𝟙 B) ⊗ₘ ((β_ B B).hom ≫ μ) ⊗ₘ (𝟙 B))) ≫ (𝟙 B ⊗ₘ μ) ≫ μ := by simp
        rw[this, ← THIS]
        have : (lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (α_ B B (B ⊗ B)).hom ≫
            (𝟙 B ⊗ₘ (α_ B B B).inv) ≫ (𝟙 B ⊗ₘ μ ⊗ₘ 𝟙 B)) ≫
            (𝟙 B ⊗ₘ μ) ≫ μ = (lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (((α_ B B (B ⊗ B)).hom ≫
            (𝟙 B ⊗ₘ (α_ B B B).inv) ≫ (𝟙 B ⊗ₘ μ ⊗ₘ 𝟙 B)) ≫ (𝟙 B ⊗ₘ μ) ≫ μ)) := by simp
        -- I am not sure why it is making me create the next `this`
        have this' : (((α_ B B (B ⊗ B)).hom ≫ (𝟙 B ⊗ₘ (α_ B B B).inv) ≫ (𝟙 B ⊗ₘ μ ⊗ₘ 𝟙 B)) ≫
            (𝟙 B ⊗ₘ μ) ≫ μ) = (α_ B B (B ⊗ B)).hom ≫ ((𝟙 B) ⊗ₘ (α_ B B B).inv) ≫
            ((𝟙 B) ⊗ₘ μ ⊗ₘ (𝟙 B)) ≫ ((𝟙 B) ⊗ₘ μ) ≫ μ := by simp
        rw[this, this', big_this]
        have : lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (μ ⊗ₘ μ) ≫ μ
            = (lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (μ ⊗ₘ μ)) ≫ μ := by simp
        rw[this, ← this₀]
    }
  }

set_option linter.unusedSectionVars false
lemma add_def_of_isCommMonObj_Hom (f g : (Hom (mk A) (mk B))) : (f + g).hom = (lift f.hom g.hom) ≫ μ
    := rfl

instance : AddCommSemigroup (Hom (mk A) (mk B)) where
  add f g := f + g
  add_assoc f g h := by
    ext
    simp only [add_def_of_isCommMonObj_Hom]
    have : ((lift (lift f.hom g.hom) (h.hom)) ≫ (μ[B] ▷ B))
        = lift (lift f.hom g.hom ≫ μ) h.hom := by
      ext <;> simp
    rw[← this]
    have : (lift (lift f.hom g.hom) h.hom) ≫ (μ ▷ B) ≫ μ
        = ((lift (lift f.hom g.hom) h.hom) ≫ (μ ▷ B)) ≫ μ := by
      apply Category.assoc'
    simp only [← this, MonObj.mul_assoc, Category.assoc']
    have : ((lift (lift f.hom g.hom) h.hom ≫ (α_ B B B).hom) ≫ B ◁ μ)
        = lift f.hom (lift g.hom h.hom ≫ μ) := by
      ext <;> simp
    rw[this]
  add_comm f g := by
    ext
    simp only [add_def_of_isCommMonObj_Hom]
    nth_rw 1 [← IsCommMonObj.mul_comm B, Category.assoc']
    have : (lift f.hom g.hom ≫ (β_ B B).hom) = lift g.hom f.hom := by
      ext <;> simp
    rw[this]


lemma zero_hom.zero_add (f : Hom (mk A) (mk B)) : (zero_hom A B) + f = f := by
    ext
    rw[add_def_of_isCommMonObj_Hom]
    have : lift (zero_hom A B).hom f.hom
        = lift (toUnit A) (f.hom) ≫ (η ⊗ₘ (𝟙 B)) := by
      ext
      · simp only [lift_fst, tensorHom_id, lift_whiskerRight]; rfl
      · simp only [lift_snd, tensorHom_id, lift_whiskerRight]
    rw[this, Category.assoc]
    simp[MonObj.one_mul B]

instance : AddZeroClass (Hom (mk A) (mk B)) where
  zero := zero_hom A B
  add f g := f + g
  zero_add f := zero_hom.zero_add _ _ f
  add_zero f := by
    rw[add_comm]
    exact zero_hom.zero_add _ _ f

def mon_hom.nsmul (n : ℕ) : (Hom (mk A) (mk B)) →  (Hom (mk A) (mk B)) :=
  match n with
  | Nat.zero => fun _ => 0
  | Nat.succ m => fun f => (mon_hom.nsmul m f) + f

instance : AddCommMonoid (Hom (mk A) (mk B)) where
  add f g := f + g
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  nsmul n := mon_hom.nsmul A B n
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  add_comm := add_comm


instance [GrpObj A] [GrpObj B] : AddCommGroup (Hom (mk A) (mk B)) where
  add f g := f + g
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  neg := sorry
  zsmul := sorry
  sub_eq_add_neg := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  neg_add_cancel := sorry
  add_comm := sorry

/-
## Multiplication
-/



instance : Mul (Hom (mk A) (mk A)) where
  mul f g := {
    hom := g.hom ≫ f.hom
    isMonHom_hom := by infer_instance
  }

lemma mul_def_of_isCommMonObj_Hom (f g : (Hom (mk A) (mk A))) :
    (f * g).hom = g.hom ≫ f.hom := rfl

/-
## Ring structures
-/

set_option linter.style.show false
instance : Semiring (Hom (mk A) (mk A)) where
  mul_assoc f g h := by
    ext
    simp[mul_def_of_isCommMonObj_Hom]
  one := {
    hom := 𝟙 A
    isMonHom_hom := by infer_instance
  }
  one_mul f := by
    ext
    show f.hom ≫ (𝟙 A) = f.hom
    simp only [Category.comp_id]
  mul_one f := by
    ext
    show (𝟙 A) ≫ f.hom = f.hom
    simp only [Category.id_comp]
  zero_mul f := by
    ext
    show f.hom ≫ ((toUnit A) ≫ (MonObj.one : 𝟙_ C ⟶ A)) = ((toUnit A) ≫ (MonObj.one : 𝟙_ C ⟶ A))
    simp only [comp_toUnit_assoc]
  mul_zero f := by
    ext
    show ((toUnit A) ≫ (MonObj.one : 𝟙_ C ⟶ A)) ≫ f.hom = ((toUnit A) ≫ (MonObj.one : 𝟙_ C ⟶ A))
    simp only [Category.assoc, IsMonHom.one_hom]
  left_distrib f g h := by
    ext
    sorry
  right_distrib := sorry

#min_imports
