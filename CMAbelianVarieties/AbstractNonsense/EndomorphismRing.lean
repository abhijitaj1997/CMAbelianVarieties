module

--import Mathlib
public import CMAbelianVarieties.AbstractNonsense.MonHom

@[expose] public section

open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {G : C} [MonObj G] [IsCommMonObj G]
variable {H : C} [MonObj H] [IsCommMonObj H]
variable {A : C} [GrpObj A] [IsCommMonObj A]
variable {B : C} [GrpObj B] [IsCommMonObj B]


abbrev EndRing (A₀ : C) [MonObj A₀] [IsCommMonObj A₀] := Hom (mk A₀) (mk A₀)



/-
## Addition
-/


/-
Is `G` and `H` are monoidal object in a Cartesian Monoidal Category, the monoidal
homomorphisms between them has a natural addition
-/
instance : Add (Hom (mk G) (mk H)) where
  add f g := {
    hom := (lift f.hom g.hom) ≫ μ[H]
    isMonHom_hom := {
      one_hom := by
        rw[← Category.assoc]
        have : (η[G] ≫ (lift f.hom g.hom)) = (lift η[H] η[H]) := by
          ext
          · simp[@IsMonHom.one_hom _ _ _ _ _ _ _ f.hom (f.isMonHom_hom)]
          · simp[@IsMonHom.one_hom _ _ _ _ _ _ _ g.hom (g.isMonHom_hom)]
        rw[this]
        have this₀ : (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ η[H]) ≫ (λ_ H).hom = η[H] := by
          simp
        have this₁ : (𝟙 (𝟙_ C) ⊗ₘ η[H]) ≫ (η[H] ⊗ₘ 𝟙 H) = η[H] ⊗ₘ η[H] := by
          ext
          · have : (η[H] ⊗ₘ (𝟙 H)) ≫ fst H H = (fst (𝟙_ C) H) ≫ η[H] :=
              tensorHom_fst η (𝟙 H)
            rw[Category.assoc, this, ← Category.assoc]
            have : ((𝟙 (𝟙_ C) ⊗ₘ η[H]) ≫ fst (𝟙_ C) H)
                = (fst (𝟙_ C) (𝟙_ C)) ≫ 𝟙 (𝟙_ C) :=
              tensorHom_fst (𝟙 (𝟙_ C)) η
            rw[this, Category.assoc]
            simp
          · have : (η[H] ⊗ₘ (𝟙 H)) ≫ snd H H = (snd (𝟙_ C) H) ≫ 𝟙 H :=
              tensorHom_snd η (𝟙 H)
            rw[Category.assoc, this, ← Category.assoc]
            have : ((𝟙 (𝟙_ C) ⊗ₘ η[H]) ≫ snd (𝟙_ C) H)
                = (snd (𝟙_ C) (𝟙_ C)) ≫ η[H] :=
              tensorHom_snd (𝟙 (𝟙_ C)) η
            rw[this, Category.assoc]
            simp
        have : (λ_ (𝟙_ C)).inv ≫ (η[H] ⊗ₘ η[H]) = lift η[H] η[H] := by
          ext <;> simp
        rw[← this, ← this₁, ← Category.assoc, Category.assoc, ← this₀]
        simp

      mul_hom := by
        have : μ[G] ≫ lift f.hom g.hom = lift (μ[G] ≫ f.hom) (μ[G] ≫ g.hom) := by
          ext <;> simp
        rw[← Category.assoc, this, f.isMonHom_hom.mul_hom, g.isMonHom_hom.mul_hom]
        have this₀ : lift ((f.hom ⊗ₘ f.hom) ≫ μ) ((g.hom ⊗ₘ g.hom) ≫ μ)
            = lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (μ ⊗ₘ μ) := by
          ext <;> simp
        have this₀₀ : ((lift (f.hom) (g.hom)) ⊗ₘ (lift (f.hom) (g.hom))) ≫ (μ ⊗ₘ μ)
            = (lift f.hom g.hom ≫ μ ⊗ₘ lift f.hom g.hom ≫ μ) := by
          ext <;> simp
        have big_this : (α_ H H (H ⊗ H)).hom ≫ ((𝟙 H) ⊗ₘ (α_ H H H).inv) ≫
            ((𝟙 H) ⊗ₘ μ ⊗ₘ (𝟙 H)) ≫ ((𝟙 H) ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by
          have : (α_ H H (H ⊗ H)).hom ≫ (𝟙 H ⊗ₘ (α_ H H H).inv) ≫
              (𝟙 H ⊗ₘ μ ⊗ₘ 𝟙 H) ≫ (𝟙 H ⊗ₘ μ) ≫ μ
              = (α_ H H (H ⊗ H)).hom ≫ ((𝟙 H ⊗ₘ (α_ H H H).inv) ≫
              (𝟙 H ⊗ₘ μ ⊗ₘ 𝟙 H) ≫ (𝟙 H ⊗ₘ μ)) ≫ μ := by simp
          rw[this]
          have : ((𝟙 H) ⊗ₘ (α_ H H H).inv) ≫ ((𝟙 H) ⊗ₘ μ[H] ⊗ₘ (𝟙 H)) ≫
              ((𝟙 H) ⊗ₘ μ[H])
              = H ◁ ((α_ H H H).inv ≫ (μ ⊗ₘ (𝟙 H)) ≫ μ) := by
            ext <;> simp
          rw[this]
          simp only [tensorHom_id, MonObj.mul_assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp,
            Category.assoc]
          have : H ◁ μ ≫ μ = (α_ H H H).inv ≫ (μ ▷ H) ≫ μ := by simp
          rw[this]
          have : (α_ H H (H ⊗ H)).hom ≫ H ◁ H ◁ μ ≫ (α_ H H H).inv ≫ μ ▷ H ≫ μ
              = ((α_ H H (H ⊗ H)).hom ≫ H ◁ H ◁ μ ≫ (α_ H H H).inv ≫ μ ▷ H) ≫ μ := by simp
          rw[this]
          have : ((α_ H H (H ⊗ H)).hom ≫ H ◁ H ◁ μ ≫ (α_ H H H).inv ≫ μ ▷ H) = μ ⊗ₘ μ := by
            ext
            · have : ((α_ H H (H ⊗ H)).hom ≫ H ◁ H ◁ μ ≫
                  (α_ H H H).inv ≫ μ ▷ H) ≫ fst H H
                  = (((α_ H H (H ⊗ H)).hom ≫ H ◁ H ◁ μ ≫ (α_ H H H).inv) ≫
                  μ ▷ H) ≫ fst H H := by simp
              rw[this]
              have : ((α_ H H (H ⊗ H)).hom ≫ H ◁ H ◁ μ ≫ (α_ H H H).inv)
                  = ((H ⊗ H) ◁ μ[H]) := by simp
              rw[this]
              have : ((H ⊗ H) ◁ μ ≫ μ ▷ H) = μ ⊗ₘ μ := by
                have : ((H ⊗ H) ◁ μ ≫ μ ▷ H) = ((𝟙 (H ⊗ H)) ≫ μ) ⊗ₘ (μ ≫ (𝟙 (H))) := by
                  have LHS : ((H ⊗ H) ◁ μ ≫ μ ▷ H)
                      = ((𝟙 (H ⊗ H)) ⊗ₘ μ[H]) ≫ (μ[H] ⊗ₘ (𝟙 H)) := by simp
                  have {U V W X Y Z : C} (φ₁ : U ⟶ W) (φ₂ : V ⟶ X) (ψ₁ : W ⟶ Y)
                      (ψ₂ : X ⟶ Z) : (φ₁ ⊗ₘ φ₂) ≫ (ψ₁ ⊗ₘ ψ₂) = (φ₁ ≫ ψ₁) ⊗ₘ (φ₂ ≫ ψ₂) := by
                    ext <;> simp
                  rw[LHS, this (𝟙 (H ⊗ H)) μ[H] μ[H] (𝟙 H)]
                rw[this]
                simp
              rw[this]
            · simp
          rw[this]
        have this₁ : ((𝟙 H) ⊗ₘ ((β_ H H).hom ≫ μ) ⊗ₘ (𝟙 H)) = ((𝟙 H) ⊗ₘ μ[H] ⊗ₘ (𝟙 H)) := by
          rw[IsCommMonObj.mul_comm]
        have THIS : lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫
            ((α_ H H (H ⊗ H)).hom ≫ ((𝟙 H) ⊗ₘ (α_ H H H).inv) ≫
            ((𝟙 H) ⊗ₘ μ[H] ⊗ₘ (𝟙 H)))
            = ((lift (f.hom) (g.hom)) ⊗ₘ (lift (f.hom) (g.hom))) ≫
            (α_ H H (H ⊗ H)).hom ≫ ((𝟙 H) ⊗ₘ (α_ H H H).inv) ≫
            ((𝟙 H) ⊗ₘ ((β_ H H).hom ≫ μ) ⊗ₘ (𝟙 H)) := by
          ext
          · simp
          · simp only [id_tensorHom, tensorHom_id, Category.assoc, whiskerLeft_snd,
            whiskerLeft_snd_assoc, whiskerRight_fst]
            have : lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (α_ H H (H ⊗ H)).hom ≫
                snd H (H ⊗ H ⊗ H) ≫ (α_ H H H).inv ≫ fst (H ⊗ H) H ≫ μ
                = (lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (α_ H H (H ⊗ H)).hom ≫
                snd H (H ⊗ H ⊗ H) ≫ (α_ H H H).inv ≫ fst (H ⊗ H) H) ≫ μ
                := by simp
            rw[this]
            have : lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫
                (α_ H H (H ⊗ H)).hom ≫ snd H (H ⊗ H ⊗ H) ≫ (α_ H H H).inv ≫ fst (H ⊗ H) H
                = (lift f.hom g.hom ⊗ₘ lift f.hom g.hom) ≫ (α_ H H (H ⊗ H)).hom ≫
                snd H (H ⊗ H ⊗ H) ≫ (α_ H H H).inv ≫ fst (H ⊗ H) H ≫ (β_ H H).hom := by
              ext <;> simp
            simp[this]
          · simp
        rw[← this₀₀]
        have : ((lift f.hom g.hom ⊗ₘ lift f.hom g.hom) ≫ (μ ⊗ₘ μ)) ≫ μ
            = ((lift f.hom g.hom ⊗ₘ lift f.hom g.hom) ≫ ((μ ⊗ₘ μ)) ≫ μ) := by simp
        rw[this, ← big_this, ← this₁]
        have : (lift f.hom g.hom ⊗ₘ lift f.hom g.hom) ≫
            (α_ H H (H ⊗ H)).hom ≫ (𝟙 H ⊗ₘ (α_ H H H).inv) ≫ (𝟙 H ⊗ₘ (β_ H H).hom ≫
            μ ⊗ₘ 𝟙 H) ≫ (𝟙 H ⊗ₘ μ) ≫ μ = (((lift (f.hom) (g.hom)) ⊗ₘ (lift (f.hom) (g.hom))) ≫
            (α_ H H (H ⊗ H)).hom ≫ ((𝟙 H) ⊗ₘ (α_ H H H).inv) ≫
            ((𝟙 H) ⊗ₘ ((β_ H H).hom ≫ μ) ⊗ₘ (𝟙 H))) ≫ (𝟙 H ⊗ₘ μ) ≫ μ := by simp
        rw[this, ← THIS]
        have : (lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (α_ H H (H ⊗ H)).hom ≫
            (𝟙 H ⊗ₘ (α_ H H H).inv) ≫ (𝟙 H ⊗ₘ μ ⊗ₘ 𝟙 H)) ≫
            (𝟙 H ⊗ₘ μ) ≫ μ = (lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (((α_ H H (H ⊗ H)).hom ≫
            (𝟙 H ⊗ₘ (α_ H H H).inv) ≫ (𝟙 H ⊗ₘ μ ⊗ₘ 𝟙 H)) ≫ (𝟙 H ⊗ₘ μ) ≫ μ)) := by simp
        -- I am not sure why it is making me create the next `this`
        have this' : (((α_ H H (H ⊗ H)).hom ≫ (𝟙 H ⊗ₘ (α_ H H H).inv) ≫ (𝟙 H ⊗ₘ μ ⊗ₘ 𝟙 H)) ≫
            (𝟙 H ⊗ₘ μ) ≫ μ) = (α_ H H (H ⊗ H)).hom ≫ ((𝟙 H) ⊗ₘ (α_ H H H).inv) ≫
            ((𝟙 H) ⊗ₘ μ ⊗ₘ (𝟙 H)) ≫ ((𝟙 H) ⊗ₘ μ) ≫ μ := by simp
        rw[this, this', big_this]
        have : lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (μ ⊗ₘ μ) ≫ μ
            = (lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (μ ⊗ₘ μ)) ≫ μ := by simp
        rw[this, ← this₀]
    }
  }

set_option linter.unusedSectionVars false
lemma add_def_of_isCommMonObj_Hom (f g : (Hom (mk G) (mk H))) : (f + g).hom = (lift f.hom g.hom) ≫ μ
    := rfl

instance : AddCommSemigroup (Hom (mk G) (mk H)) where
  add f g := f + g
  add_assoc f g h := by
    ext
    simp only [add_def_of_isCommMonObj_Hom]
    have : ((lift (lift f.hom g.hom) (h.hom)) ≫ (μ[H] ▷ H))
        = lift (lift f.hom g.hom ≫ μ) h.hom := by
      ext <;> simp
    rw[← this]
    have : (lift (lift f.hom g.hom) h.hom) ≫ (μ ▷ H) ≫ μ
        = ((lift (lift f.hom g.hom) h.hom) ≫ (μ ▷ H)) ≫ μ := by
      apply Category.assoc'
    simp only [← this, MonObj.mul_assoc, Category.assoc']
    have : ((lift (lift f.hom g.hom) h.hom ≫ (α_ H H H).hom) ≫ H ◁ μ)
        = lift f.hom (lift g.hom h.hom ≫ μ) := by
      ext <;> simp
    rw[this]
  add_comm f g := by
    ext
    simp only [add_def_of_isCommMonObj_Hom]
    nth_rw 1 [← IsCommMonObj.mul_comm H, ← Category.assoc,
      lift_braiding_hom f.hom g.hom]


lemma zero_hom.zero_add (f : Hom (mk G) (mk H)) : (zero_hom G H) + f = f := by
    ext
    rw[add_def_of_isCommMonObj_Hom]
    have : lift (zero_hom G H).hom f.hom
        = lift (toUnit G) (f.hom) ≫ (η ⊗ₘ (𝟙 H)) := by
      ext
      · simp only [lift_fst, tensorHom_id, lift_whiskerRight]; rfl
      · simp only [lift_snd, tensorHom_id, lift_whiskerRight]
    rw[this, Category.assoc]
    simp[MonObj.one_mul H]

instance : AddZeroClass (Hom (mk G) (mk H)) where
  zero := zero_hom G H
  add f g := f + g
  zero_add f := zero_hom.zero_add f
  add_zero f := by
    rw[add_comm]
    exact zero_hom.zero_add f

def mon_hom.nsmul (n : ℕ) : (Hom (mk G) (mk H)) →  (Hom (mk G) (mk H)) :=
  match n with
  | Nat.zero => fun _ => 0
  | Nat.succ m => fun f => (mon_hom.nsmul m f) + f

def mon_hom.zsmul (n : ℤ) : (Hom (mk A) (mk B)) → (Hom (mk A) (mk B)) :=
  match n with
  | Int.ofNat m => mon_hom.nsmul m
  | Int.negSucc m => fun f => {
      hom := inv_comp (mon_hom.nsmul (m + 1) f).hom
      isMonHom_hom := by infer_instance
  }


/-
Is `G` and `H` are commutative monoidal object in a Cartesian Monoidal Category,
the monoidal homomorphisms between them has a natural additive commutative
monoid structure
-/
instance : AddCommMonoid (Hom (mk G) (mk H)) where
  add f g := f + g
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  nsmul := mon_hom.nsmul
  add_comm := add_comm


instance : AddCommGroup (Hom (mk A) (mk B)) where
  add f g := f + g
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  neg f := {
    hom := inv_comp f.hom
    isMonHom_hom := by infer_instance
  }
  zsmul := mon_hom.zsmul
  neg_add_cancel f := by
    ext
    simp only [add_def_of_isCommMonObj_Hom]
    have : lift (inv_comp f.hom) f.hom = f.hom ≫ (lift ι (𝟙 B)) := by
      ext
      · simp only [lift_fst, comp_lift, Category.comp_id]
        rfl
      · simp only [lift_snd, comp_lift, Category.comp_id]
    simp only [this, Category.assoc, GrpObj.left_inv, comp_toUnit_assoc]
    rfl
  add_comm := add_comm






/-
## Multiplication
-/

instance : Mul (Hom (mk G) (mk G)) where
  mul f g := {
    hom := g.hom ≫ f.hom
    isMonHom_hom := by infer_instance
  }

lemma mul_def_of_isCommMonObj_Hom (f g : (Hom (mk G) (mk G))) :
    (f * g).hom = g.hom ≫ f.hom := rfl





/-
## Ring structures
-/

set_option linter.style.show false
instance : Semiring (Hom (mk G) (mk G)) where
  mul_assoc f g h := by
    ext
    simp[mul_def_of_isCommMonObj_Hom]
  one := {
    hom := 𝟙 G
    isMonHom_hom := by infer_instance
  }
  one_mul f := by
    ext
    show f.hom ≫ (𝟙 G) = f.hom
    simp only [Category.comp_id]
  mul_one f := by
    ext
    show (𝟙 G) ≫ f.hom = f.hom
    simp only [Category.id_comp]
  zero_mul f := by
    ext
    show f.hom ≫ ((toUnit G) ≫ (MonObj.one : 𝟙_ C ⟶ G)) = ((toUnit G) ≫ (MonObj.one : 𝟙_ C ⟶ G))
    simp only [comp_toUnit_assoc]
  mul_zero f := by
    ext
    show ((toUnit G) ≫ (MonObj.one : 𝟙_ C ⟶ G)) ≫ f.hom = ((toUnit G) ≫ (MonObj.one : 𝟙_ C ⟶ G))
    simp only [Category.assoc, IsMonHom.one_hom]
  left_distrib f g h := by
    ext
    simp only [mul_def_of_isCommMonObj_Hom, add_def_of_isCommMonObj_Hom,
      Category.assoc, IsMonHom.mul_hom f.hom]
    have : lift (g.hom ≫ f.hom) (h.hom ≫ f.hom)
        = lift g.hom h.hom ≫ (f.hom ⊗ₘ f.hom) := by ext <;> simp
    rw[this, Category.assoc]
  right_distrib f g h := by
    ext
    simp only [mul_def_of_isCommMonObj_Hom, add_def_of_isCommMonObj_Hom]
    rw[← Category.assoc]
    have : lift (h.hom ≫ f.hom) (h.hom ≫ g.hom)
        = (h.hom ≫ lift f.hom g.hom) := by ext <;> simp
    rw[this]




instance : Ring (Hom (mk A) (mk A)) where
  zero_add := zero_add
  add_zero := add_zero
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := left_distrib
  right_distrib := right_distrib
  neg_add_cancel := neg_add_cancel

#min_imports
