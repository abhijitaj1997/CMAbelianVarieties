module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon

@[expose] public section

open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {G : Mon C}
variable {H : Mon C} [IsCommMonObj H.X]

/-
If `G` and `H` are monoidal object in a Cartesian Monoidal Category, where `H` has a
commutative monoidal structure, the monoidal homomorphisms between them have a natural
addition.

We use the additive notation here for two reasons:
1. Multiplication of functions usually means compositon
2. The additive structure will later be part of a ring strucutre.
-/
instance : Add (Hom G H) where
  add f g := {
    hom := (lift f.hom g.hom) ≫ μ[H.X]
    isMonHom_hom := {
      one_hom := by
        rw[← Category.assoc]
        have : (η[G.X] ≫ (lift f.hom g.hom)) = (lift η[H.X] η[H.X]) := by
          ext
          · simp[@IsMonHom.one_hom _ _ _ _ _ _ _ f.hom (f.isMonHom_hom)]
          · simp[@IsMonHom.one_hom _ _ _ _ _ _ _ g.hom (g.isMonHom_hom)]
        rw[this]
        have this₀ : (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ η[H.X]) ≫ (λ_ H.X).hom = η[H.X] := by
          simp only [id_tensorHom, id_whiskerLeft, IsMonHom.one_hom, Category.assoc,
            Iso.inv_hom_id_assoc]
        have this₁ : (𝟙 (𝟙_ C) ⊗ₘ η[H.X]) ≫ (η[H.X] ⊗ₘ 𝟙 H.X) = η[H.X] ⊗ₘ η[H.X] := by
          ext
          · have : (η[H.X] ⊗ₘ (𝟙 H.X)) ≫ fst H.X H.X = (fst (𝟙_ C) H.X) ≫ η[H.X] :=
              tensorHom_fst η (𝟙 H.X)
            rw[Category.assoc, this, ← Category.assoc]
            have : ((𝟙 (𝟙_ C) ⊗ₘ η[H.X]) ≫ fst (𝟙_ C) H.X)
                = (fst (𝟙_ C) (𝟙_ C)) ≫ 𝟙 (𝟙_ C) :=
              tensorHom_fst (𝟙 (𝟙_ C)) η
            rw[this, Category.assoc]
            simp only [Category.id_comp, tensorHom_fst]
          · have : (η[H.X] ⊗ₘ (𝟙 H.X)) ≫ snd H.X H.X = (snd (𝟙_ C) H.X) ≫ 𝟙 H.X :=
              tensorHom_snd η (𝟙 H.X)
            rw[Category.assoc, this, ← Category.assoc]
            have : ((𝟙 (𝟙_ C) ⊗ₘ η[H.X]) ≫ snd (𝟙_ C) H.X)
                = (snd (𝟙_ C) (𝟙_ C)) ≫ η[H.X] :=
              tensorHom_snd (𝟙 (𝟙_ C)) η
            rw[this, Category.assoc]
            simp only [Category.comp_id, tensorHom_snd]
        have : (λ_ (𝟙_ C)).inv ≫ (η[H.X] ⊗ₘ η[H.X]) = lift η[H.X] η[H.X] := by
          ext <;> simp only [Category.assoc, tensorHom_fst, leftUnitor_inv_fst_assoc, toUnit_unit,
            Category.id_comp, lift_fst,tensorHom_snd, leftUnitor_inv_snd_assoc,
            lift_snd]
        rw[← this, ← this₁, ← Category.assoc, Category.assoc, ← this₀]
        simp only [id_tensorHom, id_whiskerLeft, IsMonHom.one_hom, Category.assoc,
          Iso.inv_hom_id_assoc, tensorHom_id, MonObj.one_mul]

      mul_hom := by
        have : μ[G.X] ≫ lift f.hom g.hom = lift (μ[G.X] ≫ f.hom) (μ[G.X] ≫ g.hom) := by
          ext <;> simp only [comp_lift, IsMonHom.mul_hom, lift_fst,lift_snd]
        rw[← Category.assoc, this, f.isMonHom_hom.mul_hom, g.isMonHom_hom.mul_hom]
        have this₀ : lift ((f.hom ⊗ₘ f.hom) ≫ μ) ((g.hom ⊗ₘ g.hom) ≫ μ)
            = lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (μ ⊗ₘ μ) := by
          ext <;> simp only [lift_fst, lift_snd, lift_map]
        have this₀₀ : ((lift (f.hom) (g.hom)) ⊗ₘ (lift (f.hom) (g.hom))) ≫ (μ ⊗ₘ μ)
            = (lift f.hom g.hom ≫ μ ⊗ₘ lift f.hom g.hom ≫ μ) := by
          ext <;> simp only [tensorHom_comp_tensorHom, tensorHom_fst, tensorHom_snd]
        have big_this : (α_ H.X H.X (H.X ⊗ H.X)).hom ≫ ((𝟙 H.X) ⊗ₘ (α_ H.X H.X H.X).inv) ≫
            ((𝟙 H.X) ⊗ₘ μ ⊗ₘ (𝟙 H.X)) ≫ ((𝟙 H.X) ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by
          have : (α_ H.X H.X (H.X ⊗ H.X)).hom ≫ (𝟙 H.X ⊗ₘ (α_ H.X H.X H.X).inv) ≫
              (𝟙 H.X ⊗ₘ μ ⊗ₘ 𝟙 H.X) ≫ (𝟙 H.X ⊗ₘ μ) ≫ μ
              = (α_ H.X H.X (H.X ⊗ H.X)).hom ≫ ((𝟙 H.X ⊗ₘ (α_ H.X H.X H.X).inv) ≫
              (𝟙 H.X ⊗ₘ μ ⊗ₘ 𝟙 H.X) ≫ (𝟙 H.X ⊗ₘ μ)) ≫ μ := by simp
          rw[this]
          have : ((𝟙 H.X) ⊗ₘ (α_ H.X H.X H.X).inv) ≫ ((𝟙 H.X) ⊗ₘ μ[H.X] ⊗ₘ (𝟙 H.X)) ≫
              ((𝟙 H.X) ⊗ₘ μ[H.X])
              = H.X ◁ ((α_ H.X H.X H.X).inv ≫ (μ ⊗ₘ (𝟙 H.X)) ≫ μ) := by
            ext <;> simp
          rw[this]
          simp only [tensorHom_id, MonObj.mul_assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp,
            Category.assoc]
          have : H.X ◁ μ ≫ μ = (α_ H.X H.X H.X).inv ≫ (μ ▷ H.X) ≫ μ := by simp
          rw[this]
          have : (α_ H.X H.X (H.X ⊗ H.X)).hom ≫ H.X ◁ H.X ◁ μ ≫ (α_ H.X H.X H.X).inv ≫ μ ▷ H.X ≫ μ
              = ((α_ H.X H.X (H.X ⊗ H.X)).hom ≫ H.X ◁ H.X ◁ μ ≫
              (α_ H.X H.X H.X).inv ≫ μ ▷ H.X) ≫ μ := by simp only [MonObj.mul_assoc,
                Iso.inv_hom_id_assoc, Category.assoc]
          rw[this]
          have : ((α_ H.X H.X (H.X ⊗ H.X)).hom ≫ H.X ◁ H.X ◁ μ ≫ (α_ H.X H.X H.X).inv ≫
               μ ▷ H.X) = μ ⊗ₘ μ := by
            ext
            · have : ((α_ H.X H.X (H.X ⊗ H.X)).hom ≫ H.X ◁ H.X ◁ μ ≫
                  (α_ H.X H.X H.X).inv ≫ μ ▷ H.X) ≫ fst H.X H.X
                  = (((α_ H.X H.X (H.X ⊗ H.X)).hom ≫ H.X ◁ H.X ◁ μ ≫ (α_ H.X H.X H.X).inv) ≫
                  μ ▷ H.X) ≫ fst H.X H.X := by simp only [Category.assoc, whiskerRight_fst]
              rw[this]
              have : ((α_ H.X H.X (H.X ⊗ H.X)).hom ≫ H.X ◁ H.X ◁ μ ≫ (α_ H.X H.X H.X).inv)
                  = ((H.X ⊗ H.X) ◁ μ[H.X]) := by simp only [tensor_whiskerLeft]
              rw[this]
              have : ((H.X ⊗ H.X) ◁ μ ≫ μ ▷ H.X) = μ ⊗ₘ μ := by
                have : ((H.X ⊗ H.X) ◁ μ ≫ μ ▷ H.X) = ((𝟙 (H.X ⊗ H.X)) ≫ μ) ⊗ₘ (μ ≫ (𝟙 (H.X))) := by
                  have LHS : ((H.X ⊗ H.X) ◁ μ ≫ μ ▷ H.X)
                      = ((𝟙 (H.X ⊗ H.X)) ⊗ₘ μ[H.X]) ≫ (μ[H.X] ⊗ₘ (𝟙 H.X)) := by simp
                  have {U V W X Y Z : C} (φ₁ : U ⟶ W) (φ₂ : V ⟶ X) (ψ₁ : W ⟶ Y)
                      (ψ₂ : X ⟶ Z) : (φ₁ ⊗ₘ φ₂) ≫ (ψ₁ ⊗ₘ ψ₂) = (φ₁ ≫ ψ₁) ⊗ₘ (φ₂ ≫ ψ₂) := by
                    ext <;> simp
                  rw[LHS, this (𝟙 (H.X ⊗ H.X)) μ[H.X] μ[H.X] (𝟙 H.X)]
                rw[this]
                simp only [Category.id_comp, Category.comp_id]
              rw[this]
            · simp only [Category.assoc, whiskerRight_snd, associator_inv_snd,
              whiskerLeft_snd_assoc, whiskerLeft_snd, associator_hom_snd_snd_assoc, tensorHom_snd]
          rw[this]
        have this₁ : ((𝟙 H.X) ⊗ₘ ((β_ H.X H.X).hom ≫ μ) ⊗ₘ (𝟙 H.X)) = ((𝟙 H.X) ⊗ₘ μ[H.X] ⊗ₘ (𝟙 H.X))
            := by rw[IsCommMonObj.mul_comm]
        have THIS : lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫
            ((α_ H.X H.X (H.X ⊗ H.X)).hom ≫ ((𝟙 H.X) ⊗ₘ (α_ H.X H.X H.X).inv) ≫
            ((𝟙 H.X) ⊗ₘ μ[H.X] ⊗ₘ (𝟙 H.X)))
            = ((lift (f.hom) (g.hom)) ⊗ₘ (lift (f.hom) (g.hom))) ≫
            (α_ H.X H.X (H.X ⊗ H.X)).hom ≫ ((𝟙 H.X) ⊗ₘ (α_ H.X H.X H.X).inv) ≫
            ((𝟙 H.X) ⊗ₘ ((β_ H.X H.X).hom ≫ μ) ⊗ₘ (𝟙 H.X)) := by
          ext
          · simp only [id_tensorHom, tensorHom_id, Category.assoc, whiskerLeft_fst,
            associator_hom_fst, lift_fst_assoc, tensorHom_fst, IsCommMonObj.mul_comm,
            tensorHom_fst_assoc, lift_fst]
          · simp only [id_tensorHom, tensorHom_id, Category.assoc, whiskerLeft_snd,
            whiskerLeft_snd_assoc, whiskerRight_fst]
            have : lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (α_ H.X H.X (H.X ⊗ H.X)).hom ≫
                snd H.X (H.X ⊗ H.X ⊗ H.X) ≫ (α_ H.X H.X H.X).inv ≫ fst (H.X ⊗ H.X) H.X ≫ μ
                = (lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (α_ H.X H.X (H.X ⊗ H.X)).hom ≫
                snd H.X (H.X ⊗ H.X ⊗ H.X) ≫ (α_ H.X H.X H.X).inv ≫ fst (H.X ⊗ H.X) H.X) ≫ μ
                := by simp
            rw[this]
            have : lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫
                (α_ H.X H.X (H.X ⊗ H.X)).hom ≫ snd H.X (H.X ⊗ H.X ⊗ H.X) ≫ (α_ H.X H.X H.X).inv ≫
                fst (H.X ⊗ H.X) H.X
                = (lift f.hom g.hom ⊗ₘ lift f.hom g.hom) ≫ (α_ H.X H.X (H.X ⊗ H.X)).hom ≫
                snd H.X (H.X ⊗ H.X ⊗ H.X) ≫ (α_ H.X H.X H.X).inv ≫ fst (H.X ⊗ H.X) H.X ≫
                (β_ H.X H.X).hom := by
              ext <;> simp only [Category.assoc, associator_inv_fst_fst, associator_hom_snd_fst,
                lift_fst_assoc, tensorHom_snd, braiding_hom_fst, associator_inv_fst_snd,
                associator_hom_snd_snd_assoc, tensorHom_snd_assoc, lift_fst,lift_snd_assoc,
                  tensorHom_fst, braiding_hom_snd, associator_inv_fst_fst, associator_hom_snd_fst,
                  tensorHom_fst_assoc, lift_snd]
            simp only [Category.assoc, IsCommMonObj.mul_comm, this]
          · simp only [id_tensorHom, tensorHom_id, Category.assoc, whiskerLeft_snd,
            whiskerLeft_snd_assoc, whiskerRight_snd, associator_inv_snd,
            associator_hom_snd_snd_assoc, lift_snd_assoc, tensorHom_snd, IsCommMonObj.mul_comm,
            tensorHom_snd_assoc, lift_snd]
        rw[← this₀₀]
        have : ((lift f.hom g.hom ⊗ₘ lift f.hom g.hom) ≫ (μ ⊗ₘ μ)) ≫ μ
            = ((lift f.hom g.hom ⊗ₘ lift f.hom g.hom) ≫ ((μ ⊗ₘ μ)) ≫ μ)
          := by simp only [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc]
        rw[this, ← big_this, ← this₁]
        have : (lift f.hom g.hom ⊗ₘ lift f.hom g.hom) ≫
            (α_ H.X H.X (H.X ⊗ H.X)).hom ≫ (𝟙 H.X ⊗ₘ (α_ H.X H.X H.X).inv) ≫
            (𝟙 H.X ⊗ₘ (β_ H.X H.X).hom ≫ μ ⊗ₘ 𝟙 H.X) ≫ (𝟙 H.X ⊗ₘ μ) ≫ μ = (((lift (f.hom) (g.hom))
            ⊗ₘ (lift (f.hom) (g.hom))) ≫ (α_ H.X H.X (H.X ⊗ H.X)).hom ≫ ((𝟙 H.X) ⊗ₘ
            (α_ H.X H.X H.X).inv) ≫ ((𝟙 H.X) ⊗ₘ ((β_ H.X H.X).hom ≫ μ) ⊗ₘ (𝟙 H.X))) ≫ (𝟙 H.X ⊗ₘ μ) ≫
            μ := by simp only [id_tensorHom, IsCommMonObj.mul_comm, tensorHom_id, Category.assoc]
        rw[this, ← THIS]
        have : (lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (α_ H.X H.X (H.X ⊗ H.X)).hom ≫
            (𝟙 H.X ⊗ₘ (α_ H.X H.X H.X).inv) ≫ (𝟙 H.X ⊗ₘ μ ⊗ₘ 𝟙 H.X)) ≫
            (𝟙 H.X ⊗ₘ μ) ≫ μ = (lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (((α_ H.X H.X (H.X ⊗
            H.X)).hom ≫ (𝟙 H.X ⊗ₘ (α_ H.X H.X H.X).inv) ≫ (𝟙 H.X ⊗ₘ μ ⊗ₘ 𝟙 H.X)) ≫
            (𝟙 H.X ⊗ₘ μ) ≫ μ))
            := by simp only [id_tensorHom, tensorHom_id, Category.assoc]
        -- I am not sure why it is making me create the next `this`
        have this' : (((α_ H.X H.X (H.X ⊗ H.X)).hom ≫ (𝟙 H.X ⊗ₘ (α_ H.X H.X H.X).inv) ≫ (𝟙 H.X ⊗ₘ μ
            ⊗ₘ 𝟙 H.X)) ≫ (𝟙 H.X ⊗ₘ μ) ≫ μ) = (α_ H.X H.X (H.X ⊗ H.X)).hom ≫ ((𝟙 H.X) ⊗ₘ
            (α_ H.X H.X H.X).inv) ≫ ((𝟙 H.X) ⊗ₘ μ ⊗ₘ (𝟙 H.X)) ≫ ((𝟙 H.X) ⊗ₘ μ) ≫ μ
            := by simp only [id_tensorHom, tensorHom_id, Category.assoc]
        rw[this, this', big_this]
        have : lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (μ ⊗ₘ μ) ≫ μ
            = (lift (f.hom ⊗ₘ f.hom) (g.hom ⊗ₘ g.hom) ≫ (μ ⊗ₘ μ)) ≫ μ := by
          simp only [lift_map_assoc, lift_map]
        rw[this, ← this₀]
    }
  }


set_option linter.unusedSectionVars false
lemma add_def_hom_of_Mon_Hom (f g : (Hom G H)) : (f + g).hom = (lift f.hom g.hom) ≫ μ
    := rfl
