module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon

@[expose] public section

section RingStructure


open CategoryTheory MonoidalCategory AddMon AddMonObj CartesianMonoidalCategory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
variable {G G₁ H : C} [AddMonObj G] [AddMonObj H]

namespace IsAddMonHom

-- `σ[G]` the sum map (was `μ[G]`)
-- `ζ[G]` the unit map (was `η[G]`)


/-- Given two morphisms `f g : X ⟶ G`, for a monoid object `G`, `add f g` defines the
sum of these two -/
abbrev add {X : C} (f g : X ⟶ G) : X ⟶ G := (lift f g) ≫ σ[G]

-- I am not sure what is the right name for this
lemma zero_comp_lift (f g : G ⟶ H) [IsAddMonHom f] [IsAddMonHom g]
    : (ζ[G] ≫ (lift f g)) = (lift ζ[H] ζ[H]) := by
  ext
  · simp [IsAddMonHom.zero_hom f]
  · simp [IsAddMonHom.zero_hom g]

lemma leftUnitor_neg_comp_zero : (λ_ (𝟙_ C)).inv ≫ (ζ[H] ⊗ₘ ζ[H]) = lift ζ[H] ζ[H]
    := by
  ext <;> simp only [mon_tauto] <;> simp

instance add_IsMonHom [BraidedCategory C] [IsCommAddMonObj H] {f g : G ⟶ H}
    [IsAddMonHom f] [IsAddMonHom g] : IsAddMonHom (IsAddMonHom.add f g) where
  zero_hom := by
    rw [reassoc_of% zero_comp_lift f g]
    simp_rw [← reassoc_of% leftUnitor_neg_comp_zero, mon_tauto]
  add_hom := by
    have : σ[G] ≫ lift f g = lift (σ[G] ≫ f) (σ[G] ≫ g) := by
      ext <;> simp
    rw [← Category.assoc, this, IsAddMonHom.add_hom]
    have this₀ : lift ((f ⊗ₘ f) ≫ σ) ((g ⊗ₘ g) ≫ σ)
        = lift (f ⊗ₘ f) (g ⊗ₘ g) ≫ (σ ⊗ₘ σ) := by
      ext <;> simp
    have this₀₀ : ((lift f g) ⊗ₘ (lift f g)) ≫ (σ ⊗ₘ σ)
        = (lift f g ≫ σ ⊗ₘ lift f g ≫ σ) := by
      ext <;> simp
    have big_this : (α_ H H (H ⊗ H)).hom ≫ (H ◁ (α_ H H H).inv) ≫
        (H ◁ σ ▷ H) ≫ (H ◁ σ) ≫ σ = (σ ⊗ₘ σ) ≫ σ := by
      simp only [mon_tauto]
    have this₁ : (H ◁ ((β_ H H).hom ≫ σ) ▷ H) = (H ◁ σ[H] ▷ H) := by
      rw [IsCommAddMonObj.add_comm]
    have THIS : lift (f ⊗ₘ f) (g ⊗ₘ g) ≫
        ((α_ H H (H ⊗ H)).hom ≫ (H ◁ (α_ H H H).inv) ≫
        ((H ◁ σ[H] ▷ H)))
        = ((lift f g) ⊗ₘ (lift f g)) ≫
        (α_ H H (H ⊗ H)).hom ≫ (H ◁ (α_ H H H).inv) ≫
        (H ◁ ((β_ H H).hom ≫ σ) ▷ H) := by
      ext
      · simp only [Category.assoc, whiskerLeft_fst, associator_hom_fst,
        lift_fst_assoc, tensorHom_fst, IsCommAddMonObj.add_comm, tensorHom_fst_assoc, lift_fst]
      · simp only [Category.assoc, whiskerLeft_snd, whiskerLeft_snd_assoc, whiskerRight_fst,
        comp_whiskerRight, whiskerLeft_comp, whiskerRight_fst_assoc]
        have : lift (f ⊗ₘ f) (g ⊗ₘ g) ≫ (α_ H H (H ⊗ H)).hom ≫
            snd H (H ⊗ H ⊗ H) ≫ (α_ H H H).inv ≫ fst (H ⊗ H) H ≫ σ
            = (lift (f ⊗ₘ f) (g ⊗ₘ g) ≫ (α_ H H (H ⊗ H)).hom ≫
            snd H (H ⊗ H ⊗ H) ≫ (α_ H H H).inv ≫ fst (H ⊗ H) H) ≫ σ
            := by simp
        rw [this]
        have : lift (f ⊗ₘ f) (g ⊗ₘ g) ≫
            (α_ H H (H ⊗ H)).hom ≫ snd H (H ⊗ H ⊗ H) ≫ (α_ H H H).inv ≫ fst (H ⊗ H) H
            = (lift f g ⊗ₘ lift f g) ≫ (α_ H H (H ⊗ H)).hom ≫
            snd H (H ⊗ H ⊗ H) ≫ (α_ H H H).inv ≫ fst (H ⊗ H) H ≫ (β_ H H).hom := by
          ext <;> simp
        simp [this]
      · simp
    rw [← this₀₀]
    have : ((lift f g ⊗ₘ lift f g) ≫ (σ ⊗ₘ σ)) ≫ σ
        = ((lift f g ⊗ₘ lift f g) ≫ ((σ ⊗ₘ σ)) ≫ σ) := by simp
    simp_rw [this, ← big_this, ← this₁, ← reassoc_of% THIS, mon_tauto,
    IsAddMonHom.add_hom, ← reassoc_of% this₀]

end IsAddMonHom

/-
If `G` and `H` are monoidal object in a Cartesian Monoidal Category, where `H` has a
commutative monoidal structure, the monoidal homomorphisms between them have a natural
addition.

We use the additive notation here for two reasons:
1. Multiplication of functions usually means compositon
2. The additive structure will later be part of a ring strucutre.

I will submit the rest of the ring structure separately.
-/
instance [BraidedCategory C] {G₀ H₀ : AddMon C} [IsCommAddMonObj H₀.X] : Add (Hom G₀ H₀) where
  add f g := {
    hom := IsAddMonHom.add f.hom g.hom
    isAddMonHom_hom := inferInstance
  }

lemma AddMonHom.add_hom [BraidedCategory C] {G₀ H₀ : AddMon C} [IsCommAddMonObj H₀.X]
    (f g : (Hom G₀ H₀)) : (f + g).hom = (lift f.hom g.hom) ≫ σ[H₀.X] := rfl

end RingStructure

#min_imports
