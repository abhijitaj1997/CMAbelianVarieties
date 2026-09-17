
module

public import Mathlib.CategoryTheory.Monoidal.Grp

/-!

The goal of this file is to file is to catalogue the group structure of the pullback
and the fact the some of the maps are group homomorphisms

_Incomplete tasks_
•A bunch of instances

-/

@[expose] public noncomputable section

open CategoryTheory Limits AddMonObj MonoidalCategory

variable {C : Type*} [Category* C] [HasPullbacks C] [CartesianMonoidalCategory C]
variable {G H T : C} {f : G ⟶ T} {g : H ⟶ T}
variable [AddGrpObj G] [AddGrpObj T] [AddGrpObj H] [IsAddMonHom f] [IsAddMonHom g]

--instance : HasPullbacks (AddGrp C) := sorry

def φ₁ (f : G ⟶ T) (g : H ⟶ T) := pullback.fst f g
def φ₂ (f : G ⟶ T) (g : H ⟶ T) := pullback.snd f g

lemma zero_lift_condition {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    {G H T : C} (f : G ⟶ T) (g : H ⟶ T) [AddGrpObj G] [AddGrpObj T] [AddGrpObj H] [IsAddMonHom f]
    [IsAddMonHom g] : ζ ≫ f = ζ ≫ g := by simp

lemma add_lift_condition {C : Type*} [Category* C] [HasPullbacks C] [CartesianMonoidalCategory C]
    {G H T : C} (f : G ⟶ T) (g : H ⟶ T) [AddGrpObj G] [AddGrpObj T] [AddGrpObj H] [IsAddMonHom f]
    [IsAddMonHom g] : ((φ₁ f g ⊗ₘ φ₁ f g) ≫ σ) ≫ f = ((φ₂ f g ⊗ₘ φ₂ f g) ≫ σ) ≫ g := by
  simp_rw [Category.assoc, IsAddMonHom.add_hom, Category.assoc']
  have : (φ₁ f g ⊗ₘ φ₁ f g) ≫ (f ⊗ₘ f) = (φ₂ f g ⊗ₘ φ₂ f g) ≫ (g ⊗ₘ g) := by
    have hf : (φ₁ f g ⊗ₘ φ₁ f g) ≫ (f ⊗ₘ f) = ((φ₁ f g ≫ f) ⊗ₘ (φ₁ f g ≫ f)) := by ext <;> simp
    have hg : (φ₂ f g ⊗ₘ φ₂ f g) ≫ (g ⊗ₘ g) = ((φ₂ f g ≫ g) ⊗ₘ (φ₂ f g ≫ g)) := by ext <;> simp
    rw [hf, hg, φ₁, φ₂, pullback.condition]
  rw [this]

instance : AddGrpObj (pullback f g) := by
  exact {
    zero := by
      have : ζ ≫ f = ζ ≫ g := by simp
      exact pullback.lift ζ ζ (zero_lift_condition f g)
    add := by
      exact pullback.lift ((φ₁ f g ⊗ₘ φ₁ f g) ≫ σ) ((φ₂ f g ⊗ₘ φ₂ f g) ≫ σ) (add_lift_condition f g)
    zero_add := by
      simp
      set z := pullback.lift ζ ζ (zero_lift_condition f g) with hz
      set mul := pullback.lift ((φ₁ f g ⊗ₘ φ₁ f g) ≫ σ) ((φ₂ f g ⊗ₘ φ₂ f g) ≫ σ) (add_lift_condition f g) with hmul
      have : (z ▷ (pullback f g)) ≫ mul ≫ φ₁ f g = ((𝟙_ C) ◁ φ₁ f g) ≫ (λ_ G).hom := sorry
      have : (z ▷ (pullback f g)) ≫ mul ≫ φ₂ f g = ((𝟙_ C) ◁ φ₂ f g) ≫ (λ_ H).hom := sorry

      sorry
    add_zero := sorry
    add_assoc := sorry
    neg := sorry
    left_neg := sorry
    right_neg := sorry
  }

instance [BraidedCategory C] [IsCommAddMonObj G] [IsCommAddMonObj H]
    : IsCommAddMonObj (pullback f g) := sorry

example {α : C} {F G : α ⟶ pullback f g} (h₁ : F ≫ pullback.fst f g = G ≫ pullback.fst f g)
    (h₂ : F ≫ pullback.snd f g = G ≫ pullback.snd f g) : F = G := pullback.hom_ext h₁ h₂

instance : IsAddMonHom (pullback.fst f g) := sorry

instance : IsAddMonHom (pullback.snd f g) := sorry

lemma IsAddMonHom.pullback_lift {X : C} [AddGrpObj X] {φ : X ⟶ G} {ψ : X ⟶ H} [IsAddMonHom φ]
    [IsAddMonHom ψ] (h : φ ≫ f = ψ ≫ g) : IsAddMonHom (pullback.lift φ ψ h) := by
  sorry


-- Important
example (φ : G ⟶ H) [IsAddMonHom φ] {X : C} : (X ⟶ G) →+ (X ⟶ H) := by
  exact IsAddMonHom.addMonoidHom φ X

#min_imports
