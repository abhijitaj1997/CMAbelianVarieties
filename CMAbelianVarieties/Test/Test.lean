module

public import Mathlib

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [HasPullbacks C]

variable {A B T : C} {f : A ⟶ T} {g : B ⟶ T}

#check pullback f g

noncomputable example {X : C} {φ : X ⟶ A} {ψ : X ⟶ B} (h : φ ≫ f = ψ ≫ g) : X ⟶ pullback f g
    := by
  exact pullback.lift φ ψ h
