module

public import Mathlib
--public import CMAbelianVarieties.AbstractNonsense.Kernels

open CategoryTheory Limits

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
variable [hC : HasPullbacks C] {X : C}
variable {α β τ : Over X} {φ : α ⟶ τ} {ψ : β ⟶ τ}

example : (pullback φ ψ).left ≅ pullback φ.left ψ.left := by
  sorry
