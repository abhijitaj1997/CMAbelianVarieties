/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Extension.Presentation.Core

/-!
## Algebra for algebraic geometry

Algebraic results used in `AlgebraicGeometry/`.

-/

@[expose] public section

universe u

variable {K : Type u} [Field K]

-- written by Claude
open TensorProduct in
/-- A finite type algebra `A` over an algebraic extension `L/K` has a model `A₀` over a
finite extension `E/K` inside `L`, i.e. `L ⊗[E] A₀ ≃ₐ[L] A`. We take `E` to be generated over `K`
by the coefficients of the relations of a finite presentation of `A`. -/
lemma exists_model_of_finiteType {L A : Type u} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [CommRing A] [Algebra L A] [Algebra.FiniteType L A] :
    ∃ (E : IntermediateField K L) (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra E A₀),
      FiniteDimensional K E ∧ Algebra.FiniteType E A₀ ∧ Nonempty (L ⊗[E] A₀ ≃ₐ[L] A) := by
  have : Algebra.FinitePresentation L A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let P := Algebra.Presentation.ofFinitePresentation L A
  let E := IntermediateField.adjoin K P.coeffs
  have : Finite P.coeffs := P.finite_coeffs
  have : P.HasCoeffs E := ⟨fun x hx ↦ ⟨⟨x, IntermediateField.subset_adjoin K _ hx⟩, rfl⟩⟩
  exact ⟨E, P.ModelOfHasCoeffs E, inferInstance, inferInstance,
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x,
    inferInstance, ⟨P.tensorModelOfHasCoeffsEquiv E⟩⟩

-- pick up from here : This is where I need to start. The next goal has to be the creation of the rational model.
open TensorProduct in
lemma nameless {L A : Type u} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] (I : L ⊗[K] A) :
    ∃ (L₁ : IntermediateField K L) (I₁ : Ideal (L₁ ⊗[K] A)), 1 = 1 := by
  #check L ⊗[K] A
  sorry
