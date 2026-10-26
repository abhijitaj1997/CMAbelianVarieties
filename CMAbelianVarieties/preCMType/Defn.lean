/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import CMAbelianVarieties.Algebra.CMField

/-!
# CM Types

In this section we define CM types

-/

@[expose] public section

open ComplexConjugate NumberField

variable {F : Type*} [Field F] [NumberField F] [IsCMField F]

variable (F) in
structure preCMType where
  partition : Set (F →+* ℂ)
  partition_condition : ∀ φ : (F →+* ℂ), φ ∈ partition ↔
    (conj : ℂ →+* ℂ).comp φ ∈ partitionᶜ

/-
Maybe a lemma should be created which says that given a `preCMType`, we
have a natural map from to the set of places of `K`
-/

section

variable (F : Type*) [Field F] [NumberField F] [IsCMField F]

#check (Module.finrank ℚ F)

#synth Finite (F →+* ℂ)

/- The number of complex embeddings equals the degree `[F : ℚ]`. -/
#check NumberField.Embeddings.card F ℂ

/- A totally complex field (e.g. a CM field) has even degree. -/
#check NumberField.IsTotallyComplex.finrank F

#check InfinitePlace.nrComplexPlaces



end

#check real_tensor_CMField F

/- Written by Claude: for each infinite place `w`, the composition
`ℝ ⊗[ℚ] F ≃ₐ[ℝ] (InfinitePlace F → ℂ) →ₐ[ℝ] ℂ` of `real_tensor_CMField F` with evaluation at `w`
(`Pi.evalAlgHom`, in `Mathlib/Algebra/Algebra/Pi.lean`). -/
#check fun w : InfinitePlace F ↦
  (Pi.evalAlgHom ℝ (fun _ ↦ ℂ) w).comp (real_tensor_CMField F).toAlgHom

open TensorProduct in
noncomputable def preCMType.ofComplexStructure {j : ℝ ⊗[ℚ] F} (hj : j * j = -1) : preCMType F := by
  let φ (w : InfinitePlace F) := (Pi.evalAlgHom ℝ (fun _ ↦ ℂ) w).comp
    (real_tensor_CMField F).toAlgHom
  let s₁ := InfinitePlace.embedding '' {w | φ w j = Complex.I}
  let s₂ := (fun w ↦ ComplexEmbedding.conjugate w.embedding) '' {w | φ w j = -Complex.I}
  exact {
    partition := s₁ ⊔ s₂
    partition_condition ψ := by
      constructor
      · rintro (h₁ | h₂)
        · -- Claude: membership in an image `f '' s` (`Mathlib/Data/Set/Operations.lean`).
          rw [Set.mem_image InfinitePlace.embedding ({w | φ w j = Complex.I}) ψ] at h₁
          rcases h₁ with ⟨w, hw, hwψ⟩
          simp at hw
          sorry
        · sorry
      · sorry
  }
