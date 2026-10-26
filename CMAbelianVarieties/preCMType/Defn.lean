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
  partition_condition : ∀ w : InfinitePlace F, (w.embedding ∈ partition ↔
    (conj).comp w.embedding ∈ partitionᶜ)

open TensorProduct in
noncomputable def preCMType.ofComplexStructure {j : ℝ ⊗[ℚ] F} (hj : j * j = -1) : preCMType F := by
  let φ (w : InfinitePlace F) := (Pi.evalAlgHom ℝ (fun _ ↦ ℂ) w).comp
    (real_tensor_CMField F).toAlgHom
  let s₁ := InfinitePlace.embedding '' {w | φ w j = Complex.I}
  let s₂ := (fun w ↦ (conj).comp w.embedding) '' {w | φ w j = -Complex.I}
  have hs₁' (w : InfinitePlace F) : (conj).comp w.embedding ∈ s₁ → φ w j = -Complex.I := by
    rintro ⟨w', -, hw'w⟩
    exfalso
    have hw : w' = w := by
      rw [← InfinitePlace.mk_embedding w', hw'w]
      exact (InfinitePlace.mk_conjugate_eq w.embedding).trans w.mk_embedding
    subst hw
    exact InfinitePlace.isComplex_iff.mp (IsTotallyComplex.isComplex w') hw'w.symm
  have hs₂ (w : InfinitePlace F) : (conj).comp w.embedding ∈ s₂ → φ w j = -Complex.I := by
    rintro ⟨w', hw', hw'w : ComplexEmbedding.conjugate w'.embedding = _⟩
    have hw : w' = w := by
      rw [← InfinitePlace.mk_embedding w', ← InfinitePlace.mk_conjugate_eq, hw'w]
      exact (InfinitePlace.mk_conjugate_eq w.embedding).trans w.mk_embedding
    rwa [← hw]
  have hs₂' (w : InfinitePlace F) : w.embedding ∈ s₂ → φ w j = Complex.I := by
    rintro ⟨w', -, hw'w : ComplexEmbedding.conjugate w'.embedding = _⟩
    exfalso
    have hw : w' = w := by
      rw [← w.mk_embedding, ← hw'w]
      exact ((InfinitePlace.mk_conjugate_eq w'.embedding).trans w'.mk_embedding).symm
    subst hw
    exact InfinitePlace.isComplex_iff.mp (IsTotallyComplex.isComplex w') hw'w
  exact {
    partition := s₁ ∪ s₂
    partition_condition w := by
      have hI : Complex.I ≠ -Complex.I := fun h ↦ Complex.I_ne_zero (self_eq_neg.mp h)
      constructor <;> intro h
      · have hw : φ w j = Complex.I := by
          rcases h with ⟨w', hw', hw'w⟩ | h
          · rwa [← InfinitePlace.embedding_inj.mp hw'w]
          · exact hs₂' w h
        exact fun h' ↦ hI (hw.symm.trans (h'.elim (hs₁' w) (hs₂ w)))
      · have hw : φ w j = Complex.I ∨ φ w j = -Complex.I :=
          mul_self_eq_mul_self_iff.mp (by rw [← map_mul, hj, map_neg, map_one, Complex.I_mul_I])
        exact Or.inl ⟨w, hw.resolve_right fun hw ↦ h (Or.inr ⟨w, hw, rfl⟩), rfl⟩
  }
