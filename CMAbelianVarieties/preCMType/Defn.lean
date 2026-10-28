/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.Algebra.CMField

/-!
# CM Types

In this section we define pre CM types

A pre CM type of a CM field `F` is a set `Φ ⊆ (F →+* ℂ)` such that `Φ` and
`conj(Φ)` are complementary to each other.

-/

@[expose] public section

open ComplexConjugate NumberField

variable {F : Type*} [Field F] [NumberField F] [IsCMField F]

variable (F) in
structure preCMType where
  /-- The subset of inclusions `F →+* ℂ` -/
  partition : Set (F →+* ℂ)
  /-- The set `partition` is in fact a partition. That is, `partition ⊔ conj (partition) = ⊤` and
  `partition ⊥ conj (partition) = ⊥`. -/
  partition_condition : IsCompl partition ((conj).comp '' partition)

-- partly solved and cleaned up by claude
def preCMType.ofInclusions (Φ : Set (F →+* ℂ)) (h : ∀ i : F →+* ℂ, (i ∈ Φ ↔
    (conj).comp i ∈ Φᶜ)) : preCMType F where
  partition := Φ
  partition_condition := by
    constructor <;> intro S hS hSconj τ hτ
    · obtain ⟨x, hx, rfl⟩ := hSconj hτ
      exact (h _).1 (hS hτ) (by simpa [← RingHom.comp_assoc] using hx)
    · by_cases hτΦ : τ ∈ Φ
      · exact hS hτΦ
      · exact hSconj ⟨(conj).comp τ, Set.notMem_compl_iff.1 (mt (h τ).2 hτΦ), star_star τ⟩

-- partly solved and cleaned up by claude.
def preCMType.ofInfinitePlaces (Φ : Set (F →+* ℂ)) (h : ∀ w : InfinitePlace F, (w.embedding ∈ Φ ↔
    (conj).comp w.embedding ∈ Φᶜ)) : preCMType F :=
  preCMType.ofInclusions Φ fun τ ↦ by
    obtain ⟨w, rfl | rfl⟩ : ∃ w : InfinitePlace F, w.embedding = τ ∨ (conj).comp w.embedding = τ :=
      ⟨InfinitePlace.mk τ,
        (InfinitePlace.embedding_mk_eq τ).imp_right fun hτ ↦ by rw [hτ]; exact star_star τ⟩
    · exact h w
    · rw [show (conj).comp ((conj).comp w.embedding) = w.embedding from star_star _]
      exact iff_not_comm.1 (h w)

-- cleaned up by claude
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
  let Φ := s₁ ∪ s₂
  have : ∀ w : InfinitePlace F, (w.embedding ∈ Φ ↔ (conj).comp w.embedding ∈ Φᶜ) := by
    have hI : Complex.I ≠ -Complex.I := fun h ↦ Complex.I_ne_zero (self_eq_neg.mp h)
    intro w
    constructor <;> intro h
    · have hw : φ w j = Complex.I := by
        rcases h with ⟨w', hw', hw'w⟩ | h
        · rwa [← InfinitePlace.embedding_inj.mp hw'w]
        · exact hs₂' w h
      exact fun h' ↦ hI (hw.symm.trans (h'.elim (hs₁' w) (hs₂ w)))
    · have hw : φ w j = Complex.I ∨ φ w j = -Complex.I :=
        mul_self_eq_mul_self_iff.mp (by rw [← map_mul, hj, map_neg, map_one, Complex.I_mul_I])
      exact Or.inl ⟨w, hw.resolve_right fun hw ↦ h (Or.inr ⟨w, hw, rfl⟩), rfl⟩
  exact preCMType.ofInfinitePlaces Φ this
