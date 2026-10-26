/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

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
  /-- The subset of inclusions `F →+* ℂ` -/
  partition : Set (F →+* ℂ)
  /-- The `partition` is infact a partition. The condition basically says that an infinite
  place, and its conjugate can not be in the same set within the partition
  `partition ⊔ partitionᶜ` -/
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

/-
Suggested by Claude: add a lemma recovering the condition for all complex embeddings, not just
the chosen embeddings `w.embedding` of the infinite places:
  `∀ σ : F →+* ℂ, σ ∈ Φ.partition ↔ (conj).comp σ ∈ Φ.partitionᶜ`.
Proof idea: every `σ` is `w.embedding` or `conj ∘ w.embedding` for `w = InfinitePlace.mk σ`
(`InfinitePlace.mk_eq_iff`); in the second case use the contrapositive of `partition_condition w`.
-/

/-
Suggested by Claude: partitions in Mathlib.
- `IsCompl` (`Mathlib/Order/Disjoint.lean`): `IsCompl x y` means `Disjoint x y` and
  `Codisjoint x y` (i.e. `x ⊓ y = ⊥` and `x ⊔ y = ⊤`); for sets, `x ∩ y = ∅` and
  `x ∪ y = univ`. The CM type condition could be stated as
    `IsCompl partition ((conj).comp '' partition)`,
  i.e. `Hom(F, ℂ) = Φ ⊔ conj ∘ Φ`, which is the textbook statement. `IsCompl.compl_eq` turns it
  into `(conj).comp '' Φ = Φᶜ`, and the "for every `σ`" version follows quickly.
More general notions (for more than two pieces):
- `Setoid.IsPartition (c : Set (Set α))` (`Mathlib/Order/Setoid/Partition.lean`):
  `∅ ∉ c ∧ ∀ a, ∃! b ∈ c, a ∈ b`; unindexed, nonempty pieces; linked to equivalence relations.
- `IndexedPartition (s : ι → Set α)` (same file): indexed family, each point in exactly one
  `s i`, with `index : α → ι` and a chosen point `some i ∈ s i` (so no piece is empty).
- `Partition (s : α)` (`Mathlib/Order/Partition/Basic.lean`): partition of an element of a
  complete lattice: `sSupIndep` parts, `⊥` not a part, supremum `s`.
- `Finpartition (a : α)` (`Mathlib/Order/Partition/Finpartition.lean`): finite version, with
  parts a `Finset`.
-/
