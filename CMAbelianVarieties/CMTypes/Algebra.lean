module

public import Mathlib

/-!
## Goal

The goal of this document go through all the algebraic background required
to define CM Types

-/

@[expose] public noncomputable section

open Subring

instance {R : Type*} [Ring R] [Algebra ℚ R] : SMul ℚ (center R) where
  smul x r := {
    val := x • r
    property := by
      rw [mem_center_iff]
      intro s
      simp [Subring.mem_center_iff.1 r.property s]
  }

lemma center_smul_def {R : Type*} [Ring R] [Algebra ℚ R] {x : ℚ} {r : center R} :
    ↑(x • r) = x • (r : R) := by rfl

def center_algebra_map (R : Type*) [Ring R] [Algebra ℚ R] : ℚ →+* (center R) where
  toFun x := x • 1
  map_one' := by
    ext; simp [center_smul_def]
  map_mul' x y := by
    ext; simp [center_smul_def, ← mul_smul y x (1 : R), mul_comm]
  map_zero' := by
    ext; simp [center_smul_def]
  map_add' x y := by
    ext; simp [center_smul_def, add_smul]

instance {R : Type*} [Ring R] [Algebra ℚ R] : Algebra ℚ (center R) where
  smul x r := x • r
  algebraMap := center_algebra_map R
  commutes' x r := by
    ext; simp [center_algebra_map, center_smul_def]
  smul_def' x r := by
    ext; simp [center_algebra_map, center_smul_def]

open scoped TensorProduct
open Module

#check Algebra.IsCentral
#check Subsemiring.center

/- the center of a simple ring is a field -/
#check IsSimpleRing.isField_center


lemma IsSimpleRing_basechange (F K R : Type*) [Field K] [Field F] [Algebra K F] [Ring R]
    [Algebra K R] [IsSimpleRing R] : IsSimpleRing (F ⊗[K] R) := sorry

-- Does not look like it's needed
lemma IsCentral_basechange (F K R : Type*) [Field K] [Field F] [Algebra K F] [Ring R]
    [Algebra K R] [Algebra.IsCentral K R] : Algebra.IsCentral F (F ⊗[K] R) := sorry

lemma fact₁ (K R : Type*) [Ring R] [Field K] [Algebra K R] [IsSimpleRing R]
    [FiniteDimensional K R] : ∃ n : ℕ, ∃ _ : NeZero n, Nonempty (AlgebraicClosure K ⊗[K] R
    ≃ₐ[AlgebraicClosure K] Matrix (Fin n) (Fin n) (AlgebraicClosure K)) :=
  (@IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed (AlgebraicClosure K)
    ((AlgebraicClosure K) ⊗[K] R) _ _ _ _
    (IsSimpleRing_basechange (AlgebraicClosure K) K R) _)

lemma fact₂ (K R : Type*) [Ring R] [Field K] [Algebra K R] [FiniteDimensional K R] (n : ℕ) :
    finrank K (Matrix (Fin n) (Fin n) K) = (n * n : ℕ) := by
  have : n * n = Fintype.card (Fin n) * Fintype.card (Fin n) * finrank K K
      := by simp only [Fintype.card_fin, finrank_self, mul_one]
  rw [this, ←  Module.finrank_matrix K K (Fin n) (Fin n)]

variable (K R : Type*) [Ring R] [Field K] [Algebra K R] [IsSimpleRing R]
    [FiniteDimensional K R]

lemma dimension_IsSimple_algebra (K R : Type*) [Ring R] [Field K] [Algebra K R] [IsSimpleRing R]
    [FiniteDimensional K R] : ∃ n : ℕ, finrank (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] R)
    = (n * n : ℕ) := by
  use (fact₁ K R).choose
  rw [LinearEquiv.finrank_eq (Classical.choice ((fact₁ K R).choose_spec).choose_spec).toLinearEquiv]
  exact fact₂ (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] R) (fact₁ K R).choose
