module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

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
open Module Algebra Subring

#check IsCentral
#check center

/- the center of a simple ring is a field -/
#check IsSimpleRing.isField_center
#check Decidable.or_not_self
#check Classical.dec

lemma IsCentral_basechange (F K R : Type*) [Field K] [Field F] [Algebra K F] [Ring R]
    [Algebra K R] [DecidableEq (Basis.ofVectorSpaceIndex K F)] [IsCentral K R] : IsCentral F
    (F ⊗[K] R) := by
  have : ∀ (x : F ⊗[K] R), x ∈  Subalgebra.center F (F ⊗[K] R) →
      (x : F ⊗[K] R) ∈ (algebraMap F (F ⊗[K] R)).range := by
    intro x hx
    let I := Basis.ofVectorSpaceIndex K F
    let e := Basis.ofVectorSpace K F
    -- the `obtain` below was an `rcases`. Claude helped change that.
    obtain ⟨b, hb⟩ : ∃ b : I →₀ R, ∑ i ∈ b.support, e i ⊗ₜ[K] b i = x :=
      TensorProduct.eq_repr_basis_left e x
    have : ∀ a : R, (1 ⊗ₜ a) * x = x * (1 ⊗ₜ a) := by
      intro a
      exact Subalgebra.mem_center_iff.mp hx (1 ⊗ₜ a)
    have h (a : R) : ∑ i ∈ b.support, e i ⊗ₜ[K] (a * b i)
        = ∑ i ∈ b.support, e i ⊗ₜ[K] (b i * a) := by
      -- credit to Claude for this `have`
      have hl (a : R) : (1 ⊗ₜ[K] a * ∑ i ∈ b.support, e i ⊗ₜ[K] b i)
          = ∑ i ∈ b.support, e i ⊗ₜ[K] (a * b i) := by
        simp [Finset.mul_sum]
      rw [← hl a, hb, this, ← hb]
      simp [Finset.sum_mul]
    -- got Claude to do the `calc` below
    have (a : R) : ∑ i ∈ b.support, e i ⊗ₜ[K] (a * b i - b i * a) = 0 := by
      calc ∑ i ∈ b.support, e i ⊗ₜ[K] (a * b i - b i * a)
          _ = ∑ i ∈ b.support, e i ⊗ₜ[K] (a * b i) - ∑ i ∈ b.support, e i ⊗ₜ[K] (b i * a) := by
            simp [TensorProduct.tmul_sub, Finset.sum_sub_distrib]
          _ = 0 := by rw [h a, sub_self]
    have (a : R) (i : I) : i ∈ b.support → a * b i = b i * a := by
      intro hi
      specialize this a
      let b' : I →₀ R := {
        support := by sorry
        toFun i := (a * b i - b i * a)
        mem_support_toFun := by
          intro i
          constructor <;> intro hi
          · #check Finsupp.mem_support_toFun b i
            sorry
          · sorry
      }
      have hypo : ∑ i ∈ b.support, e i ⊗ₜ[K] (a * b i - b i * a)
          = (b.sum fun i n ↦ e i ⊗ₜ[K] (a * n - n * a)) := by
        rfl
      rw [hypo] at this
      #check TensorProduct.sum_tmul_basis_left_eq_zero e b
      sorry
    -- simp will get it to the final needed form
    have (i : I) (hi : i ∈ b.support ): b i ∈ (algebraMap K R).range := by
      have : b i ∈ center R := by
        rw [Subring.mem_center_iff]
        exact fun r => this r i hi
      have : (algebraMap K R).range = (Subalgebra.center K R).toSubring := by
        ext r
        have : (algebraMap K R).range = (⊥ : Subalgebra K R).toSubring := by rfl
        constructor <;> intro h
        · rcases h with ⟨x, rfl⟩
          simp only [Subalgebra.center_toSubring]
          rw [mem_center_iff]
          exact fun g ↦ Eq.symm (commutes' x g)
        · apply (IsCentral.out : Subalgebra.center K R ≤ (⊥ : Subalgebra K R)) h
      simpa [this]
    simp [← hb]
    sorry
  exact {
    out := by
      intro x hx
      specialize this x hx
      exact Algebra.mem_bot.mpr this
  }

lemma IsSimpleRing_basechange (F K R : Type*) [Field K] [Field F] [Algebra K F] [Ring R]
    [Algebra K R] [IsSimpleRing R] [IsCentral K R] : IsSimpleRing (F ⊗[K] R) := sorry

lemma fact₁ (K R : Type*) [Ring R] [Field K] [Algebra K R] [IsSimpleRing R] [IsCentral K R]
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

lemma dimension_IsSimple_algebra (K R : Type*) [Ring R] [Field K] [Algebra K R] [IsSimpleRing R]
    [IsCentral K R] [FiniteDimensional K R] : ∃ n : ℕ, finrank (AlgebraicClosure K)
    ((AlgebraicClosure K) ⊗[K] R) = (n * n : ℕ) := by
  use (fact₁ K R).choose
  rw [LinearEquiv.finrank_eq (Classical.choice ((fact₁ K R).choose_spec).choose_spec).toLinearEquiv]
  exact fact₂ (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] R) (fact₁ K R).choose

#min_imports
