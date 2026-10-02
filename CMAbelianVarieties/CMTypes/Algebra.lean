module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.RingTheory.SimpleRing.Principal -- probably not needed!
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
    [Algebra K R] [IsCentral K R] : IsCentral F
    (F ⊗[K] R) := by
  classical
  have : ∀ x ∈  Subalgebra.center F (F ⊗[K] R), x ∈ (algebraMap F (F ⊗[K] R)).range := by
    intro x hx
    let I := Basis.ofVectorSpaceIndex K F
    let e := Basis.ofVectorSpace K F
    -- the `obtain` below was an `rcases`. Claude helped change that.
    obtain ⟨b, hb⟩ : ∃ b : I →₀ R, ∑ i ∈ b.support, e i ⊗ₜ[K] b i = x :=
      TensorProduct.eq_repr_basis_left e x
    have h1 (a : R) : ∑ i ∈ b.support, e i ⊗ₜ[K] (a * b i)
        = ∑ i ∈ b.support, e i ⊗ₜ[K] (b i * a) := by
      have hl (a : R) : (1 ⊗ₜ[K] a * ∑ i ∈ b.support, e i ⊗ₜ[K] b i)
          = ∑ i ∈ b.support, e i ⊗ₜ[K] (a * b i) := by
        simp [Finset.mul_sum]
      simp_rw [← hl a, hb, Subalgebra.mem_center_iff.mp hx (1 ⊗ₜ a), ← hb,
        Finset.sum_mul, TensorProduct.tmul_mul_tmul, mul_one]
    -- got Claude to do the `calc` below
    have h2 (a : R) : ∑ i ∈ b.support, e i ⊗ₜ[K] (a * b i - b i * a) = 0 := by
      calc ∑ i ∈ b.support, e i ⊗ₜ[K] (a * b i - b i * a)
          _ = ∑ i ∈ b.support, e i ⊗ₜ[K] (a * b i) - ∑ i ∈ b.support, e i ⊗ₜ[K] (b i * a) := by
            simp [TensorProduct.tmul_sub, Finset.sum_sub_distrib]
          _ = 0 := by rw [h1 a, sub_self]
    have (a : R) (i : I) : i ∈ b.support → a * b i = b i * a := by
      intro hi
      specialize h2 a
      let b' : I →₀ R := {
        support := by
          have : Finite {i : I | (a * b i - b i * a) ≠ 0 } := by
            have : {i : I | (a * b i - b i * a) ≠ 0 }.Finite := by
              apply @Set.Finite.subset I b.support _ {i : I | (a * b i - b i * a) ≠ 0 }
              · intro i hi
                by_cases hb : b i ≠ 0
                · simp [hb]
                · simp at hi
                  push Not at hb
                  simp [hb] at hi
              · simp
            exact Set.Finite.to_subtype this
          have := Fintype.ofFinite {i : I | (a * b i - b i * a) ≠ 0 }
          exact @Set.toFinset _ {i : I | (a * b i - b i * a) ≠ 0 } _
        toFun i := (a * b i - b i * a)
        mem_support_toFun := by
          intro i
          constructor <;> intro hi
          · simp only [ne_eq, Set.mem_toFinset, Set.mem_ofPred_eq] at hi
            push Not at hi
            assumption
          · simpa }
      have h₁ (i : I) : b' i = b'.toFun i := rfl
      have h₂ (i : I) : b'.toFun = fun i => a * b i - b i * a := rfl
      have rewrite : ∑ i ∈ b'.support, e i ⊗ₜ[K] (a * b i - b i * a) = ∑ i ∈ b.support, e i ⊗ₜ[K]
          (a * b i - b i * a) := by
        have sub : b'.support ⊆ b.support := by
          intro i hi
          simp only [Finsupp.mem_support_iff, ne_eq, Subtype.forall] at *
          contrapose hi
          simp [h₁, h₂ i, hi]
        apply Finset.sum_subset sub
        intro i hi hi'
        simp [h₁, h₂ i] at hi'
        simp [hi']
      rw [← rewrite] at h2
      have : b' = 0 → (a * b i = b i * a) := by
        intro h
        by_cases hb : i ∈ b'.support
        · simp [h] at hb
        · simp only [Finsupp.mem_support_iff, ne_eq, not_not, h₁] at hb
          exact eq_of_sub_eq_zero hb
      apply this
      exact (TensorProduct.sum_tmul_basis_left_eq_zero e b' h2)
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
    simp only [← hb, RingHom.mem_range, TensorProduct.algebraMap_apply, algebraMap_self,
      RingHom.id_apply]
    let x (i : I) : K := if hi : i ∈ b.support then (this i hi).choose else 0
    have (i : I) : e i ⊗ₜ[K] b i = (x i • e i) ⊗ₜ[K] 1 := by
      rw [TensorProduct.smul_tmul]
      by_cases hb : i ∈ b.support
      · have h : x i = (this i hb).choose := by
          simp only [x, hb, dite_true]
        simp only [h, smul_def' (Exists.choose (this i hb)) (1 : R), (this i hb).choose_spec,
          mul_one]
      · have h : x i = 0 := by
          simp only [Finsupp.mem_support_iff, ne_eq, dite_eq_right_iff, x]
          intro h
          simp [h] at hb
        have : b i = 0 := by
          contrapose hb
          simp only [b.mem_support_toFun i, ne_eq]
          exact hb
        simp [h, this]
    use (∑ i ∈ b.support, (x i • e i))
    simp [this, TensorProduct.sum_tmul]
  exact {
    out := fun x hx => Algebra.mem_bot.mpr (this x hx)
  }

lemma IsSimpleRing_basechange (F K R : Type*) [Field K] [Field F] [Algebra K F] [Ring R]
    [Algebra K R] [IsSimpleRing R] [IsCentral K R] : IsSimpleRing (F ⊗[K] R) := by
  have eq_bot_or_eq_top : ∀ (J : TwoSidedIdeal (F ⊗[K] R)), J = ⊥ ∨ J = ⊤ := by
    intro J
    by_cases hJ : J = ⊥
    · left; assumption
    · right
      apply TwoSidedIdeal.eq_top
      obtain ⟨x, hxJ, hx⟩ : ∃ x ∈ J, x ≠ 0 := by
        contrapose hJ
        push Not at hJ
        ext x
        constructor <;> intro h <;> simp only [TwoSidedIdeal.mem_bot] at *
        · exact hJ x h
        · simp [h]

      sorry
  exact {
    simple := {
      exists_pair_ne := by
        use ⊥, ⊤
        simp
      eq_bot_or_eq_top := eq_bot_or_eq_top
    }
  }

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
