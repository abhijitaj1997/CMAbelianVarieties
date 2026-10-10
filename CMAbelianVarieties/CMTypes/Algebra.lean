module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.Algebra.Central.Basic
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
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

lemma IsCentral_basechange' (F K R : Type*) [Field K] [Field F] [Algebra K F] [Ring R]
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
      simpa only [this, Subalgebra.center_toSubring]
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

-- A really short proof given by Claude
lemma IsCentral_basechange (F K R : Type*) [Field K] [Field F] [Algebra K F] [Ring R]
    [Algebra K R] [IsCentral K R] : IsCentral F (F ⊗[K] R) where
  out x hx := by
    have hx' : x ∈ Subalgebra.centralizer K
        (Algebra.TensorProduct.includeRight : R →ₐ[K] F ⊗[K] R).range := by
      rintro _ ⟨r, rfl⟩
      exact Subalgebra.mem_center_iff.mp hx _ ▸ rfl
    rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct,
      IsCentral.center_eq_bot] at hx'
    obtain ⟨y, rfl⟩ := hx'
    clear hx
    induction y using TensorProduct.inductionOn with
    | tmul f r =>
      obtain ⟨k, hk⟩ := Algebra.mem_bot.mp r.2
      refine Algebra.mem_bot.mpr ⟨k • f, ?_⟩
      rw [Algebra.TensorProduct.algebraMap_apply, algebraMap_self, RingHom.id_apply]
      simp [← hk, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add a b ha hb => simpa using add_mem ha hb

-- mostly written by Claude
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
      classical
      -- write elements of `F ⊗[K] R` as `∑ e i ⊗ c i` for a `K`-basis `e` of `F`
      let e := Basis.ofVectorSpace K F
      let Φ := Finsupp.lsum K fun i ↦ TensorProduct.mk K F R (e i)
      have hΦ_inj : Function.Injective Φ := TensorProduct.sum_tmul_basis_left_injective e
      have hΦ_single (i) (r : R) : Φ (Finsupp.single i r) = e i ⊗ₜ r := by
        simp [Φ]
      have hL (a : R) (c) : (1 ⊗ₜ a) * Φ c = Φ (c.mapRange (a * ·) (mul_zero a)) := by
        induction c using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg =>
          rw [map_add, mul_add, hf, hg, Finsupp.mapRange_add (mul_add a), map_add]
        | single i r => simp [hΦ_single]
      have hR (b : R) (c) : Φ c * (1 ⊗ₜ b) = Φ (c.mapRange (· * b) (zero_mul b)) := by
        induction c using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg =>
          rw [map_add, add_mul, hf, hg, Finsupp.mapRange_add (fun x y ↦ add_mul x y b), map_add]
        | single i r => simp [hΦ_single]
      -- choose a nonzero element of `J` with the fewest basis terms
      have hex : ∃ n, ∃ c, Φ c ∈ J ∧ c ≠ 0 ∧ c.support.card = n := by
        obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left e x
        have hc : Φ c = x := hc
        exact ⟨_, c, hc ▸ hxJ, by rintro rfl; simp [← hc] at hx, rfl⟩
      obtain ⟨c, hcJ, hc0, hcn⟩ := Nat.find_spec hex
      have hmin : ∀ d, Φ d ∈ J → d.support.card < c.support.card → d = 0 := by
        intro d hdJ hd
        by_contra hd0
        exact Nat.find_min hex (hcn ▸ hd) ⟨d, hdJ, hd0, rfl⟩
      obtain ⟨i₀, hi₀⟩ := Finsupp.support_nonempty_iff.mpr hc0
      -- the coefficients at `i₀` of elements of `J` supported in `c.support` form an ideal
      let T : TwoSidedIdeal R := TwoSidedIdeal.mk'
        {s | ∃ d, Φ d ∈ J ∧ d.support ⊆ c.support ∧ d i₀ = s}
        ⟨0, by simp [J.zero_mem], by simp, rfl⟩
        (by
          rintro _ _ ⟨d, hdJ, hds, rfl⟩ ⟨d', hdJ', hds', rfl⟩
          refine ⟨d + d', ?_, Finsupp.support_add.trans (Finset.union_subset hds hds'), rfl⟩
          rw [map_add]
          exact J.add_mem hdJ hdJ')
        (by
          rintro _ ⟨d, hdJ, hds, rfl⟩
          refine ⟨-d, ?_, by simpa using hds, rfl⟩
          rw [map_neg]
          exact J.neg_mem hdJ)
        (by
          rintro a _ ⟨d, hdJ, hds, rfl⟩
          refine ⟨d.mapRange (a * ·) (mul_zero a), ?_, Finsupp.support_mapRange.trans hds, rfl⟩
          rw [← hL]
          exact J.mul_mem_left _ _ hdJ)
        (by
          rintro _ b ⟨d, hdJ, hds, rfl⟩
          refine ⟨d.mapRange (· * b) (zero_mul b), ?_, Finsupp.support_mapRange.trans hds, rfl⟩
          rw [← hR]
          exact J.mul_mem_right _ _ hdJ)
      -- since `R` is simple, we can normalise the coefficient at `i₀` to `1`
      have h1 : (1 : R) ∈ T := IsSimpleRing.one_mem_of_ne_zero_mem T
        (Finsupp.mem_support_iff.mp hi₀)
        ((TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mpr ⟨c, hcJ, subset_rfl, rfl⟩)
      obtain ⟨d, hdJ, hds, hd1⟩ := (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mp h1
      -- by minimality, `Φ d` commutes with every `1 ⊗ a`
      have hcomm (a : R) : (1 ⊗ₜ a) * Φ d = Φ d * (1 ⊗ₜ a) := by
        set d' := d.mapRange (a * ·) (mul_zero a) - d.mapRange (· * a) (zero_mul a) with hd'
        have hΦd' : (1 ⊗ₜ a) * Φ d - Φ d * (1 ⊗ₜ a) = Φ d' := by
          rw [hL, hR, ← map_sub]
        have hd'J : Φ d' ∈ J :=
          hΦd' ▸ J.sub_mem (J.mul_mem_left _ _ hdJ) (J.mul_mem_right _ _ hdJ)
        have hd's : d'.support ⊆ c.support := fun i hi ↦ hds <| by
          have := Finsupp.support_sub hi
          simp only [Finset.mem_union] at this
          exact this.elim (fun h ↦ Finsupp.support_mapRange h) (fun h ↦ Finsupp.support_mapRange h)
        have hd'i₀ : i₀ ∉ d'.support := by simp [hd', hd1]
        have := hmin d' hd'J <| Finset.card_lt_card <|
          (Finset.ssubset_iff_of_subset hd's).mpr ⟨i₀, hi₀, hd'i₀⟩
        rw [← sub_eq_zero, hΦd', this, map_zero]
      -- hence `Φ d` is central, so it is `f ⊗ 1` for some nonzero `f : F`
      have hcenter : Φ d ∈ Subalgebra.center F (F ⊗[K] R) := by
        rw [Subalgebra.mem_center_iff]
        intro y
        induction y using TensorProduct.inductionOn with
        | tmul f r =>
          have : f ⊗ₜ[K] r = algebraMap F (F ⊗[K] R) f * (1 ⊗ₜ r) := by
            simp [Algebra.TensorProduct.tmul_mul_tmul]
          rw [this, mul_assoc, hcomm, ← mul_assoc, Algebra.commutes, mul_assoc]
        | add y z hy hz => rw [add_mul, mul_add, hy, hz]
      have : IsCentral F (F ⊗[K] R) := IsCentral_basechange' F K R
      obtain ⟨f, hf⟩ := Algebra.mem_bot.mp (IsCentral.out hcenter)
      have hf0 : f ≠ 0 := by
        rintro rfl
        have : d = 0 := hΦ_inj (by rw [← hf, map_zero, map_zero])
        simp [this] at hd1
      have : algebraMap F (F ⊗[K] R) f⁻¹ * Φ d = 1 := by
        rw [← hf, ← map_mul, inv_mul_cancel₀ hf0, map_one]
      exact this ▸ J.mul_mem_left _ _ hdJ
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
