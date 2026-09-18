module

public import Mathlib
public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.IntHom
public import CMAbelianVarieties.AbstractNonsense.PullbackAddGrp

/-!
## Main goal

The main goal of this section is to define the Tate module of an Abelian Variety
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp Limits CartesianMonoidalCategory
open AddMonObj MonoidalCategory

open AlgebraicGeometry Scheme Hom CategoryTheory Iso

variable {K : Type*} [Field K]
variable {A : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable {p : ℕ} {hp : p.Prime}

/-
the unit element in `Over (Spec ↧K)`, i.e, `Spec K`
-/
abbrev specᵤ (K : Type*) [Field K] := 𝟙_ (Over (Spec ↧K))
abbrev p₁ (n : ℤ) := pullback.fst (n[A]) ζ
abbrev p₂ (n : ℤ) := pullback.snd (n[A]) ζ


notation:50 A:51 "[" n:51 "]( " K:50 " )" => (specᵤ K ⟶ A[n])

lemma int_hom_rational (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (n : ℕ) (X : Over (Spec ↧K)) : ∀ g : X ⟶ A, n • g = g ≫ (n[A]) := sorry

lemma rational_torsion (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (n : ℕ) : ∀ g : A[n](K), n • g = 0 := by
  intro g
  let p : (specᵤ K ⟶ A[n]) →ₗ[ℤ] (specᵤ K ⟶ A)
    := AddMonoidHom.toIntLinearMap (IsAddMonHom.addMonoidHom (p₁ n) (specᵤ K))
  have : p (n • g) = n • p g := LinearMap.map_smul_of_tower p n g
  have : n • p g = p g ≫ (n[A]) := by
    induction n with
    | zero =>
        simp [int_hom]; rfl
    | succ k hk =>

        sorry
  sorry

/-
Steps:
1. Define a function from `A[n](K)` to function `{pt} → |A[n]|`
2. the above function is injective
3. this should imply finitness.
-/
lemma finite_torsion_points {n : ℤ} (A : Over (Spec ↧K)) [IsProper A.hom]
    [GeometricallyIntegral A.hom] [AddGrpObj A] (hn : n ≠ 0) : Finite (AddGrpCat.mk (A[n](K)))
    := by
  simp
  let : ((specᵤ K) ⟶ A[n]) →  ((specᵤ K).left.carrier ⟶ A[n].left.carrier) := sorry
  #check (specᵤ K).left.carrier
  #check Scheme
  sorry

def torsion_map_of_schemes (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (p : ℤ) {n m : ℕ} (h : n ≥ m) : A[p ^ n] ⟶ A[p ^ m] := by
  have : p  ^ m ∣ p ^ n := by
    have : n = m + (n - m) := by
      exact Eq.symm (Nat.add_sub_of_le h)
    rw [Eq.symm (Nat.add_sub_of_le h), Int.pow_add]
    use p ^ (n - m)
  exact ker_int_hom A this

instance {p : ℤ} {n m : ℕ} {h : n ≥ m} : IsAddMonHom (torsion_map_of_schemes A p h) := by
  simp only [torsion_map_of_schemes]
  infer_instance

def torsion_map (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (p : ℤ) {n m : ℕ} (h : n ≥ m) : A[p ^ n](K) →+ A[p ^ m](K) := by
  exact IsAddMonHom.addMonoidHom (torsion_map_of_schemes A p h) (specᵤ K)

def torsion_point_as_profinite {n : ℤ} (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral
    A.hom] [AddGrpObj A] (hn : n ≠ 0) : ProfiniteAddGrp :=
  ProfiniteAddGrp.ofFiniteAddGrp (@FiniteAddGrp.mk (AddGrpCat.mk (A[n](K))) (finite_torsion_points A
  hn))



#min_imports
