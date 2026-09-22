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

/-
the unit element in `Over (Spec ↧K)`, i.e, `Spec K`
-/
abbrev specᵤ (K : Type*) [Field K] := 𝟙_ (Over (Spec ↧K))
abbrev p₁ (n : ℤ) := pullback.fst (n[A]) ζ
abbrev p₂ (n : ℤ) := pullback.snd (n[A]) ζ

lemma int_hom_rational (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (n : ℕ) (X : Over (Spec ↧K)) : ∀ g : X ⟶ A, n • g = g ≫ (n[A]) := sorry

lemma rational_torsion (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (n : ℕ) : ∀ g : (specᵤ K ⟶ A[n]), n • g = 0 := by
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
-- *The proof was done by Claude*
-- It probably needs to be broken down and we need to make use of older results.
lemma finite_torsion_points {n : ℤ} (A : Over (Spec ↧K)) [IsProper A.hom]
    [GeometricallyIntegral A.hom] [AddGrpObj A] (hn : n ≠ 0) :
    Finite (AddGrpCat.mk (specᵤ K ⟶ A[n])) := by
  have hhom : (A[n]).hom = (pullback.snd (n[A]) ζ[A]).left := by
    have := Over.w (pullback.snd (n[A]) ζ[A])
    simpa using this.symm
  set X := (A[n]).left with hX
  have hfin : IsFinite ((A[n]).hom) := hhom ▸ step₂ hn
  have hAff : IsAffine X := isAffine_of_isAffineHom (A[n]).hom
  set B := Γ(Spec ↧K, ⊤) with hB
  let ψ := (A[n]).hom.appTop
  algebraize [ψ.hom]
  have hMF : Module.Finite B Γ(X, ⊤) := by
    apply IsFinite.finite_app
    rw [← affine_iff_top]
    infer_instance
  have hBAR : IsArtinianRing B :=
    RingEquiv.isArtinianRing (ΓSpecIso ↧K).symm.commRingCatIsoToRingEquiv
  have hAR : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite B Γ(X, ⊤)
  have hDom : IsDomain B :=
    MulEquiv.isDomain K (ΓSpecIso ↧K).commRingCatIsoToRingEquiv
  -- `Γ(X, ⊤) →ₐ[B] B` is finite: it injects into `PrimeSpectrum Γ(X, ⊤)` via the kernel,
  -- since an algebra homomorphism into `B` is determined by its kernel.
  have step2 : Finite (Γ(X, ⊤) →ₐ[B] B) := by
    have hinj : Function.Injective (fun f : Γ(X, ⊤) →ₐ[B] B =>
        (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum Γ(X, ⊤))) := by
      intro f g h
      have hker : RingHom.ker f = RingHom.ker g := by
        simpa using congrArg PrimeSpectrum.asIdeal h
      ext x
      have hx : x - algebraMap B Γ(X, ⊤) (f x) ∈ RingHom.ker f := by
        simp [RingHom.mem_ker, AlgHom.commutes]
      rw [hker] at hx
      simp only [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hx
      exact hx.symm
    exact Finite.of_injective _ hinj
  -- Every K-point `g : specᵤ K ⟶ A[n]` gives, via global sections, an algebra map
  -- `Γ(X, ⊤) →ₐ[B] B`, and this assignment is injective since `X` is affine.
  have step1 : Function.Injective (fun g : (specᵤ K ⟶ A[n]) =>
      (⟨g.left.appTop.hom, fun c => by
        have hw0 : g.left ≫ (A[n]).hom = 𝟙 (Spec ↧K) := Over.w g
        have hw := congrArg Scheme.Hom.appTop hw0
        simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at hw
        have hpt := congrArg (fun (φ : B ⟶ B) => φ.hom c) hw
        rw [RingHom.algebraMap_toAlgebra]
        exact hpt⟩ :
        Γ(X, ⊤) →ₐ[B] B)) := by
    intro g1 g2 h
    have happ : g1.left.appTop = g2.left.appTop := by
      have := congrArg (fun (f : Γ(X, ⊤) →ₐ[B] B) => f.toRingHom) h
      exact CommRingCat.hom_ext (by simpa using this)
    have : g1.left = g2.left := ext_of_isAffine happ
    exact Over.OverMorphism.ext this
  exact Finite.of_injective _ step1

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
    [AddGrpObj A] (p : ℤ) {n m : ℕ} (h : n ≥ m) : (specᵤ K ⟶ A[p ^ n]) →+ (specᵤ K ⟶ A[p ^ m]) := by
  exact IsAddMonHom.addMonoidHom (torsion_map_of_schemes A p h) (specᵤ K)

def torsion_point_as_profinite {n : ℤ} (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral
    A.hom] [AddGrpObj A] (hn : n ≠ 0) : ProfiniteAddGrp :=
  ProfiniteAddGrp.ofFiniteAddGrp (@FiniteAddGrp.mk (AddGrpCat.mk (specᵤ K ⟶ A[n]))
  (finite_torsion_points A hn))

notation:50 A:51 "[" hn:51 "]ₚ" => torsion_point_as_profinite A hn

-- *This defintion was written by Claude*
-- It look wrong because it does not make use of the fact that `n ≠ 0`
-- So, its probably not the defintion we want.
def torsion_point_as_profinite_map {m n : ℤ} (A : Over (Spec ↧K)) [IsProper A.hom]
    [GeometricallyIntegral A.hom] [AddGrpObj A] (h : m ∣ n) (hn : n ≠ 0) :
    let hm : m ≠ 0 := fun hm0 => hn (by obtain ⟨c, hc⟩ := h; subst hc; simp [hm0])
    A[hn]ₚ ⟶ A[hm]ₚ :=
  ProfiniteAddGrp.ofFiniteAddGrpHom (InducedCategory.homMk
  (AddGrpCat.ofHom (IsAddMonHom.addMonoidHom (ker_int_hom A h) (specᵤ K))))

open Opposite

def tate_module_chain (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] {p : ℕ} (hp : p ≠ 0) : ℕᵒᵖ ⥤ ProfiniteAddGrp where
  obj n := by
    have : ((p ^ (unop n)) : ℤ) ≠ 0 := by
      contrapose hp
      simp only [pow_eq_zero_iff', Int.natCast_eq_zero, ne_eq] at hp
      exact hp.1
    exact A[this]ₚ
  map φ := by
    rename_i n m
    have : unop m ≤ unop n := by
      exact le_of_op_hom φ
    have hn : (p ^ (unop n) : ℤ) ≠ 0 := by
      contrapose hp
      simp only [pow_eq_zero_iff', Int.natCast_eq_zero, ne_eq] at hp
      exact hp.1
    have : (p ^ (unop m) : ℤ) ∣ p ^ (unop n) := by
      obtain ⟨k, hk⟩ : p ^ (unop m) ∣ p ^ (unop n) := by
        exact Nat.pow_dvd_pow p this
      use k
      exact Eq.symm (Nat.ToInt.of_eq rfl rfl (id (Eq.symm hk)))
    exact torsion_point_as_profinite_map A this hn
  map_id n := by
    sorry
  map_comp := sorry

def tate_module (A : Over (Spec ↧K)) [IsProper A.hom]
    [GeometricallyIntegral A.hom] [AddGrpObj A] {p : ℕ} (hp : p.Prime) :
    ProfiniteAddGrp :=
  ProfiniteAddGrp.limit (tate_module_chain A (Nat.Prime.ne_zero hp))



#min_imports
