module

public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.IntHom
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
## Main goal

The main goal of this section is to define the Tate module of an Abelian Variety

Fixes:
Some things below look weird. Both `torsion_point_as_profinite` and `AddGrpCatHom_of_torsion_map`
require us to view `A[n](K)` an an object in the category `FiniteAddGrp`. But I never define
it an an object there. That makes the definitions look weird. Maybe I should create definitions
to view it an an element of `AddGrpCate` and then also `FiniteAddGrp`. So that it look much
neater in the two things mentioned above!
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp Limits CartesianMonoidalCategory
open AddMonObj MonoidalCategory IntHom

open AlgebraicGeometry Scheme Hom CategoryTheory Iso

variable {K : Type*} [Field K]
variable {A : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

/-
the cannonical geometric point in `Over (Spec ↧K)`, i.e, `Spec K̄`
-/
abbrev gspec (K : Type*) [Field K] : (Over (Spec ↧K)) where
  left := Spec ↧(AlgebraicClosure K)
  right := ⟨⟨⟩⟩
  hom := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
private abbrev p₁ (n : ℤ) := pullback.fst ([n]_ A) ζ
private abbrev p₂ (n : ℤ) := pullback.snd ([n]_ A) ζ

/-
_PROBABLY DON'T NEED THIS - AT LEAST MOVE IT TO ABSTRACTNONSENCE/INTHOM IF NEEDED_
lemma int_hom_rational (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (n : ℕ) (X : Over (Spec ↧K)) : ∀ g : X ⟶ A, n • g = g ≫ ([n]_ A) := sorry

lemma rational_torsion (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (n : ℕ) : ∀ g : (gspec K ⟶ A[n]), n • g = 0 := by
  intro g
  let p : (gspec K ⟶ A[n]) →ₗ[ℤ] (gspec K ⟶ A)
    := AddMonoidHom.toIntLinearMap (IsAddMonHom.addMonoidHom (p₁ n) (gspec K))
  have : p (n • g) = n • p g := LinearMap.map_smul_of_tower p n g
  have : n • p g = p g ≫ ([n]_ A) := by
    induction n with
    | zero =>
        simp [int_hom]; rfl
    | succ k hk =>

        sorry
  sorry-/

-- *The proof was done by Claude*
-- It probably needs to be broken down and we need to make use of older results.
lemma finite_torsion_points {n : ℤ} (A : Over (Spec ↧K)) [IsProper A.hom]
    [GeometricallyIntegral A.hom] [AddGrpObj A] (hn : n ≠ 0) :
    Finite (AddGrpCat.mk (gspec K ⟶ A[n])) := by
  sorry
  /- __Old proof for `specᵤ K` (K-points); needs adapting to `gspec K` (K̄-points):__
  have hhom : (A[n]).hom = (pullback.snd ([n]_ A) ζ[A]).left := by
    have := Over.w (pullback.snd ([n]_ A) ζ[A])
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
  have step1 : Function.Injective (fun g : (gspec K ⟶ A[n]) =>
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
  -/

/--
For `m ∣ n`, we have a map abelian groups `A[n](K) →+ A[m](K)`
-/
def torsion_map (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] {n m : ℤ} (h : m ∣ n) : (gspec K ⟶ A[n]) →+ (gspec K ⟶ A[m]) := by
  exact IsAddMonHom.addMonoidHom (ker_int_hom A h) (gspec K)


-- I probably do not need this
/--
For `m ∣ n`, we have a morphism `A[n](K) ⟶ A[m](K)` in the category `AddGrpCat`
-/
def AddGrpCatHom_of_torsion_map (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] {n m : ℤ} (h : m ∣ n) : (↧(gspec K ⟶ A[n]) : AddGrpCat) ⟶ ↧(gspec K ⟶ A[m])
    := AddGrpCat.ofHom (torsion_map A h)

def torsion_point_as_profinite {n : ℤ} (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral
    A.hom] [AddGrpObj A] (hn : n ≠ 0) : ProfiniteAddGrp :=
  ProfiniteAddGrp.ofFiniteAddGrp (@FiniteAddGrp.mk (↧(gspec K ⟶ A[n]) : AddGrpCat)
  (finite_torsion_points A hn))

notation:50 A:51 "[" hn:51 "]ₚ" => torsion_point_as_profinite A hn

/--
For `m ∣ n`, we have a morphism `A[n](K) ⟶ A[m](K)` in the category `FiniteAddGrp`
-/
def FiniteAddGrpHom_of_torsion_map (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral
    A.hom] [AddGrpObj A] {n m : ℤ} (h : m ∣ n) (hn : n ≠ 0) :=
  @FiniteAddGrp.ofHom _ _ _ (finite_torsion_points A hn) _ (finite_torsion_points A
    (ne_zero_of_dvd_ne_zero hn h)) (torsion_map A h)

def torsion_point_as_profinite_map {m n : ℤ} (A : Over (Spec ↧K)) [IsProper A.hom]
    [GeometricallyIntegral A.hom] [AddGrpObj A] (h : m ∣ n) (hn : n ≠ 0) :
    A[hn]ₚ ⟶ A[(ne_zero_of_dvd_ne_zero hn h)]ₚ := by
  exact ProfiniteAddGrp.ofFiniteAddGrpHom
    (FiniteAddGrpHom_of_torsion_map A h hn)

lemma torsion_map_id {n : ℤ} (A : Over (Spec ↧K)) [IsProper A.hom]
    [GeometricallyIntegral A.hom] [AddGrpObj A] (hn : n ≠ 0) :
    torsion_point_as_profinite_map A (Int.dvd_refl n) hn = 𝟙 (A[hn]ₚ) := by
  have : ker_int_hom A (Int.dvd_refl n) = 𝟙 (A[n]) := by
    have : ([1]_ A) = 𝟙 A := by
      simp [int_hom]
    simp [ker_int_hom, Int.ediv_self hn, this]
  simp only [torsion_point_as_profinite_map, FiniteAddGrpHom_of_torsion_map, torsion_map, this]
  rfl

lemma torsion_map_comp {k m n : ℤ} (A : Over (Spec ↧K)) [IsProper A.hom]
    [GeometricallyIntegral A.hom] [AddGrpObj A] (hn : n ≠ 0) (hkm : k ∣ m)
    (hmn : m ∣ n) :
    (torsion_point_as_profinite_map A hmn hn) ≫ (torsion_point_as_profinite_map A hkm
    (ne_zero_of_dvd_ne_zero hn hmn)) = (torsion_point_as_profinite_map A (Int.dvd_trans hkm hmn) hn)
    := by
  have : ker_int_hom A (Int.dvd_trans hkm hmn) = (ker_int_hom A hmn) ≫ (ker_int_hom A hkm) := by
    have fst : ker_int_hom A (Int.dvd_trans hkm hmn) ≫ p₁ k
        = ((ker_int_hom A hmn) ≫ (ker_int_hom A hkm)) ≫ p₁ k
        := by
      have {s t : ℤ} (hst : s ∣ t) : (ker_int_hom A hst) ≫ p₁ s = p₁ t ≫ [t/s]_ A := by
        simp [ker_int_hom]
      -- Claude found the last three rewrites in the below sequence
      rw [Category.assoc, this hkm, Category.assoc', this hmn, this (Int.dvd_trans hkm hmn),
        Category.assoc, int_hom_comp, mul_comm, ← Int.mul_ediv_assoc _ hkm, Int.ediv_mul_cancel hmn]
    have snd : ker_int_hom A (Int.dvd_trans hkm hmn) ≫ p₂ k
        = ((ker_int_hom A hmn) ≫ (ker_int_hom A hkm)) ≫ p₂ k
        := by
      have {s t : ℤ} (hst : s ∣ t) : (ker_int_hom A hst) ≫ p₂ s = p₂ t := by
        simp [ker_int_hom]
      rw [Category.assoc, this hkm, this hmn, this (Int.dvd_trans hkm hmn)]
    exact pullback.hom_ext fst snd
  simp only [torsion_point_as_profinite_map, FiniteAddGrpHom_of_torsion_map, torsion_map, this]
  rfl

def tate_module_chain (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] {p : ℕ} (hp : p ≠ 0) : ℕᵒᵖ ⥤ ProfiniteAddGrp := by
  have h {m n : ℕᵒᵖ} (φ : n ⟶ m) : (p ^ m.unop : ℤ) ∣ (p ^ n.unop) := by
    have : m.unop ≤ n.unop := by
      exact le_of_op_hom φ
    obtain ⟨k, hk⟩ : (p ^ m.unop) ∣ (p ^ n.unop) := by
      exact Nat.pow_dvd_pow p this
    use k
    exact Eq.symm <| Nat.ToInt.of_eq rfl rfl <| id <| Eq.symm hk
  exact {
    obj n := by
      have : ((p ^ (n.unop)) : ℤ) ≠ 0 := by
        contrapose hp
        simp only [pow_eq_zero_iff', Int.natCast_eq_zero, ne_eq] at hp
        exact hp.1
      exact A[this]ₚ
    map φ := by
      rename_i n m
      have hn : (p ^ (n.unop) : ℤ) ≠ 0 := by
        contrapose hp
        simp only [pow_eq_zero_iff', Int.natCast_eq_zero, ne_eq] at hp
        exact hp.1
      exact torsion_point_as_profinite_map A (h φ) hn
    map_id n := by
      have : ((p ^ (n.unop)) : ℤ) ≠ 0 := by
        contrapose hp
        simp only [pow_eq_zero_iff', Int.natCast_eq_zero, ne_eq] at hp
        exact hp.1
      exact torsion_map_id A this
    map_comp := by
      intro n m k hnm hmk
      have hmn : (p ^ (m.unop) : ℤ) ∣ p ^ (n.unop) := h hnm
      have hkm : (p ^ (k.unop) : ℤ) ∣ p ^ (m.unop) := h hmk
      have hn : (p ^ (n.unop) : ℤ) ≠ 0 := by
        contrapose hp
        simp only [pow_eq_zero_iff', Int.natCast_eq_zero, ne_eq] at hp
        exact hp.1
      exact (torsion_map_comp A hn hkm hmn).symm
  }

def tate_module {p : ℕ} (hp : p.Prime) (A : Over (Spec ↧K)) [IsProper A.hom]
    [GeometricallyIntegral A.hom] [AddGrpObj A] :
    ProfiniteAddGrp :=
  ProfiniteAddGrp.limit (tate_module_chain A (Nat.Prime.ne_zero hp))

namespace TateModule
-- Claude helped create the notation

/-- `T_ p (A)` is the `p`-adic Tate module of `A`. The primality proof of `p` is found
automatically: from a hypothesis in context, a `Fact p.Prime` instance, or `norm_num`. -/
scoped syntax:max "T_ " term:max " (" term ")" : term

scoped macro_rules
  | `(T_ $p ($A)) => `(tate_module (p := $p) (by first | assumption | exact Fact.out | norm_num) $A)

end TateModule

section Representation

open TateModule

variable {A B : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom]
  [AddGrpObj A] [IsProper B.hom] [GeometricallyIntegral B.hom] [AddGrpObj B]
variable {p : ℕ} (f : A ⟶ B) [IsAddMonHom f]

-- I'll probably not keep this definition
def blah (p n : ℕ) : A[p ^ n] ⟶ B[p ^ n] := by
  exact functorial_ker_int (p ^ n) f

def tate_module_representation (hp : p.Prime) : T_ p (A) ⟶ T_ p (B) := sorry

end Representation



#min_imports
