/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.CategoryTheory.Category.Preorder

/-!
## Algebra for algebraic geometry

Algebraic results used in `AlgebraicGeometry/`.

-/

@[expose] public section

section Model

universe u

variable {K : Type u} [Field K]

-- written by Claude
open TensorProduct in
/-- A finite type algebra `A` over an algebraic extension `L/K` has a model `A₀` over a
finite extension `E/K` inside `L`, i.e. `L ⊗[E] A₀ ≃ₐ[L] A`. We take `E` to be generated over `K`
by the coefficients of the relations of a finite presentation of `A`. -/
lemma exists_model_of_finiteType {L A : Type u} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [CommRing A] [Algebra L A] [Algebra.FiniteType L A] :
    ∃ (E : IntermediateField K L) (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra E A₀),
      FiniteDimensional K E ∧ Algebra.FiniteType E A₀ ∧ Nonempty (L ⊗[E] A₀ ≃ₐ[L] A) := by
  have : Algebra.FinitePresentation L A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let P := Algebra.Presentation.ofFinitePresentation L A
  let E := IntermediateField.adjoin K P.coeffs
  have : Finite P.coeffs := P.finite_coeffs
  have : P.HasCoeffs E := ⟨fun x hx ↦ ⟨⟨x, IntermediateField.subset_adjoin K _ hx⟩, rfl⟩⟩
  exact ⟨E, P.ModelOfHasCoeffs E, inferInstance, inferInstance,
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x,
    inferInstance, ⟨P.tensorModelOfHasCoeffsEquiv E⟩⟩


-- written by AI (Claude)
open TensorProduct in
/-- The isomorphism `L ⊗[L₁] (L₁ ⊗[K] A) ≃ₐ[L] L ⊗[K] A` sending `x ⊗ (y ⊗ a) ↦ xy ⊗ a`. -/
def rationalModel_equiv {L A : Type u} [Field L] [Algebra K L] (L₁ : IntermediateField K L)
    [CommRing A] [Algebra K A] : L ⊗[L₁] (L₁ ⊗[K] A) ≃ₐ[L] L ⊗[K] A :=
  Algebra.TensorProduct.cancelBaseChange K L₁ L L A

-- aided by claude
open TensorProduct in
lemma exists_ker_rationalModel_map_lift_eq {L A : Type u} [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (I : Ideal (L ⊗[K] A)) :
    ∃ (L₁ : IntermediateField K L) (_ : FiniteDimensional K L₁) (I₁ : Ideal (L₁ ⊗[K] A)),
      Function.Surjective (rationalModel_equiv (A := A) L₁) ∧
        (I₁.map (Algebra.TensorProduct.includeRight (R := L₁) (A := L))).map
          (rationalModel_equiv L₁) = I := by
  have : IsNoetherianRing (L ⊗[K] A) := Algebra.FiniteType.isNoetherianRing L _
  let x : Finset (L ⊗[K] A) := (IsNoetherian.noetherian I).choose
  have hx : Ideal.span x = I := (IsNoetherian.noetherian I).choose_spec
  obtain ⟨L₁, _, hL₁⟩ : ∃ (L₁ : IntermediateField K L) (_ : FiniteDimensional K L₁),
      ∀ y ∈ x, y ∈ (Algebra.TensorProduct.map L₁.val (AlgHom.id K A)).range := by
    obtain ⟨M, hM, hxM⟩ :=
      exists_finite_submodule_left_of_setFinite (x : Set (L ⊗[K] A)) x.finite_toSet
    obtain ⟨S, rfl⟩ := Module.Finite.iff_fg.mp hM
    refine ⟨IntermediateField.adjoin K S,
      IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x,
      fun y hy ↦ ?_⟩
    obtain ⟨z, rfl⟩ := hxM hy
    have hle : Submodule.span K (S : Set L) ≤
        (IntermediateField.adjoin K (S : Set L)).toSubalgebra.toSubmodule :=
      Submodule.span_le.mpr (IntermediateField.subset_adjoin K _)
    refine ⟨(Submodule.inclusion hle).rTensor A z, ?_⟩
    clear hy
    induction z using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  classical
  let x' : Finset (L₁ ⊗[K] A) :=
    x.attach.image fun y ↦ ((AlgHom.mem_range _).mp (hL₁ y.1 y.2)).choose
  have hx₁ : x'.image (Algebra.TensorProduct.map L₁.val (AlgHom.id K A)) = x := by
    ext y
    simp only [x', Finset.image_image, Finset.mem_image, Finset.mem_attach, true_and,
      Function.comp_apply]
    constructor
    · rintro ⟨⟨z, hz⟩, rfl⟩
      rwa [((AlgHom.mem_range _).mp (hL₁ z hz)).choose_spec]
    · exact fun hy ↦ ⟨⟨y, hy⟩, ((AlgHom.mem_range _).mp (hL₁ y hy)).choose_spec⟩
  let I₁ : Ideal (L₁ ⊗[K] A) := Ideal.span x'
  use L₁, inferInstance, I₁
  -- written by AI (Claude)
  refine ⟨(rationalModel_equiv L₁).surjective, ?_⟩
  rw [← hx, ← hx₁, Finset.coe_image]
  simp only [I₁, Ideal.map_span, Set.image_image]
  refine congrArg _ (Set.image_congr' fun z ↦ ?_)
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [rationalModel_equiv, Algebra.smul_def]
  | add a b ha hb => simp only [map_add, ha, hb]

end Model

section IntermediateField

namespace IntermediateField

open CategoryTheory

universe u

variable {K₀ K : Type*} [Field K] [Field K₀] [Algebra K₀ K]

-- written by AI (Claude)
def forget (F : IntermediateField K₀ K) :
    IntermediateField F K ⥤ {L : IntermediateField K₀ K // F ≤ L} :=
  (IntermediateField.extendScalars.orderIso F).symm.monotone.functor

-- Commented out: unused, and slows instance search (heartbeat timeouts).
-- instance forget_algebra {F : IntermediateField K₀ K} {L : IntermediateField F K} {A : Type*}
--     [CommRing A] [Algebra L A] : Algebra (F.forget.obj L).val A :=
--   inferInstanceAs (Algebra L A)

instance {F : IntermediateField K₀ K} {L : IntermediateField F K} :
    Algebra F (F.forget.obj L).val :=
  inferInstanceAs (Algebra F L)

open TensorProduct in
def forget_basechange {F : IntermediateField K₀ K} (L : IntermediateField F K) (A : Type*)
    [CommRing A] [Algebra F A] : L ⊗[F] A ≃+* (F.forget.obj L).val ⊗[F] A :=
  (Algebra.TensorProduct.congr
    ({ RingEquiv.refl L with commutes' := fun _ ↦ rfl } : L ≃ₐ[F] (F.forget.obj L).val)
    AlgEquiv.refl).toRingEquiv

-- written by AI (Claude)
/-- The identity `L ≃+* (F.forget.obj L).val`: both have the same underlying field. -/
def forgetRingEquiv (F : IntermediateField K₀ K) (L : IntermediateField F K) :
    L ≃+* (F.forget.obj L).val where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

-- written by AI (Claude)
instance {F : IntermediateField K₀ K} {L : IntermediateField F K} :
    RingHomInvPair (forgetRingEquiv F L : L →+* (F.forget.obj L).val)
      (forgetRingEquiv F L).symm :=
  .of_ringEquiv _

-- written by AI (Claude)
instance {F : IntermediateField K₀ K} {L : IntermediateField F K} :
    RingHomInvPair ((forgetRingEquiv F L).symm : (F.forget.obj L).val →+* L)
      (forgetRingEquiv F L) :=
  .of_ringEquiv_symm _

-- written by AI (Claude)
open TensorProduct in
/-- `forget_basechange` as a semilinear isomorphism along `forgetRingEquiv F L`. -/
def forget_basechangeₛₗ {F : IntermediateField K₀ K} (L : IntermediateField F K) (A : Type*)
    [CommRing A] [Algebra F A] :
    L ⊗[F] A ≃ₛₗ[(forgetRingEquiv F L : L →+* (F.forget.obj L).val)]
      (F.forget.obj L).val ⊗[F] A :=
  { (forget_basechange L A).toAddEquiv with
    map_smul' l x := by
      induction x using TensorProduct.inductionOn with
      | tmul a b => rfl
      | add x y hx hy => simp_all [smul_add] }

end IntermediateField

end IntermediateField
