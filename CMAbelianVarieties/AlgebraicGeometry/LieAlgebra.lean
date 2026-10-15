/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib
public import CMAbelianVarieties.ForMathlib.Endomorphism

/-!
## Lie algebra of a group object

In this file we shall define the Lie algebra of a group scheme over a field
`K` as a vector space over `K`.

_This needs to be rewritten at some point_

-/

@[expose] public noncomputable section

-- Almost all the proofs in this file were constructured by Claude.

open CategoryTheory AlgebraicGeometry IsLocalRing AddMonObj AddGrp End
open scoped End

universe u

variable {K : Type u} [Field K]
variable {G : Over (Spec ↧K)} [AddGrpObj G]

/-- The identity point of `G`: the image of the unique point of `Spec K` under the
zero section `ζ[G] : 𝟙_ _ ⟶ G`. -/
def e (G : Over (Spec ↧K)) [AddGrpObj G] : (⊤ : G.left.Opens) :=
  ⟨ζ[G].left (closedPoint K), trivial⟩

set_option quotPrecheck false in
/-- `𝒪_ H` is the local ring (stalk) of `H` at the identity point `e H`. -/
notation "𝒪_ " H:max => (H).left.presheaf.stalk (e H)

set_option quotPrecheck false in
/-- `κ_ H` is the residue field of `H` at the identity point `e H`. -/
notation "κ_ " H:max => ResidueField (𝒪_ H)

/-- The Lie algebra of `G`: the dual of the cotangent space `m / m ^ 2` of `G` at `e`, as a
vector space over the residue field at `e`. -/
abbrev Lie (G : Over (Spec ↧K)) [AddGrpObj G] :=
  Module.Dual (κ_ G) (CotangentSpace (𝒪_ G))

lemma image_unit_of_End (f : End (mk G)) : (f.asHom.hom.hom : G ⟶ G).left (e G) = e G := by
  simp only [e, Over.tensorUnit_left]
  nth_rw 2 [← IsAddMonHom.zero_hom f.asHom.hom.hom]
  rfl

/-- The endomorphism of the stalk of `G` at `e G` induced by an endomorphism of `G`. -/
def stalkEnd (f : End (mk G)) :
    𝒪_ G ⟶ 𝒪_ G :=
  (G.left.presheaf.stalkCongr (.of_eq (image_unit_of_End f).symm)).hom ≫
    (f.asHom.hom.hom.left).stalkMap (e G)

instance (f : End (mk G)) : IsLocalHom (stalkEnd f).hom := by
  simp only [stalkEnd]
  infer_instance

/-- If `φ : X ⟶ X` fixes a morphism `f : S ⟶ X` then it induces the identity on the residue
fields of the points in the image of `f`. -/
lemma Scheme.residueFieldCongr_residueFieldMap_of_comp_eq {S X : Scheme} (f : S ⟶ X)
    (φ : X ⟶ X) (hf : f ≫ φ = f) (p : S) :
    (X.residueFieldCongr (show φ (f p) = f p by rw [← Scheme.Hom.comp_apply, hf]).symm).hom ≫
      φ.residueFieldMap (f p) = 𝟙 _ := by
  have h : φ (f p) = f p := by rw [← Scheme.Hom.comp_apply, hf]
  have h₁ : (X.residueFieldCongr h.symm).hom ≫ φ.residueFieldMap (f p) ≫ f.residueFieldMap p =
      𝟙 _ ≫ f.residueFieldMap p := by
    rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr hf]
    simp only [Scheme.residueFieldCongr, Category.id_comp]
    erw [eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [h]
  ext a
  exact (f.residueFieldMap p).hom.injective congr(CommRingCat.Hom.hom $h₁ a)

/-- An endomorphism `f` of `G` induces the identity on the residue field `κ_ G` at the identity
point `e G`. -/
lemma residueFieldCongr_residueFieldMap (f : End (mk G)) :
    (G.left.residueFieldCongr (image_unit_of_End f).symm).hom ≫
      (f.asHom.hom.hom.left).residueFieldMap (e G) = 𝟙 _ :=
  Scheme.residueFieldCongr_residueFieldMap_of_comp_eq ζ[G].left f.asHom.hom.hom.left
    (congrArg CommaMorphism.left (IsAddMonHom.zero_hom f.asHom.hom.hom)) (closedPoint K)

/-- The map `𝒪_ G ⟶ 𝒪_ G ⟶ κ_ G`, where the first is induced by `f`, is the
same as the quotient morphism `𝒪_ G ⟶ κ_ G` -/
lemma stalkEnd_residue (f : End (mk G)) :
    stalkEnd f ≫ G.left.residue (e G) = G.left.residue (e G) := by
  rw [stalkEnd, Category.assoc, ← Scheme.residue_residueFieldMap, ← Category.assoc,
    ← Scheme.residue_residueFieldCongr _ (image_unit_of_End f).symm, Category.assoc,
    residueFieldCongr_residueFieldMap, Category.comp_id]

/-- for `a : 𝒪_ G`, the image of `a` in `κ_ G` is the same as the image
of `a` along the composition `𝒪_ G ⟶ 𝒪_ G ⟶ κ_ G`, where the first is induced
by `f`. -/
lemma residue_stalkEnd (f : End (mk G)) (a : 𝒪_ G) :
    residue _ ((stalkEnd f).hom a) = residue _ a :=
  congr($(stalkEnd_residue f).hom a)

/-- `mₑ ⊆ f⁻¹(mₑ)` along the map `f`. -/
lemma maximalIdeal_le_comap_stalkEnd (f : End (mk G)) :
    maximalIdeal (𝒪_ G) ≤
      (maximalIdeal _).comap (stalkEnd f).hom.toIntAlgHom :=
  fun r hr ↦ map_nonunit (stalkEnd f).hom r hr

/-- The endomorphism of the cotangent space of `G` at `e G` induced by an endomorphism
of `G`.
i.e., `(mₑ / mₑ^2) ⟶[κ_ G] (mₑ / mₑ^2)` -/
def cotangentEnd (f : End (mk G)) :
    CotangentSpace (𝒪_ G) →ₗ[κ_ G]
      CotangentSpace (𝒪_ G) where
  __ := Ideal.mapCotangent (maximalIdeal _) (maximalIdeal _) (stalkEnd f).hom.toIntAlgHom
    (maximalIdeal_le_comap_stalkEnd f)
  map_smul' c v := by
    obtain ⟨a, rfl⟩ := residue_surjective c
    obtain ⟨r, rfl⟩ := Ideal.toCotangent_surjective _ v
    change Ideal.mapCotangent _ _ _ (maximalIdeal_le_comap_stalkEnd f)
        (residue _ a • Ideal.toCotangent _ r) =
      residue _ a • Ideal.mapCotangent _ _ _ (maximalIdeal_le_comap_stalkEnd f)
        (Ideal.toCotangent _ r)
    nth_rw 2 [← residue_stalkEnd f a]
    rw [← ResidueField.algebraMap_eq, algebraMap_smul, algebraMap_smul, ← map_smul,
      Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, ← map_smul]
    congr 1
    ext
    exact map_mul (stalkEnd f).hom a r

/-- The endomorphism `𝒪_{X, x} ⟶ 𝒪_{X, x}` induced by a morphism `φ : X ⟶ X` fixing `x`. -/
def AlgebraicGeometry.Scheme.Hom.fixedStalkMap {X : Scheme} (φ : X ⟶ X) (x : X) (h : φ x = x) :
    X.presheaf.stalk x ⟶ X.presheaf.stalk x :=
  (X.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ φ.stalkMap x

/-- If `φ, ψ : X ⟶ X` both fix `x`, then the endomorphism of the stalk `𝒪_{X, x}` induced by
`ψ ≫ φ` is the one induced by `φ` followed by the one induced by `ψ` -/
lemma AlgebraicGeometry.Scheme.Hom.fixedStalkMap_comp {X : Scheme} (φ ψ : X ⟶ X) (x : X)
    (hφ : φ x = x) (hψ : ψ x = x) :
    (ψ ≫ φ).fixedStalkMap x (by rw [Scheme.Hom.comp_apply, hψ, hφ]) =
      φ.fixedStalkMap x hφ ≫ ψ.fixedStalkMap x hψ := by
  rw [fixedStalkMap, fixedStalkMap, fixedStalkMap, Category.assoc,
    Scheme.Hom.stalkMap_congr_point_assoc φ x (ψ x) hψ.symm, Scheme.Hom.stalkMap_comp]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.stalkSpecializes_comp_assoc]
  rfl

/-- `𝟙 : X ⟶ X` induces the morphism `id : 𝒪_ G ⟶ 𝒪_ G` -/
lemma stalkEnd_one : stalkEnd (1 : End (mk G)) = 𝟙 _ := by
  erw [stalkEnd, Scheme.Hom.stalkMap_id]
  exact (Category.comp_id _).trans (TopCat.Presheaf.stalkSpecializes_refl _ _)

/-- `f * g : G ⟶ G` induces the composition `𝒪_ G ⟶ 𝒪_ G ⟶ 𝒪_ G` where the first
is induces by `f` and the second by `g` -/
lemma stalkEnd_mul (f g : End (mk G)) : stalkEnd (f * g) = stalkEnd f ≫ stalkEnd g :=
  Scheme.Hom.fixedStalkMap_comp _ _ _ (image_unit_of_End f) (image_unit_of_End g)

/-- for `x : Spec K`, the local ring `𝒪ₓ` is a field -/
lemma isField_stalk_Spec_field (x : Spec ↧K) : IsField ((Spec ↧K).presheaf.stalk x) := by
  refine isField_stalk_of_closure_mem_irreducibleComponents _ x ?_
  rw [Set.eq_univ_of_forall fun y ↦ subset_closure (Subsingleton.elim y x ▸ rfl)]
  simp [irreducibleComponents_eq_singleton]

/-- For `r : mₑ`, the image of `r` along the map `(mₑ / mₑ^2) ⟶[κ_ G] (mₑ / mₑ^2)`
induced bt `f`, comes from the lift `𝒪_ G ⟶ 𝒪_ G` which is induced by `f` -/
lemma cotangentEnd_toCotangent (f : End (mk G)) (r : maximalIdeal (𝒪_ G)) :
    cotangentEnd f (Ideal.toCotangent _ r) =
      Ideal.toCotangent _ ⟨(stalkEnd f).hom r, map_nonunit (stalkEnd f).hom _ r.2⟩ :=
  rfl

/-- The morphism `(mₑ / mₑ^2) ⟶[κ_ G] (mₑ / mₑ^2)` induced by `id`, is
the identity morphism -/
lemma cotangentEnd_one : cotangentEnd (1 : End (mk G)) = LinearMap.id := by
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.toCotangent_surjective _ v
  rw [cotangentEnd_toCotangent, LinearMap.id_apply]
  exact congrArg _ (Subtype.ext (by simp [stalkEnd_one]))

/-- `f * g : G ⟶ G` induces the composition `(mₑ / mₑ^2) ⟶ (mₑ / mₑ^2) ⟶ (mₑ / mₑ^2)` of
`κ_ G`-linear maps, where the first is induced by `f` and the second by `g` -/
lemma cotangentEnd_mul (f g : End (mk G)) :
    cotangentEnd (f * g) = cotangentEnd g ∘ₗ cotangentEnd f := by
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.toCotangent_surjective _ v
  simp only [LinearMap.comp_apply, cotangentEnd_toCotangent]
  exact congrArg _ (Subtype.ext (by simp [stalkEnd_mul]))

/-- If `r : mₑ`, then under the map `𝒪_e ⟶ 𝒪_e` induced by the composition `toUnit ≫ ζ`,
we have `r ↦ 0` -/
lemma Scheme.stalkCongr_hom_stalkMap_comp_apply_eq_zero {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ X)
    (x : X) (h : (f ≫ g) x = x) (hY : IsField (Y.presheaf.stalk (f x))) (r : X.presheaf.stalk x)
    (hr : r ∈ maximalIdeal (X.presheaf.stalk x)) :
    ((X.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ (f ≫ g).stalkMap x).hom r = 0 := by
  have hn := map_nonunit (g.stalkMap (f x)).hom _
    (map_nonunit (X.presheaf.stalkCongr (.of_eq h.symm)).hom.hom r hr)
  have h0 : (g.stalkMap (f x)).hom ((X.presheaf.stalkCongr (.of_eq h.symm)).hom.hom r) = 0 := by
    by_contra hne
    obtain ⟨w, hw⟩ := hY.mul_inv_cancel hne
    exact hn ⟨⟨_, w, hw, by rw [mul_comm, hw]⟩, rfl⟩
  rw [Scheme.Hom.stalkMap_comp]
  change (f.stalkMap x).hom ((g.stalkMap (f x)).hom
    ((X.presheaf.stalkCongr (.of_eq h.symm)).hom.hom r)) = 0
  rw [h0, map_zero]

/-- The map `𝒪_ G ⟶ 𝒪_ G` induced by `0 : G ⟶ G` maps every element in the `mₑ` to zero -/
lemma stalkEnd_zero_apply (r : 𝒪_ G)
    (hr : r ∈ maximalIdeal (𝒪_ G)) : (stalkEnd (0 : End (mk G))).hom r = 0 :=
  Scheme.stalkCongr_hom_stalkMap_comp_apply_eq_zero G.hom ζ[G].left _ (image_unit_of_End 0)
    (isField_stalk_Spec_field _) r hr

/-- The map `(mₑ / mₑ^2) ⟶ (mₑ / mₑ^2)` induced by the `0 : G ⟶ G` is the zero map -/
lemma cotangentEnd_zero : cotangentEnd (0 : End (mk G)) = 0 := by
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.toCotangent_surjective _ v
  rw [cotangentEnd_toCotangent, LinearMap.zero_apply]
  convert (Ideal.toCotangent (maximalIdeal (𝒪_ G))).map_zero
  exact stalkEnd_zero_apply _ r.2

/-- The representation of `End (mk G)` on the Lie algebra of `G`: the dual of `cotangentEnd`. -/
def lie_algebra_repsentation' (f : End (mk G)) :
    Lie G →ₗ[κ_ G] Lie G :=
  (cotangentEnd f).dualMap












/-- Any map `f : 𝒪_ G ⟶ T` , gives a scheme map `f_# : Spec T ⟶ G`. For any `φ : G ⟶ G`,
the morphisms `f_# ≫ φ` is equal to the morphims `Spec T ⟶ G` induced by

_No sure_ I'll update this in the future.
 -/
lemma Scheme.SpecMap_comp_fromSpecStalk_comp {X : Scheme} (x : X) (φ : X ⟶ X) (hφ : φ x = x)
    {T : CommRingCat} (f : X.presheaf.stalk x ⟶ T) :
    Spec.map f ≫ X.fromSpecStalk x ≫ φ =
      Spec.map (((X.presheaf.stalkCongr (.of_eq hφ.symm)).hom ≫ φ.stalkMap x) ≫ f) ≫
        X.fromSpecStalk x := by
  have hs : φ x ⤳ x := (congrArg (· ⤳ x) hφ).mpr specializes_rfl
  calc Spec.map f ≫ X.fromSpecStalk x ≫ φ
      = Spec.map f ≫ Spec.map (φ.stalkMap x) ≫ X.fromSpecStalk (φ x) := by
        rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
    _ = Spec.map f ≫ Spec.map (φ.stalkMap x) ≫ Spec.map (X.presheaf.stalkSpecializes hs) ≫
          X.fromSpecStalk x := by
        rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    _ = _ := by
        simp only [Spec.map_comp, Category.assoc]
        rfl

/-!
### Additivity of `cotangentEnd`

To show `cotangentEnd (f + g) = cotangentEnd f + cotangentEnd g` we test against every
`φ : Dual k (m / m²)`, where `k` is the residue field at `e`. Since `e` is a `K`-rational point,
`φ` gives a local ring hom `ψ φ : 𝒪_{G, e} ⟶ k[ε]`, `a ↦ residue a + φ (a - a₀) • ε`, and hence a
morphism `Spec k[ε] ⟶ G` over `Spec K` (a tangent vector at `e`). Composing it with `f` or `g`
gives tangent vectors whose stalk maps are `stalkEnd f ≫ ψ φ` and `stalkEnd g ≫ ψ φ`. Their sum
in the group `Spec k[ε] ⟶ G` is computed through `Spec (k ⊕ (k × k))`: this ring carries both
tangent vectors at once, and the group law restricts to the identity along each axis. So the
`ε`-parts add (`CotangentEndAdd.left_add_eq_tan`). This avoids describing the stalks of `G ×_K G`.
-/

namespace CotangentEndAdd

variable (G) in
/-- The structure map `K → 𝒪_{G, e}`. -/
def κ : ↧K ⟶ 𝒪_ G :=
  (Scheme.ΓSpecIso ↧K).inv ≫ (Spec ↧K).presheaf.germ ⊤ (G.hom (e G)) trivial ≫
    G.hom.stalkMap (e G)

variable (G) in
/-- The morphism `Spec T ⟶ G` induced by a ring hom `𝒪_{G, e} ⟶ T`. -/
def tan {T : CommRingCat} (f : 𝒪_ G ⟶ T) : Spec T ⟶ G.left :=
  Spec.map f ≫ G.left.fromSpecStalk (e G)

lemma tan_comp_hom {T : CommRingCat} (f : 𝒪_ G ⟶ T) :
    tan G f ≫ G.hom = Spec.map (κ G ≫ f) := by
  rw [tan, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, κ]
  simp only [Spec.map_comp, Category.assoc]

lemma Spec_map_comp_tan {T T' : CommRingCat} (f : 𝒪_ G ⟶ T) (r : T ⟶ T') :
    Spec.map r ≫ tan G f = tan G (f ≫ r) := by
  rw [tan, tan, Spec.map_comp, Category.assoc]

lemma tan_injective {T : CommRingCat} [IsLocalRing T] {f f' : 𝒪_ G ⟶ T}
    [IsLocalHom f.hom] [IsLocalHom f'.hom] (H : tan G f = tan G f') : f = f' := by
  have := (SpecToEquivOfLocalRing G.left T).symm.injective
    (a₁ := ⟨e G, f, ‹_›⟩) (a₂ := ⟨e G, f', ‹_›⟩) H
  simpa using this

lemma exists_eq_tan {T : CommRingCat} [IsLocalRing T] (u : Spec T ⟶ G.left)
    (hu : u (closedPoint T) = e G) :
    ∃ f : 𝒪_ G ⟶ T, IsLocalHom f.hom ∧ u = tan G f := by
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing G.left T).symm.surjective u
  have hx : x = e G := by
    change (Spec.map f ≫ G.left.fromSpecStalk x) _ = _ at hu
    erw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint] at hu
    exact hu
  subst hx
  exact ⟨f, hf, rfl⟩

lemma tan_closedPoint {T : CommRingCat} [IsLocalRing T] (f : 𝒪_ G ⟶ T)
    [IsLocalHom f.hom] : tan G f (closedPoint T) = e G := by
  rw [tan]
  erw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

variable (G) in
/-- The local ring hom `𝒪_{G, e} ⟶ K` corresponding to the zero section. -/
def hζ : 𝒪_ G ⟶ ↧K := Scheme.stalkClosedPointTo ζ[G].left

instance : IsLocalHom (hζ G).hom := Scheme.isLocalHom_stalkClosedPointTo _

lemma tan_hζ : tan G (hζ G) = ζ[G].left := Scheme.Spec_stalkClosedPointTo_fromSpecStalk _

lemma κ_hζ : κ G ≫ hζ G = 𝟙 _ := by
  apply Spec.map_injective
  rw [← tan_comp_hom, tan_hζ, Spec.map_id]
  exact Over.w ζ[G]

lemma hζ_eq_zero {r : 𝒪_ G} (hr : r ∈ maximalIdeal _) :
    (hζ G).hom r = 0 := by
  by_contra h
  exact hr (isUnit_of_map_unit (hζ G).hom r (isUnit_iff_ne_zero.mpr h))

lemma sub_κ_hζ_mem (a : 𝒪_ G) :
    a - (κ G).hom ((hζ G).hom a) ∈ maximalIdeal _ := by
  intro h
  have := h.map (hζ G).hom
  rw [map_sub, ← CommRingCat.comp_apply, κ_hζ] at this
  simp at this

lemma residue_κ_hζ (a : 𝒪_ G) :
    residue _ ((κ G).hom ((hζ G).hom a)) = residue _ a :=
  Ideal.Quotient.eq.mpr (by rw [← neg_sub]; exact neg_mem (sub_κ_hζ_mem a))

instance {R M : Type*} [Field R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] : IsLocalRing (TrivSqZeroExt R M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun r ↦ by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub,
      TrivSqZeroExt.fst_one, isUnit_iff_ne_zero, ne_eq, sub_eq_zero]
    by_cases h : r.fst = 0 <;> simp [h]

section tsze

variable {M N P : Type u} [AddCommGroup M] [Module (κ_ G) M] [Module (κ_ G)ᵐᵒᵖ M]
  [IsCentralScalar (κ_ G) M] [AddCommGroup N] [Module (κ_ G) N] [Module (κ_ G)ᵐᵒᵖ N]
  [IsCentralScalar (κ_ G) N] [AddCommGroup P] [Module (κ_ G) P] [Module (κ_ G)ᵐᵒᵖ P]
  [IsCentralScalar (κ_ G) P]

variable (G M) in
/-- The square-zero extension `k ⊕ M`. -/
abbrev T : CommRingCat := CommRingCat.of (TrivSqZeroExt (κ_ G) M)

variable (G M) in
/-- `a ↦ (residue a, 0)`. -/
def resInl : 𝒪_ G ⟶ T G M :=
  CommRingCat.ofHom ((TrivSqZeroExt.inlHom (κ_ G) M).comp (residue (𝒪_ G)))

variable (G M) in
/-- The scheme `Spec (k ⊕ M)` over `Spec K`. -/
def S : Over (Spec ↧K) := Over.mk (Spec.map (κ G ≫ resInl G M))

variable (G) in
/-- The ring hom `k ⊕ M ⟶ k ⊕ N` induced by a linear map `M → N`. -/
def mapT (f : M →ₗ[κ_ G] N) : T G M ⟶ T G N := CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom

instance (f : M →ₗ[κ_ G] N) : IsLocalHom (mapT G f).hom where
  map_nonunit r hr := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] at hr ⊢
    simpa [mapT, TrivSqZeroExt.fst_map] using hr

lemma resInl_mapT (f : M →ₗ[κ_ G] N) : resInl G M ≫ mapT G f = resInl G N := by
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  exact TrivSqZeroExt.map_inl f (residue _ a)

lemma mapT_comp (f : M →ₗ[κ_ G] N) (g : N →ₗ[κ_ G] P) :
    mapT G f ≫ mapT G g = mapT G (g ∘ₗ f) := by
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
  exact (DFunLike.congr_fun (TrivSqZeroExt.map_comp_map f g) r).symm

lemma mapT_id : mapT G (LinearMap.id : M →ₗ[κ_ G] M) = 𝟙 _ := by
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
  change TrivSqZeroExt.map LinearMap.id r = r
  rw [TrivSqZeroExt.map_id]
  rfl

variable (G) in
/-- The morphism `S N ⟶ S M` induced by a linear map `M → N`. -/
def Sp (f : M →ₗ[κ_ G] N) : S G N ⟶ S G M :=
  Over.homMk (Spec.map (mapT G f)) (by
    simp only [S, Over.mk_hom, ← Spec.map_comp, Category.assoc, resInl_mapT])

@[simp]
lemma Sp_left (f : M →ₗ[κ_ G] N) : (Sp G f).left = Spec.map (mapT G f) := rfl

lemma Sp_comp (f : M →ₗ[κ_ G] N) (g : N →ₗ[κ_ G] P) : Sp G g ≫ Sp G f = Sp G (g ∘ₗ f) := by
  ext1
  change (Spec.map (mapT G g) ≫ Spec.map (mapT G f) : Spec (T G P) ⟶ Spec (T G M)) =
    Spec.map (mapT G (g ∘ₗ f))
  rw [← Spec.map_comp, mapT_comp]

lemma Sp_id : Sp G (LinearMap.id : M →ₗ[κ_ G] M) = 𝟙 _ := by
  ext1
  simp only [Sp_left, mapT_id, Spec.map_id]
  rfl

lemma zero_left : (0 : S G M ⟶ G).left = tan G (resInl G M) := by
  rw [Hom.zero_def, Over.comp_left]
  have : (CartesianMonoidalCategory.toUnit (S G M)).left = (S G M).hom := by simp
  rw [this, ← tan_hζ]
  simp only [S, Over.mk_hom, Spec_map_comp_tan]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  change TrivSqZeroExt.inl (residue _ ((κ G).hom ((hζ G).hom a))) =
    TrivSqZeroExt.inl (M := M) (residue _ a)
  rw [residue_κ_hζ]

end tsze

lemma Sp_left_closedPoint {M N : Type u} [AddCommGroup M] [Module (κ_ G) M]
    [Module (κ_ G)ᵐᵒᵖ M] [IsCentralScalar (κ_ G) M] [AddCommGroup N] [Module (κ_ G) N]
    [Module (κ_ G)ᵐᵒᵖ N] [IsCentralScalar (κ_ G) N] (f : M →ₗ[κ_ G] N) :
    (Sp G f).left (closedPoint (T G N)) = closedPoint (T G M) :=
  Spec_closedPoint (f := mapT G f)

lemma Sp_comp_left_closedPoint {M N : Type u} [AddCommGroup M] [Module (κ_ G) M]
    [Module (κ_ G)ᵐᵒᵖ M] [IsCentralScalar (κ_ G) M] [AddCommGroup N] [Module (κ_ G) N]
    [Module (κ_ G)ᵐᵒᵖ N] [IsCentralScalar (κ_ G) N] (f : M →ₗ[κ_ G] N) (u : S G M ⟶ G) :
    (Sp G f ≫ u).left (closedPoint (T G N)) = u.left (closedPoint (T G M)) := by
  rw [Over.comp_left]
  exact congrArg u.left (Sp_left_closedPoint f)

lemma Sp_comp_left {M N : Type u} [AddCommGroup M] [Module (κ_ G) M] [Module (κ_ G)ᵐᵒᵖ M]
    [IsCentralScalar (κ_ G) M] [AddCommGroup N] [Module (κ_ G) N] [Module (κ_ G)ᵐᵒᵖ N]
    [IsCentralScalar (κ_ G) N] (u : S G M ⟶ G) (φ : 𝒪_ G ⟶ T G M)
    (hu : u.left = tan G φ) (f : M →ₗ[κ_ G] N) : (Sp G f ≫ u).left = tan G (φ ≫ mapT G f) := by
  rw [Over.comp_left, hu]
  exact Spec_map_comp_tan _ _

lemma Sp_zero_comp (u : S G (κ_ G) ⟶ G) (φ : 𝒪_ G ⟶ T G (κ_ G))
    (hu : u.left = tan G φ) (hf : ∀ r, (φ.hom r).fst = residue _ r) :
    Sp G (0 : κ_ G →ₗ[κ_ G] κ_ G) ≫ u = 0 := by
  ext1
  rw [Sp_comp_left u φ hu, zero_left]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  change TrivSqZeroExt.map 0 (φ.hom a) = TrivSqZeroExt.inl (residue _ a)
  ext <;> simp [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, hf]

section k2

variable (G)

/-- The projections, inclusions and sum map relating `k` and `k × k`. -/
abbrev fst₂ : κ_ G × κ_ G →ₗ[κ_ G] κ_ G := LinearMap.fst _ _ _
@[inherit_doc fst₂] abbrev snd₂ : κ_ G × κ_ G →ₗ[κ_ G] κ_ G := LinearMap.snd _ _ _
@[inherit_doc fst₂] abbrev inl₂ : κ_ G →ₗ[κ_ G] κ_ G × κ_ G := LinearMap.inl _ _ _
@[inherit_doc fst₂] abbrev inr₂ : κ_ G →ₗ[κ_ G] κ_ G × κ_ G := LinearMap.inr _ _ _
@[inherit_doc fst₂] abbrev sum₂ : κ_ G × κ_ G →ₗ[κ_ G] κ_ G := fst₂ G + snd₂ G

end k2

/-- Adding two morphisms `Spec k[ε] ⟶ G` through `e` adds their tangent vectors. -/
lemma left_add_eq_tan (a b : S G (κ_ G) ⟶ G) (φ₁ φ₂ : 𝒪_ G ⟶ T G (κ_ G))
    [IsLocalHom φ₁.hom] [IsLocalHom φ₂.hom] (ha : a.left = tan G φ₁) (hb : b.left = tan G φ₂)
    (hf₁ : ∀ r, (φ₁.hom r).fst = residue _ r) (hf₂ : ∀ r, (φ₂.hom r).fst = residue _ r) :
    ∃ φ : 𝒪_ G ⟶ T G (κ_ G), IsLocalHom φ.hom ∧ (a + b).left = tan G φ ∧
      ∀ r, (φ.hom r).snd = (φ₁.hom r).snd + (φ₂.hom r).snd := by
  let c : S G (κ_ G × κ_ G) ⟶ G := Sp G (inl₂ G) ≫ a + Sp G (inr₂ G) ≫ b
  have e₁ : fst₂ G ∘ₗ inl₂ G = LinearMap.id := LinearMap.ext fun _ ↦ rfl
  have e₂ : fst₂ G ∘ₗ inr₂ G = 0 := LinearMap.ext fun _ ↦ rfl
  have e₃ : snd₂ G ∘ₗ inl₂ G = 0 := LinearMap.ext fun _ ↦ rfl
  have e₄ : snd₂ G ∘ₗ inr₂ G = LinearMap.id := LinearMap.ext fun _ ↦ rfl
  have e₅ : sum₂ G ∘ₗ inl₂ G = LinearMap.id := LinearMap.ext fun _ ↦ by simp
  have e₆ : sum₂ G ∘ₗ inr₂ G = LinearMap.id := LinearMap.ext fun _ ↦ by simp
  have hc₁ : Sp G (fst₂ G) ≫ c = a := by
    simp only [c, comp_add, ← Category.assoc, Sp_comp, e₁, e₂, Sp_id, Category.id_comp,
      Sp_zero_comp b φ₂ hb hf₂, _root_.add_zero]
  have hc₂ : Sp G (snd₂ G) ≫ c = b := by
    simp only [c, comp_add, ← Category.assoc, Sp_comp, e₃, e₄, Sp_id, Category.id_comp,
      Sp_zero_comp a φ₁ ha hf₁, _root_.zero_add]
  have hc₃ : Sp G (sum₂ G) ≫ c = a + b := by
    simp only [c, comp_add, ← Category.assoc, Sp_comp, e₅, e₆, Sp_id, Category.id_comp]
  have hpt : c.left (closedPoint (T G (κ_ G × κ_ G))) = e G :=
    (Sp_comp_left_closedPoint (fst₂ G) c).symm.trans (by rw [hc₁, ha]; exact tan_closedPoint φ₁)
  obtain ⟨φc, hloc, hceq⟩ := exists_eq_tan c.left hpt
  have : IsLocalHom (mapT G (fst₂ G)).hom := inferInstance
  have : IsLocalHom (φc ≫ mapT G (fst₂ G)).hom :=
    @CommRingCat.isLocalHom_comp _ _ _ φc _ this hloc
  have : IsLocalHom (φc ≫ mapT G (snd₂ G)).hom :=
    @CommRingCat.isLocalHom_comp _ _ _ φc _ inferInstance hloc
  have f₁ : φc ≫ mapT G (fst₂ G) = φ₁ :=
    tan_injective (by rw [← Sp_comp_left c φc hceq, hc₁, ha])
  have f₂ : φc ≫ mapT G (snd₂ G) = φ₂ :=
    tan_injective (by rw [← Sp_comp_left c φc hceq, hc₂, hb])
  refine ⟨φc ≫ mapT G (sum₂ G),
    @CommRingCat.isLocalHom_comp _ _ _ φc _ inferInstance hloc, ?_, fun r ↦ ?_⟩
  · rw [← hc₃, Sp_comp_left c φc hceq]
  · rw [← f₁, ← f₂]
    change (TrivSqZeroExt.map _ (φc.hom r)).snd =
      (TrivSqZeroExt.map _ (φc.hom r)).snd + (TrivSqZeroExt.map _ (φc.hom r)).snd
    simp [TrivSqZeroExt.snd_map]

lemma tan_comp_end {T : CommRingCat} (φ : 𝒪_ G ⟶ T) (f : End (mk G)) :
    tan G φ ≫ (f.asHom.hom.hom : G ⟶ G).left = tan G (stalkEnd f ≫ φ) := by
  rw [tan, tan, stalkEnd, Category.assoc]
  exact Scheme.SpecMap_comp_fromSpecStalk_comp _ _ (image_unit_of_End f) φ

section ψ

variable (φ : Module.Dual (κ_ G) (CotangentSpace (𝒪_ G)))

variable (G) in
/-- The derivation `𝒪_{G, e} → k` attached to `φ`. -/
def der (a : 𝒪_ G) : κ_ G :=
  φ (Ideal.toCotangent _ ⟨_, sub_κ_hζ_mem a⟩)

lemma der_of_mem {r : 𝒪_ G} (hr : r ∈ maximalIdeal _) :
    der G φ r = φ (Ideal.toCotangent _ ⟨r, hr⟩) := by
  simp only [der, hζ_eq_zero hr, map_zero, sub_zero]

lemma der_κ (c : K) : der G φ ((κ G).hom c) = 0 := by
  have : (κ G).hom ((hζ G).hom ((κ G).hom c)) = (κ G).hom c := by
    rw [← CommRingCat.comp_apply (κ G) (hζ G), κ_hζ, CommRingCat.id_apply]
  simp only [der, this, sub_self]
  convert φ.map_zero
  convert (Ideal.toCotangent _).map_zero

lemma der_add (a b : 𝒪_ G) :
    der G φ (a + b) = der G φ a + der G φ b := by
  simp only [der]
  rw [← map_add, ← map_add]
  congr 2
  ext
  simp only [map_add, Submodule.coe_add]
  ring

lemma der_mul (a b : 𝒪_ G) :
    der G φ (a * b) = residue _ a * der G φ b + der G φ a * residue _ b := by
  have : Ideal.toCotangent (maximalIdeal _) ⟨_, sub_κ_hζ_mem (a * b)⟩ =
      residue _ a • Ideal.toCotangent _ ⟨_, sub_κ_hζ_mem b⟩ +
        residue _ b • Ideal.toCotangent _ ⟨_, sub_κ_hζ_mem a⟩ := by
    rw [← ResidueField.algebraMap_eq, algebraMap_smul, algebraMap_smul, ← map_smul, ← map_smul,
      ← map_add, Ideal.toCotangent_eq, pow_two]
    convert neg_mem (Ideal.mul_mem_mul (sub_κ_hζ_mem a) (sub_κ_hζ_mem b)) using 1
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
    ring
  rw [der, this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, der, der, mul_comm (φ _)]

variable (G) in
/-- The ring hom `𝒪_{G, e} →+* k[ε]`, `a ↦ residue a + der φ a • ε`. -/
def ψRingHom : 𝒪_ G →+* TrivSqZeroExt (κ_ G) (κ_ G) where
  toFun a := TrivSqZeroExt.inl (residue (𝒪_ G) a) +
    TrivSqZeroExt.inr (der G φ a)
  map_one' := by
    have : der G φ 1 = 0 := by simpa only [map_one] using der_κ φ 1
    ext <;> simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.snd_one, map_one, _root_.add_zero, this]
  map_mul' a b := by
    ext <;> simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.snd_mul, map_mul, _root_.add_zero, _root_.zero_add, smul_eq_mul, op_smul_eq_mul,
      der_mul]
  map_zero' := by
    have : der G φ 0 = 0 := by simpa only [map_zero] using der_κ φ 0
    ext <;> simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_zero,
      TrivSqZeroExt.snd_zero, map_zero, _root_.add_zero, this]
  map_add' a b := by
    ext <;> simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, map_add, _root_.add_zero,
      _root_.zero_add, der_add]

variable (G) in
/-- The local ring hom `𝒪_{G, e} ⟶ k[ε]`, `a ↦ residue a + der φ a • ε`. -/
def ψ : 𝒪_ G ⟶ T G (κ_ G) := CommRingCat.ofHom (ψRingHom G φ)

@[simp]
lemma ψ_fst (a : 𝒪_ G) : ((ψ G φ).hom a).fst = residue _ a := by
  change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : TrivSqZeroExt (κ_ G) (κ_ G)).fst = _
  rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, _root_.add_zero]

@[simp]
lemma ψ_snd (a : 𝒪_ G) : ((ψ G φ).hom a).snd = der G φ a := by
  change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : TrivSqZeroExt (κ_ G) (κ_ G)).snd = _
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add]

instance : IsLocalHom (ψ G φ).hom where
  map_nonunit a ha := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, ψ_fst] at ha
    exact isUnit_of_map_unit (residue _) a ha

lemma κ_ψ : κ G ≫ ψ G φ = κ G ≫ resInl G (κ_ G) := by
  refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
  change (ψ G φ).hom ((κ G).hom c) = TrivSqZeroExt.inl (residue _ ((κ G).hom c))
  ext
  · exact ψ_fst φ _
  · rw [ψ_snd]
    exact der_κ φ c

variable (G) in
/-- The tangent vector `Spec k[ε] ⟶ G` at `e` attached to `φ`. -/
def tanVec : S G (κ_ G) ⟶ G :=
  Over.homMk (tan G (ψ G φ)) ((tan_comp_hom _).trans (by rw [κ_ψ]; rfl))

end ψ

end CotangentEndAdd

open CotangentEndAdd in
/-- The map induced on cotangent spaces is additive in the endomorphism. -/
lemma cotangentEnd_add [IsCommAddMonObj G] (f g : End (mk G)) :
    cotangentEnd (f + g) = cotangentEnd f + cotangentEnd g := by
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.toCotangent_surjective _ v
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (κ_ G)]
  intro φ
  rw [map_sub, sub_eq_zero, LinearMap.add_apply, map_add]
  have key (u : End (AddGrp.mk G)) :
      (tanVec G φ ≫ u.asHom.hom.hom).left = tan G (stalkEnd u ≫ ψ G φ) :=
    tan_comp_end _ u
  have hf (u : End (AddGrp.mk G)) (r : 𝒪_ G) :
      ((stalkEnd u ≫ ψ G φ).hom r).fst = residue (𝒪_ G) r := by
    rw [CommRingCat.comp_apply, ψ_fst, residue_stalkEnd]
  have hl (u : End (AddGrp.mk G)) : IsLocalHom (stalkEnd u ≫ ψ G φ).hom :=
    @CommRingCat.isLocalHom_comp _ _ _ (stalkEnd u) (ψ G φ) inferInstance inferInstance
  have := hl f
  have := hl g
  have := hl (f + g)
  obtain ⟨f', hloc, hf', hsnd⟩ :=
    left_add_eq_tan _ _ _ _ (key f) (key g) (hf f) (hf g)
  have : f' = stalkEnd (f + g) ≫ ψ G φ := by
    refine tan_injective (hf'.symm.trans ?_)
    rw [← key, ← comp_add]
    rfl
  subst this
  have hm (u : End (AddGrp.mk G)) : (stalkEnd u).hom r.1 ∈ maximalIdeal _ :=
    map_nonunit (stalkEnd u).hom _ r.2
  have := hsnd r.1
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply, ψ_snd, ψ_snd, ψ_snd,
    der_of_mem φ (hm f), der_of_mem φ (hm g), der_of_mem φ (hm (f + g))] at this
  rw [cotangentEnd_toCotangent, cotangentEnd_toCotangent, cotangentEnd_toCotangent]
  exact this

/-- The representation of `End (mk G)` on the Lie algebra of `G`, as a ring homomorphism. -/
def lie_algebra_represenation [IsCommAddMonObj G] :
    End (mk G) →+* (Lie G →ₗ[κ_ G] Lie G) where
  toFun f := lie_algebra_repsentation' f
  map_one' := by
    simp only [lie_algebra_repsentation', cotangentEnd_one, LinearMap.dualMap_id]
    rfl
  map_mul' f g := by
    simp only [lie_algebra_repsentation', cotangentEnd_mul, ← LinearMap.dualMap_comp_dualMap]
    rfl
  map_zero' := by
    ext
    simp [lie_algebra_repsentation', cotangentEnd_zero, LinearMap.dualMap_apply]
  map_add' f g := by
    ext
    simp [lie_algebra_repsentation', cotangentEnd_add, LinearMap.dualMap_apply]
