/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import CMAbelianVarieties.ForMathlib.Endomorphism

/-!
## Lie algebra of a group object

In this file we shall define the Lie algebra of a group scheme over a field
`K` as a vector space over `K`.

_This needs to be rewritten at some point_
This docuent has a bunch of results I should consider putting in the catalogue
section

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

/-- An endomorphism `f` of `G` induces the identity on the residue field `κ_{G,e}` at the identity
point `e G`. -/
lemma residueFieldCongr_residueFieldMap (f : End (mk G)) :
    (G.left.residueFieldCongr (image_unit_of_End f).symm).hom ≫
      (f.asHom.hom.hom.left).residueFieldMap (e G) = 𝟙 _ :=
  Scheme.residueFieldCongr_residueFieldMap_of_comp_eq ζ[G].left f.asHom.hom.hom.left
    (congrArg CommaMorphism.left (IsAddMonHom.zero_hom f.asHom.hom.hom)) (closedPoint K)

/-- The map `𝒪_{G,e} ⟶ 𝒪_{G,e} ⟶ κ_{G,e}`, where the first is induced by `f`, is the
same as the quotient morphism `𝒪_{G,e} ⟶ κ_{G,e}` -/
lemma stalkEnd_residue (f : End (mk G)) :
    stalkEnd f ≫ G.left.residue (e G) = G.left.residue (e G) := by
  rw [stalkEnd, Category.assoc, ← Scheme.residue_residueFieldMap, ← Category.assoc,
    ← Scheme.residue_residueFieldCongr _ (image_unit_of_End f).symm, Category.assoc,
    residueFieldCongr_residueFieldMap, Category.comp_id]

/-- For `a : 𝒪_{G,e}`, the image of `a` in `κ_{G,e}` is the same as the image
of `a` along the composition `𝒪_{G,e} ⟶ 𝒪_{G,e} ⟶ κ_{G,e}`, where the first is induced
by `f`. -/
lemma residue_stalkEnd (f : End (mk G)) (a : 𝒪_ G) :
    residue _ ((stalkEnd f).hom a) = residue _ a :=
  congr($(stalkEnd_residue f).hom a)

/-- `mₑ ⊆ f⁻¹(mₑ)` along the map `f`. -/
lemma maximalIdeal_le_comap_stalkEnd (f : End (mk G)) :
    maximalIdeal (𝒪_ G) ≤
      (maximalIdeal _).comap (stalkEnd f).hom.toIntAlgHom :=
  fun r hr ↦ map_nonunit (stalkEnd f).hom r hr

/- Hey claude, when you see this comment remind me the following: In the theorem
`Ideal.mapCotangent`, the docstring uses `I` and `J`, while the theorem uses `I₁` and
`I₂`. I should change that some day. -/
/-- The endomorphism of the cotangent space of `G` at `e G` induced by an endomorphism
of `G`. That is, `(mₑ / mₑ^2) ⟶[κ_{G,e}] (mₑ / mₑ^2)` -/
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

/-- `𝟙 : X ⟶ X` induces the morphism `id : 𝒪_{G,e} ⟶ 𝒪_{G,e}` -/
lemma stalkEnd_one : stalkEnd (1 : End (mk G)) = 𝟙 _ := by
  erw [stalkEnd, Scheme.Hom.stalkMap_id]
  exact (Category.comp_id _).trans (TopCat.Presheaf.stalkSpecializes_refl _ _)

/-- `f * g : G ⟶ G` induces the composition `𝒪_{G,e} ⟶ 𝒪_{G,e} ⟶ 𝒪_{G,e}` where the first
is induced by `f` and the second by `g` -/
lemma stalkEnd_mul (f g : End (mk G)) : stalkEnd (f * g) = stalkEnd f ≫ stalkEnd g :=
  Scheme.Hom.fixedStalkMap_comp _ _ _ (image_unit_of_End f) (image_unit_of_End g)

/-- For `x : Spec K`, the local ring `𝒪ₓ` is a field -/
lemma isField_stalk_Spec_field (x : Spec ↧K) : IsField ((Spec ↧K).presheaf.stalk x) := by
  refine isField_stalk_of_closure_mem_irreducibleComponents _ x ?_
  rw [Set.eq_univ_of_forall fun y ↦ subset_closure (Subsingleton.elim y x ▸ rfl)]
  simp [irreducibleComponents_eq_singleton]

/-- For `r : mₑ`, the image of `r` along the map `(mₑ / mₑ^2) ⟶[κ_{G,e}] (mₑ / mₑ^2)`
induced by `f`, comes from the lift `𝒪_{G,e} ⟶ 𝒪_{G,e}` which is induced by `f` -/
lemma cotangentEnd_toCotangent (f : End (mk G)) (r : maximalIdeal (𝒪_ G)) :
    cotangentEnd f (Ideal.toCotangent _ r) =
      Ideal.toCotangent _ ⟨(stalkEnd f).hom r, map_nonunit (stalkEnd f).hom _ r.2⟩ :=
  rfl

/-- The morphism `(mₑ / mₑ^2) ⟶[κ_{G,e}] (mₑ / mₑ^2)` induced by `id`, is
the identity morphism -/
lemma cotangentEnd_one : cotangentEnd (1 : End (mk G)) = LinearMap.id := by
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.toCotangent_surjective _ v
  rw [cotangentEnd_toCotangent, LinearMap.id_apply]
  exact congrArg _ (Subtype.ext (by simp [stalkEnd_one]))

/-- `f * g : G ⟶ G` induces the composition `(mₑ / mₑ^2) ⟶ (mₑ / mₑ^2) ⟶ (mₑ / mₑ^2)` of
`κ_{G,e}`-linear maps, where the first is induced by `f` and the second by `g` -/
lemma cotangentEnd_mul (f g : End (mk G)) :
    cotangentEnd (f * g) = cotangentEnd g ∘ₗ cotangentEnd f := by
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.toCotangent_surjective _ v
  simp only [LinearMap.comp_apply, cotangentEnd_toCotangent]
  exact congrArg _ (Subtype.ext (by simp [stalkEnd_mul]))

/-- If `r : mₑ`, then under the map `𝒪_{G,e} ⟶ 𝒪_{G,e}` induced by the composition `toUnit ≫ ζ`,
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

/-- The map `𝒪_{G,e} ⟶ 𝒪_{G,e}` induced by `0 : G ⟶ G` maps every element in the `mₑ` to zero -/
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

/-- Any map `f : 𝒪_ G ⟶ T` , gives a scheme map `f_# : Spec T ⟶ Spec 𝒪_ G ⟶ G`. For any
`φ : G ⟶ G`, the image of `f_#` under the map `φ(T) : G(T) ⟶ G(T)`is `g_#` for the map
`g : 𝒪_ G ≅ 𝒪_ {G, φ(e)} ⟶ 𝒪_ {G, e} ⟶ T`/

P.S., I know that `𝒪_ {G, e} = 𝒪_ G`, but I used the other notation above because I wanted
to show that the morphisms `𝒪_ {G, φ(e)} ⟶ 𝒪_ {G, e}` comes from `φ`. -/
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

/- `cotangentEnd f` is the map `(mₑ / mₑ^2) ⟶[κ_{G,e}] (mₑ / mₑ^2)` generated by `f` -/
namespace CotangentEndAdd

/-- The structure map `K → 𝒪_{G,e}`. -/
def π (G : Over (Spec ↧K)) [AddGrpObj G] : ↧K ⟶ 𝒪_ G :=
  (Scheme.ΓSpecIso ↧K).inv ≫ (Spec ↧K).presheaf.germ ⊤ (G.hom (e G)) trivial ≫
    G.hom.stalkMap (e G)

/-- The morphism `Spec T ⟶ G` induced by a ring hom `𝒪_{G,e} ⟶ T`. -/
def tan {T : CommRingCat} (f : 𝒪_ G ⟶ T) : Spec T ⟶ G.left :=
  Spec.map f ≫ G.left.fromSpecStalk (e G)

/-- The composition `Spec T ⟶ G ⟶ Spec K`, where the first one is induced by a map
`𝒪_{G,e} ⟶ T`, is the spec map induced by the composition `K ⟶ 𝒪_{G,e} ⟶ T` -/
lemma tan_comp_hom {T : CommRingCat} (f : 𝒪_ G ⟶ T) :
    tan f ≫ G.hom = Spec.map (π G ≫ f) := by
  rw [tan, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, π]
  simp only [Spec.map_comp, Category.assoc]

/-- If `Spec T ⟶ G` is induced by a ring hom `𝒪_{G,e} ⟶ T`, and we are given
a ring home `T ⟶ T'`, the obvious composition `Spec T' ⟶ Spec T ⟶ G` is
induced by the obvious composition `𝒪_{G,e} ⟶ T ⟶ T'`. -/
lemma Spec_map_comp_tan {T T' : CommRingCat} (f : 𝒪_ G ⟶ T) (φ : T ⟶ T') :
    Spec.map φ ≫ tan f = tan (f ≫ φ) := by
  rw [tan, tan, Spec.map_comp, Category.assoc]

/-- If two morphisms `Spec T ⟶ G` induced by two different `f g : 𝒪_{G,e} ⟶ T`
are equal, then `f = g`. -/
lemma tan_injective {T : CommRingCat} {f f' : 𝒪_ G ⟶ T} (H : tan f = tan f') :
    f = f' :=
  Spec.map_injective ((cancel_mono (G.left.fromSpecStalk (e G))).mp H)

/-- For a local ring `T`, and morphism `Spec T ⟶ G`, if the closed point goes
to `e`, then the morphisms is induced by a morphisms `𝒪_{G,e} ⟶ T` -/
lemma exists_eq_tan {T : CommRingCat} [IsLocalRing T] (g : Spec T ⟶ G.left)
    (hg : g (closedPoint T) = e G) :
    ∃ f : 𝒪_ G ⟶ T, IsLocalHom f.hom ∧ g = tan f := by
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing G.left T).symm.surjective g
  have hx : x = e G := by
    change (Spec.map f ≫ G.left.fromSpecStalk x) _ = _ at hg
    erw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint] at hg
    exact hg
  subst hx
  exact ⟨f, hf, rfl⟩

/-- For a local ring `T`, and a local morphism `𝒪_{G,e} ⟶ T`, the induced morphisms
`Spec T ⟶ G` maps the closed point to `e`. -/
lemma tan_closedPoint {T : CommRingCat} [IsLocalRing T] (f : 𝒪_ G ⟶ T)
    [IsLocalHom f.hom] : tan f (closedPoint T) = e G := by
  rw [tan]
  erw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- The local ring hom `𝒪_{G,e} ⟶ K` inducing the zero section (although it is
not defined precisely like that) -/
def hζ (G : Over (Spec ↧K)) [AddGrpObj G] : 𝒪_ G ⟶ ↧K := Scheme.stalkClosedPointTo ζ[G].left

/-- The morphisms `hζ` is local -/
instance : IsLocalHom (hζ G).hom := Scheme.isLocalHom_stalkClosedPointTo _

/-- the morphisms `Spec K ⟶ G` induced by `hζ` is infact `ζ` -/
lemma tan_hζ : tan (hζ G) = ζ[G].left := Scheme.Spec_stalkClosedPointTo_fromSpecStalk _

/-- The compositon `Spec K ⟶ 𝒪_{G,e} ⟶ Spec K`, where the former is structure
morphism and the latter is the one that induces `ζ` is identity. -/
lemma π_hζ : π G ≫ hζ G = 𝟙 _ := by
  apply Spec.map_injective
  rw [← tan_comp_hom, tan_hζ, Spec.map_id]
  exact Over.w ζ[G]

/-- the map `𝒪_{G,e} ⟶ K` which induces `ζ` maps elements of the maximal ideal
to zero. -/
lemma hζ_eq_zero {r : 𝒪_ G} (hr : r ∈ maximalIdeal _) :
    (hζ G).hom r = 0 := by
  by_contra h
  exact hr (isUnit_of_map_unit (hζ G).hom r (isUnit_iff_ne_zero.mpr h))

/-- If we consider the composition `comp: 𝒪_{G,e} ⟶ K ⟶ 𝒪_{G,e}`, where the former
is induces `ζ`, and the latter the strucutre map, then for any `a : 𝒪_{G,e}`,
`a - comp(a) ∈ mₑ` -/
lemma sub_π_hζ_mem (a : 𝒪_ G) :
    a - (π G).hom ((hζ G).hom a) ∈ maximalIdeal _ := by
  intro h
  have := h.map (hζ G).hom
  rw [map_sub, ← CommRingCat.comp_apply, π_hζ] at this
  simp at this

/-- If we consider the composition `comp: 𝒪_{G,e} ⟶ K ⟶ 𝒪_{G,e} ⟶ κ_{G,e}`, where
the first morphism induces `ζ`, and the second the strucutre map, then for any
`a : 𝒪_{G,e}`, the image in `κ_{G,e}` is equal to the `comp(a)` -/
lemma residue_π_hζ (a : 𝒪_ G) :
    residue _ ((π G).hom ((hζ G).hom a)) = residue _ a :=
  Ideal.Quotient.eq.mpr (by rw [← neg_sub]; exact neg_mem (sub_π_hζ_mem a))

/-
Below, and in later lemmas, `TrivSqZeroExt E M` is the ring `E ⊕ M` with multiplication
`(a, m) * (b, n) = (a * b, a • n + b • m)`.

Here `Eᵐᵒᵖ` is the opposite ring of `E`, with
multiplication `a * b := b * a`, so a `Module Eᵐᵒᵖ M` is a right `E`-module.

Mathlib defines `TrivSqZeroExt` for non-commutative rings too, so it needs this right action
(and `IsCentralScalar E M`, saying both actions agree) even when `E` is commutative.
Mathlib's convention for a commutative ring is to assume these as hypotheses, rather than
creating the right action automatically.
-/


/-- `TrivSqZeroExt E M` is a local ring. This implies `RGM` below is local. -/
instance {E M : Type*} [Field E] [AddCommGroup M] [Module E M] [Module Eᵐᵒᵖ M]
    [IsCentralScalar E M] : IsLocalRing (TrivSqZeroExt E M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun r ↦ by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub,
      TrivSqZeroExt.fst_one, isUnit_iff_ne_zero, ne_eq, sub_eq_zero]
    by_cases h : r.fst = 0 <;> simp [h]

section TrivSqZeroExt

/- For a `κ_{G,e}`-vector space `M`, we define the scheme `SGM := Spec (κ_{G,e} ⊕ M)` over
`Spec K`, and the morphisms `S G N ⟶ S G M` induced by linear maps `M → N`. For `M = κ_{G,e}`
this is `Spec κ_{G,e}[ε]`, whose morphisms to `G` are tangent vectors. Later,
`M = κ_{G,e} × κ_{G,e}` is used to add two tangent vectors. -/

variable {M N P : Type u} [AddCommGroup M] [Module (κ_ G) M] [Module (κ_ G)ᵐᵒᵖ M]
  [IsCentralScalar (κ_ G) M] [AddCommGroup N] [Module (κ_ G) N] [Module (κ_ G)ᵐᵒᵖ N]
  [IsCentralScalar (κ_ G) N] [AddCommGroup P] [Module (κ_ G) P] [Module (κ_ G)ᵐᵒᵖ P]
  [IsCentralScalar (κ_ G) P]

variable (G M) in
/-- The square-zero extension `RGM := κ_{G,e} ⊕ M`. -/
abbrev R : CommRingCat := CommRingCat.of (TrivSqZeroExt (κ_ G) M)

variable (G M) in
/-- `resInl` is the composition `𝒪_{G,e} ⟶ κ_{G,e} ⟶ κ_{G,e} ⊕ M = RGM` given by `a ↦ ([a], 0)`,
where `[a]` is the image of `a` in `κ_{G,e}`. -/
def resInl : 𝒪_ G ⟶ R G M :=
  CommRingCat.ofHom ((TrivSqZeroExt.inlHom (κ_ G) M).comp (residue (𝒪_ G)))

variable (G M) in
/-- The scheme `SGM := Spec (κ_{G,e} ⊕ M)` over `Spec K`. The structure map is defined as the
opposite of the map `K ⟶ 𝒪_{G,e} ⟶ κ_{G,e} ⊕ M = RGM`, where the latter is `resInl`. -/
def S : Over (Spec ↧K) := Over.mk (Spec.map (π G ≫ resInl G M))

/-- `mapR f` is the ring hom `κ_{G,e} ⊕ M ⟶ κ_{G,e} ⊕ N` induced by a linear map `f : M → N`. -/
def mapR (f : M →ₗ[κ_ G] N) : R G M ⟶ R G N := CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom

/-- The map `κ_{G,e} ⊕ M ⟶ κ_{G,e} ⊕ N` is local -/
instance {f : M →ₗ[κ_ G] N} : IsLocalHom (mapR f).hom where
  map_nonunit r hr := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] at hr ⊢
    simpa [mapR, TrivSqZeroExt.fst_map] using hr

/-- the composition `𝒪_{G,e} ⟶ κ_{G,e} ⊕ M ⟶ κ_{G,e} ⊕ N` is equal to
`𝒪_{G,e} ⟶ κ_{G,e} ⊕ N`. -/
lemma resInl_mapR (f : M →ₗ[κ_ G] N) : resInl G M ≫ mapR f = resInl G N := by
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  exact TrivSqZeroExt.map_inl f (residue _ a)

/-- The composition `κ_{G,e} ⊕ M ⟶ κ_{G,e} ⊕ N ⟶ κ_{G,e} ⊕ P` we get from
the composition `M →ₗ N →ₗ P` is equal to `κ_{G,e} ⊕ M ⟶ κ_{G,e} ⊕ P`, which we
get from the composition of the linear maps. -/
lemma mapR_comp (f : M →ₗ[κ_ G] N) (g : N →ₗ[κ_ G] P) :
    mapR f ≫ mapR g = mapR (g ∘ₗ f) := by
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
  exact (DFunLike.congr_fun (TrivSqZeroExt.map_comp_map f g) r).symm

/-- The map `κ_{G,e} ⊕ M ⟶ κ_{G,e} ⊕ M` which we get from the identity map
`M →ₗ M` is the identity map. -/
lemma mapR_id : mapR (LinearMap.id : M →ₗ[κ_ G] M) = 𝟙 _ := by
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
  change TrivSqZeroExt.map LinearMap.id r = r
  rw [TrivSqZeroExt.map_id]
  rfl

/-- `Sp f` is the morphism `SGN ⟶ SGM` induced by a linear map `f : M →ₗ N`. This is
a morphism defined over `Spec K`. -/
def Sp (f : M →ₗ[κ_ G] N) : S G N ⟶ S G M :=
  Over.homMk (Spec.map (mapR f)) (by
    simp only [S, Over.mk_hom, ← Spec.map_comp, Category.assoc, resInl_mapR])

/-- The underlying affine scheme map `SGN ⟶ SGM` (not over `K`), is just the opposite
of the morphisms `RGM ⟶ RGN`. -/
@[simp]
lemma Sp_left (f : M →ₗ[κ_ G] N) : (Sp f).left = Spec.map (mapR f) := rfl

/-- The composition `SGP ⟶ SGN ⟶ SGM` is equal to `SGP ⟶ SGM` coming from the respective
ring maps -/
lemma Sp_comp (f : M →ₗ[κ_ G] N) (g : N →ₗ[κ_ G] P) : Sp g ≫ Sp f = Sp (g ∘ₗ f) := by
  ext1
  change (Spec.map (mapR g) ≫ Spec.map (mapR f) : Spec (R G P) ⟶ Spec (R G M)) =
    Spec.map (mapR (g ∘ₗ f))
  rw [← Spec.map_comp, mapR_comp]

/-- the morphism `SGM ⟶ SGM` that we get from identity is identity. -/
lemma Sp_id : Sp (LinearMap.id : M →ₗ[κ_ G] M) = 𝟙 _ := by
  ext1
  simp only [Sp_left, mapR_id, Spec.map_id]
  rfl

/-- the morphism `0 : SGM = Spec RGN ⟶ G` is the same as the morphism induced by the
composition `𝒪_{G,e} ⟶ κ_{G,e} ⟶ κ_{G,e} ⊕ M = RGM`, given by `a ↦ ([a], 0)`. -/
lemma zero_left : (0 : S G M ⟶ G).left = tan (resInl G M) := by
  rw [Hom.zero_def, Over.comp_left]
  have : (CartesianMonoidalCategory.toUnit (S G M)).left = (S G M).hom := by simp
  rw [this, ← tan_hζ]
  simp only [S, Over.mk_hom, Spec_map_comp_tan]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  change TrivSqZeroExt.inl (residue _ ((π G).hom ((hζ G).hom a))) =
    TrivSqZeroExt.inl (M := M) (residue _ a)
  rw [residue_π_hζ]

end TrivSqZeroExt

/-- For the scheme map `SGN ⟶ SGM` induced by `M →ₗ N`, the closed point maps to the closed
point -/
lemma Sp_left_closedPoint {M N : Type u} [AddCommGroup M] [Module (κ_ G) M]
    [Module (κ_ G)ᵐᵒᵖ M] [IsCentralScalar (κ_ G) M] [AddCommGroup N] [Module (κ_ G) N]
    [Module (κ_ G)ᵐᵒᵖ N] [IsCentralScalar (κ_ G) N] (f : M →ₗ[κ_ G] N) :
    (Sp f).left (closedPoint (R G N)) = closedPoint (R G M) :=
  Spec_closedPoint (f := mapR f)

/-- The image of the closed point along the composition `SGN ⟶ SGM ⟶ G` is the same as the
image of the closed point along the map `SGM ⟶ G`. -/
lemma Sp_comp_left_closedPoint {M N : Type u} [AddCommGroup M] [Module (κ_ G) M]
    [Module (κ_ G)ᵐᵒᵖ M] [IsCentralScalar (κ_ G) M] [AddCommGroup N] [Module (κ_ G) N]
    [Module (κ_ G)ᵐᵒᵖ N] [IsCentralScalar (κ_ G) N] (f : M →ₗ[κ_ G] N) (φ : S G M ⟶ G) :
    (Sp f ≫ φ).left (closedPoint (R G N)) = φ.left (closedPoint (R G M)) := by
  rw [Over.comp_left]
  exact congrArg φ.left (Sp_left_closedPoint f)

/-- If a morphisms `φ : SGM = Spec RGM ⟶ G` is induced by `𝒪_{G,e} ⟶ RGM`, then given a linear
map `f : M →ₗ N` which then gives us a ring hom `RGM ⟶ RGM`, the map of scheme give by the
composition  `𝒪_{G,e} ⟶ RGM ⟶ RGN` is the same as the morphism `SGN ⟶ SGM ⟶ G`. -/
lemma Sp_comp_left {M N : Type u} [AddCommGroup M] [Module (κ_ G) M] [Module (κ_ G)ᵐᵒᵖ M]
    [IsCentralScalar (κ_ G) M] [AddCommGroup N] [Module (κ_ G) N] [Module (κ_ G)ᵐᵒᵖ N]
    [IsCentralScalar (κ_ G) N] {φ : S G M ⟶ G} {g : 𝒪_ G ⟶ R G M}
    (h : φ.left = tan g) (f : M →ₗ[κ_ G] N) : (Sp f ≫ φ).left = tan (g ≫ mapR f) := by
  rw [Over.comp_left, h]
  exact Spec_map_comp_tan _ _

/-- If a morphism `f : Spec κ_{G,e}[ε] ⟶ G` is induced by `φ : 𝒪_{G,e} ⟶ κ_{G,e}[ε]`, whose
first component is the quotient map `𝒪_{G,e} ⟶ κ_{G,e}`, then the composition
`Spec κ_{G,e}[ε] ⟶ Spec κ_{G,e}[ε] ⟶ G`, where the first map is induced by the zero map
`κ_{G,e} →ₗ κ_{G,e}`, is the zero morphism. -/
lemma Sp_zero_comp {f : S G (κ_ G) ⟶ G} {φ : 𝒪_ G ⟶ R G (κ_ G)}
    (h : f.left = tan φ) (hφ : ∀ r, (φ.hom r).fst = residue _ r) :
    Sp (0 : κ_ G →ₗ[κ_ G] κ_ G) ≫ f = 0 := by
  ext1
  rw [Sp_comp_left h, zero_left]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  change TrivSqZeroExt.map 0 (φ.hom a) = TrivSqZeroExt.inl (residue _ a)
  ext <;> simp [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, hφ]

section κκ

variable (G)

/-- The projections, inclusions and sum map relating `κ_{G,e}` and `κ_{G,e} × κ_{G,e}`. -/
abbrev fst₂ : κ_ G × κ_ G →ₗ[κ_ G] κ_ G := LinearMap.fst _ _ _
@[inherit_doc fst₂] abbrev snd₂ : κ_ G × κ_ G →ₗ[κ_ G] κ_ G := LinearMap.snd _ _ _
@[inherit_doc fst₂] abbrev inl₂ : κ_ G →ₗ[κ_ G] κ_ G × κ_ G := LinearMap.inl _ _ _
@[inherit_doc fst₂] abbrev inr₂ : κ_ G →ₗ[κ_ G] κ_ G × κ_ G := LinearMap.inr _ _ _
@[inherit_doc fst₂] abbrev sum₂ : κ_ G × κ_ G →ₗ[κ_ G] κ_ G := fst₂ G + snd₂ G

end κκ

/-- If two morphisms `f g : Spec κ_{G,e}[ε] ⟶ G` are induced by local ring homs
`φ₁ φ₂ : 𝒪_{G,e} ⟶ κ_{G,e}[ε]`, whose first components are the quotient map
`𝒪_{G,e} ⟶ κ_{G,e}`, then `f + g` is induced by a local ring hom `φ : 𝒪_{G,e} ⟶ κ_{G,e}[ε]`,
whose `ε`-component is the sum of the `ε`-components of `φ₁` and `φ₂`. -/
lemma left_add_eq_tan {f g : S G (κ_ G) ⟶ G} {φ₁ φ₂ : 𝒪_ G ⟶ R G (κ_ G)}
    [IsLocalHom φ₁.hom] [IsLocalHom φ₂.hom] (hfφ₁ : f.left = tan φ₁) (hgφ₂ : g.left = tan φ₂)
    (hφ₁ : ∀ r, (φ₁.hom r).fst = residue _ r) (hφ₂ : ∀ r, (φ₂.hom r).fst = residue _ r) :
    ∃ φ : 𝒪_ G ⟶ R G (κ_ G), IsLocalHom φ.hom ∧ (f + g).left = tan φ ∧
      ∀ r, (φ.hom r).snd = (φ₁.hom r).snd + (φ₂.hom r).snd := by
  let c : S G (κ_ G × κ_ G) ⟶ G := Sp (inl₂ G) ≫ f + Sp (inr₂ G) ≫ g
  have e₁ : fst₂ G ∘ₗ inl₂ G = LinearMap.id := LinearMap.ext fun _ ↦ rfl
  have e₂ : fst₂ G ∘ₗ inr₂ G = 0 := LinearMap.ext fun _ ↦ rfl
  have e₃ : snd₂ G ∘ₗ inl₂ G = 0 := LinearMap.ext fun _ ↦ rfl
  have e₄ : snd₂ G ∘ₗ inr₂ G = LinearMap.id := LinearMap.ext fun _ ↦ rfl
  have e₅ : sum₂ G ∘ₗ inl₂ G = LinearMap.id := LinearMap.ext fun _ ↦ by simp
  have e₆ : sum₂ G ∘ₗ inr₂ G = LinearMap.id := LinearMap.ext fun _ ↦ by simp
  have hc₁ : Sp (fst₂ G) ≫ c = f := by
    simp only [c, comp_add, ← Category.assoc, Sp_comp, e₁, e₂, Sp_id, Category.id_comp,
      Sp_zero_comp hgφ₂ hφ₂, _root_.add_zero]
  have hc₂ : Sp (snd₂ G) ≫ c = g := by
    simp only [c, comp_add, ← Category.assoc, Sp_comp, e₃, e₄, Sp_id, Category.id_comp,
      Sp_zero_comp hfφ₁ hφ₁, _root_.zero_add]
  have hc₃ : Sp (sum₂ G) ≫ c = f + g := by
    simp only [c, comp_add, ← Category.assoc, Sp_comp, e₅, e₆, Sp_id, Category.id_comp]
  have hpt : c.left (closedPoint (R G (κ_ G × κ_ G))) = e G :=
    (Sp_comp_left_closedPoint (fst₂ G) c).symm.trans (by rw [hc₁, hfφ₁]; exact tan_closedPoint φ₁)
  obtain ⟨φc, hloc, hceq⟩ := exists_eq_tan c.left hpt
  have : IsLocalHom (mapR (fst₂ G)).hom := inferInstance
  have : IsLocalHom (φc ≫ mapR (fst₂ G)).hom :=
    @CommRingCat.isLocalHom_comp _ _ _ φc _ this hloc
  have : IsLocalHom (φc ≫ mapR (snd₂ G)).hom :=
    @CommRingCat.isLocalHom_comp _ _ _ φc _ inferInstance hloc
  have f₁ : φc ≫ mapR (fst₂ G) = φ₁ :=
    tan_injective (by rw [← Sp_comp_left hceq, hc₁, hfφ₁])
  have f₂ : φc ≫ mapR (snd₂ G) = φ₂ :=
    tan_injective (by rw [← Sp_comp_left hceq, hc₂, hgφ₂])
  refine ⟨φc ≫ mapR (sum₂ G),
    @CommRingCat.isLocalHom_comp _ _ _ φc _ inferInstance hloc, ?_, fun r ↦ ?_⟩
  · rw [← hc₃, Sp_comp_left hceq]
  · rw [← f₁, ← f₂]
    change (TrivSqZeroExt.map _ (φc.hom r)).snd =
      (TrivSqZeroExt.map _ (φc.hom r)).snd + (TrivSqZeroExt.map _ (φc.hom r)).snd
    simp [TrivSqZeroExt.snd_map]

/-- the composition `Spec T ⟶ G ⟶ G` where the a latter is an endomorphisms of the group
`G` is the morphisms induced by the composition `𝒪_{G,e} ⟶ 𝒪_{G, f(e)} = 𝒪_{G,e} ⟶ T`. -/
lemma tan_comp_end {T : CommRingCat} (φ : 𝒪_ G ⟶ T) (f : End (mk G)) :
    tan φ ≫ (f.asHom.hom.hom : G ⟶ G).left = tan (stalkEnd f ≫ φ) := by
  rw [tan, tan, stalkEnd, Category.assoc]
  exact Scheme.SpecMap_comp_fromSpecStalk_comp _ _ (image_unit_of_End f) φ

section Derivation

variable (φ : Lie G)

/-- The derivation `𝒪_{G,e} → κ_{G,e}` attached to `φ : Lie G` (Note that
`φ : (mₑ / mₑ^2) ⟶ κ_{G,e}`). That is, for an element `a ∈ κ_{G,e}`, we know
that `a - comp(a) ∈ mₑ`, where `comp : 𝒪_{G,e} ⟶ K ⟶ 𝒪_{G,e}` (the first morphism
coming from `ζ`, while the second coming from the structure map). And,
`der φ a = φ([a - comp(a)])`. -/
def der (a : 𝒪_ G) : κ_ G :=
  φ (Ideal.toCotangent _ ⟨_, sub_π_hζ_mem a⟩)

/-- For an elemnt `r ∈ mₑ`, we have `der φ r = φ([r])`. -/
lemma der_of_mem {r : 𝒪_ G} (hr : r ∈ maximalIdeal _) :
    der φ r = φ (Ideal.toCotangent _ ⟨r, hr⟩) := by
  simp only [der, hζ_eq_zero hr, map_zero, sub_zero]

/-- Ther derivation of a constant function is zero. `c : K`, viewd as an elemnt of
`𝒪_{G,e}` via the structure map, `der φ c = 0`. -/
lemma der_π (c : K) : der φ ((π G).hom c) = 0 := by
  have : (π G).hom ((hζ G).hom ((π G).hom c)) = (π G).hom c := by
    rw [← CommRingCat.comp_apply (π G) (hζ G), π_hζ, CommRingCat.id_apply]
  simp only [der, this, sub_self]
  convert φ.map_zero
  convert (Ideal.toCotangent _).map_zero

/-- `der` is linear. That is, `der φ (a + b) = der φ a + der φ b` -/
lemma der_add (a b : 𝒪_ G) :
    der φ (a + b) = der φ a + der φ b := by
  simp only [der]
  rw [← map_add, ← map_add]
  congr 2
  ext
  simp only [map_add, Submodule.coe_add]
  ring

/-- `der` is a derivation `der φ (a * b) = [a] * (der φ b) + (der φ a) * [b]` -/
lemma der_mul (a b : 𝒪_ G) :
    der φ (a * b) = residue _ a * der φ b + der φ a * residue _ b := by
  have : Ideal.toCotangent (maximalIdeal _) ⟨_, sub_π_hζ_mem (a * b)⟩ =
      residue _ a • Ideal.toCotangent _ ⟨_, sub_π_hζ_mem b⟩ +
        residue _ b • Ideal.toCotangent _ ⟨_, sub_π_hζ_mem a⟩ := by
    rw [← ResidueField.algebraMap_eq, algebraMap_smul, algebraMap_smul, ← map_smul, ← map_smul,
      ← map_add, Ideal.toCotangent_eq, pow_two]
    convert neg_mem (Ideal.mul_mem_mul (sub_π_hζ_mem a) (sub_π_hζ_mem b)) using 1
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
    ring
  rw [der, this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, der, der, mul_comm (φ _)]

/-- `der φ` is a derivation `𝒪_{G,e} ⟶ κ_{G,e}`. This lifts to a ring hom `𝒪_{G,e} ⟶ κ_{G,e}[ε]`
on the dual numbers. This ring homomorphism is called `derRingHom' φ`. -/
def derRingHom' : 𝒪_ G →+* TrivSqZeroExt (κ_ G) (κ_ G) where
  toFun a := TrivSqZeroExt.inl (residue (𝒪_ G) a) +
    TrivSqZeroExt.inr (der φ a)
  map_one' := by
    have : der φ 1 = 0 := by simpa only [map_one] using der_π φ 1
    ext <;> simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.snd_one, map_one, _root_.add_zero, this]
  map_mul' a b := by
    ext <;> simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.snd_mul, map_mul, _root_.add_zero, _root_.zero_add, smul_eq_mul, op_smul_eq_mul,
      der_mul]
  map_zero' := by
    have : der φ 0 = 0 := by simpa only [map_zero] using der_π φ 0
    ext <;> simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_zero,
      TrivSqZeroExt.snd_zero, map_zero, _root_.add_zero, this]
  map_add' a b := by
    ext <;> simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, map_add, _root_.add_zero,
      _root_.zero_add, der_add]

/-- `derRingHom` is the same as `derRingHom'`, just viewed in `CommRingCat`. Recall:
`der φ` is a derivation `𝒪_{G,e} ⟶ κ_{G,e}`. This lifts to a ring hom `𝒪_{G,e} ⟶ κ_{G,e}[ε]`
on the dual numbers. This ring homomorphism is called `derRingHom' φ`. -/
def derRingHom : 𝒪_ G ⟶ R G (κ_ G) := CommRingCat.ofHom (derRingHom' φ)

/-- The projection of `derRingHom φ : 𝒪_{G,e} ⟶ κ_{G,e}[ε] = κ_{G,e} ⊕ κ_{G,e}` onto the first
component of the direct sum is the quotient map `𝒪_{G,e} ⟶ κ_{G,e}`. -/
@[simp]
lemma derRingHom_fst (a : 𝒪_ G) : ((derRingHom φ).hom a).fst = residue _ a := by
  change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : TrivSqZeroExt (κ_ G) (κ_ G)).fst = _
  rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, _root_.add_zero]

/-- The projection of `derRingHom φ : 𝒪_{G,e} ⟶ κ_{G,e}[ε] = κ_{G,e} ⊕ κ_{G,e}` onto the second
component of the direct sum is `der φ`. -/
@[simp]
lemma derRingHom_snd (a : 𝒪_ G) : ((derRingHom φ).hom a).snd = der φ a := by
  change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : TrivSqZeroExt (κ_ G) (κ_ G)).snd = _
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add]

/-- the morphisms `derRingHom φ : 𝒪_{G,e} ⟶ κ_{G,e}[ε]` is local -/
instance : IsLocalHom (derRingHom φ).hom where
  map_nonunit a ha := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, derRingHom_fst] at ha
    exact isUnit_of_map_unit (residue _) a ha

/-- The composition `K ⟶ 𝒪_{G,e} ⟶ κ_{G,e}[ε]`, where the first comes from the structure map,
while the second is `derRingHom φ`, is equal to the composition `K ⟶ 𝒪_{G,e} ⟶ κ_{G,e}[ε]`,
where the first the structure map, but the second is the map `a ↦ ([a], 0)`. -/
lemma π_derRingHom : π G ≫ derRingHom φ = π G ≫ resInl G (κ_ G) := by
  refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
  change (derRingHom φ).hom ((π G).hom c) = TrivSqZeroExt.inl (residue _ ((π G).hom c))
  ext
  · exact derRingHom_fst φ _
  · rw [derRingHom_snd]
    exact der_π φ c

/-- The tangent vector `Spec κ_{G,e}[ε] ⟶ G` at `e` attached to `φ`. -/
def tanVec : S G (κ_ G) ⟶ G :=
  Over.homMk (tan (derRingHom φ)) ((tan_comp_hom _).trans (by rw [π_derRingHom]; rfl))

end Derivation

end CotangentEndAdd

open CotangentEndAdd

/-- The map `End (mk G) → CoTangent (G, e) = Hom(Lie G, κ_{G,e})` is additive. -/
lemma cotangentEnd_add [IsCommAddMonObj G] (f g : End (mk G)) :
    cotangentEnd (f + g) = cotangentEnd f + cotangentEnd g := by
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.toCotangent_surjective _ v
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (κ_ G)]
  intro φ
  rw [map_sub, sub_eq_zero, LinearMap.add_apply, map_add]
  have key (u : End (AddGrp.mk G)) :
      (tanVec φ ≫ u.asHom.hom.hom).left = tan (stalkEnd u ≫ derRingHom φ) :=
    tan_comp_end _ u
  have hf (u : End (AddGrp.mk G)) (r : 𝒪_ G) :
      ((stalkEnd u ≫ derRingHom φ).hom r).fst = residue (𝒪_ G) r := by
    rw [CommRingCat.comp_apply, derRingHom_fst, residue_stalkEnd]
  have hl (u : End (AddGrp.mk G)) : IsLocalHom (stalkEnd u ≫ derRingHom φ).hom :=
    @CommRingCat.isLocalHom_comp _ _ _ (stalkEnd u) (derRingHom φ) inferInstance inferInstance
  have := hl f
  have := hl g
  have := hl (f + g)
  obtain ⟨f', hloc, hf', hsnd⟩ :=
    left_add_eq_tan (key f) (key g) (hf f) (hf g)
  have : f' = stalkEnd (f + g) ≫ derRingHom φ := by
    refine tan_injective (hf'.symm.trans ?_)
    rw [← key, ← comp_add]
    rfl
  subst this
  have hm (u : End (AddGrp.mk G)) : (stalkEnd u).hom r.1 ∈ maximalIdeal _ :=
    map_nonunit (stalkEnd u).hom _ r.2
  have := hsnd r.1
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply, derRingHom_snd,
    derRingHom_snd, derRingHom_snd, der_of_mem φ (hm f), der_of_mem φ (hm g),
    der_of_mem φ (hm (f + g))] at this
  rw [cotangentEnd_toCotangent, cotangentEnd_toCotangent, cotangentEnd_toCotangent]
  exact this

/-
Hey claude, this should proably be changed to `End (mk G) →+* (Lie G →ₗ[K] Lie G)`
And, whatever that follows. Remind me to do it.
-/
variable (G) in
/-- The representation of `End (mk G)` on the Lie algebra of `G`, as a ring homomorphism,
`End (mk G) →+* (Lie G →ₗ[κ_ G] Lie G)`. -/
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

section BaseField

open CotangentEndAdd in
variable (G) in
/-- The residue field `κ_{G,e}` is isomorphic to `K`. The inverse is the composition
`K ⟶ 𝒪_{G,e} ⟶ κ_{G,e}` of the structure map `π` and the quotient map, and the map
`κ_{G,e} ⟶ K` is induced by `hζ`. -/
def π_κ : κ_ G ≃+* K :=
  RingEquiv.ofRingHom (ResidueField.lift (hζ G).hom) ((residue (𝒪_ G)).comp (π G).hom)
    (by
      ext k
      change (π G ≫ hζ G).hom k = k
      rw [π_hζ]
      rfl)
    (by
      ext x
      obtain ⟨a, rfl⟩ := residue_surjective x
      simpa using residue_π_hζ a)

/-- `Lie G` is a `K`-vector space, via the isomorphism `π_κ : κ_{G,e} ≃ K`. -/
instance : Module K (Lie G) := Module.compHom (Lie G) (π_κ G).symm.toRingHom

/-- Every `κ_{G,e}`-linear map `Lie G → Lie G` is `K`-linear, since `K` acts through `π_κ`. -/
instance : LinearMap.CompatibleSMul (Lie G) (Lie G) K (κ_ G) :=
  ⟨fun f k x ↦ f.map_smul ((π_κ G).symm k) x⟩

variable (G) in
/-- The representation of `End (mk G)` on the Lie algebra of `G`, as a ring homomorphism,
`End (mk G) →+* (Lie G →ₗ[K] Lie G)`. -/
def baseField_lie_algebra_represenation [IsCommAddMonObj G] :
    End (mk G) →+* (Lie G →ₗ[K] Lie G) where
  toFun f := (lie_algebra_represenation G f).restrictScalars K
  map_one' := by rw [map_one]; rfl
  map_mul' f g := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' f g := by rw [map_add]; rfl

variable (G) in
open scoped TensorProduct in
/-- The representation of `ℚ ⊗[ℤ] End (mk G)` on the Lie algebra of `G`, as a ring
homomorphism, `ℚ ⊗[ℤ] End (mk G) →+* (Lie G →ₗ[K] Lie G)`. -/
def rationalEnd_lie_algebra_represenation [CharZero K] [IsCommAddMonObj G] :
    ℚ ⊗[ℤ] End (mk G) →+* (Lie G →ₗ[K] Lie G) :=
  let f₁ : ℚ →ₐ[ℤ] (Lie G →ₗ[K] Lie G) :=
    ((algebraMap K (Lie G →ₗ[K] Lie G)).comp (Rat.castHom K)).toIntAlgHom
  let f₂ := (baseField_lie_algebra_represenation G).toIntAlgHom
  (Algebra.TensorProduct.lift f₁ f₂ fun x y ↦
    Algebra.commute_algebraMap_left (Rat.castHom K x) (f₂ y)).toRingHom

end BaseField
