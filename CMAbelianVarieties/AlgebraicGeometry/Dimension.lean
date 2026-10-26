/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.BaseFieldChange
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
## Dimension

Results about the (Krull) dimension of schemes.

-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CommRingCat Spec

universe u

variable {K : Type u} [Field K]

#check smoothOfRelativeDimension_isStableUnderBaseChange -- But I don't wanna just prove this
-- for AVs
/-
(Written by AI.) Possibly useful: dimension of a scheme = sup of dimensions over an open cover.
Not in Mathlib as a single lemma, but it follows from these. For any open cover `𝒰` of any
scheme (or quasi-sober T0 space) `X`, `dim X = ⨆ i, dim (𝒰.X i)`; no connected/proper needed.
Ingredients:
1. `irreducibleSetEquivPoints : IrreducibleCloseds α ≃o α` (Mathlib/Topology/Sober.lean),
   needs `[QuasiSober α] [T0Space α]` and `attribute [local instance] specializationOrder`.
   With `Order.krullDim_eq_of_orderIso`: `topologicalKrullDim X = krullDim X`.
2. `Order.krullDim_eq_iSup_coheight : krullDim α = ⨆ a, ↑(coheight a)`
   (Mathlib/Order/KrullDimension.lean).
3. `Topology.IsOpenEmbedding.coheight_eq : coheight (f x) = coheight x`
   (Mathlib/Topology/KrullDimension.lean); scheme version
   `AlgebraicGeometry.coheight_eq_of_isOpenImmersion` (Mathlib/AlgebraicGeometry/Properties.lean).
4. `topologicalKrullDim_subspace_le`, `Topology.IsInducing.topologicalKrullDim_le`
   (Mathlib/Topology/KrullDimension.lean): the easy direction `⨆ i, dim Uᵢ ≤ dim X`.
5. Affine pieces: `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`
   (Mathlib/RingTheory/Spectrum/Prime/Topology.lean); also
   `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` (dim X = sup of dims of the stalks).
Proof outline:
- `≤`: by 1 and 2, `dim X = ⨆ x, coheight x`. For each `x` pick `i`, `y` with `𝒰.f i y = x`;
  by 3, `coheight x = coheight y ≤ krullDim (𝒰.X i)` (`Order.coheight_le_krullDim`),
  and that is `topologicalKrullDim (𝒰.X i)` by 1 again.
- `≥`: 4 applied to each `𝒰.f i` (an open embedding).
Example of this style of argument: `IsLocallyArtinian.of_topologicalKrullDim_le_zero`
(Mathlib/AlgebraicGeometry/Artinian.lean).

(Written by AI.) Affine case: `dim (L ⊗[K] A) = dim A` for a field extension `L/K`.
Not in Mathlib. Needs `A` of finite type over `K` (false in general: `dim K(t) = 0` but
`dim (K(t) ⊗[K] K(s)) = 1`); here that comes from `LocallyOfFiniteType`.
Route via Noether normalization:
1. `exists_finite_inj_algHom_of_fg` / `exists_integral_inj_algHom_of_fg` (Stacks 00OW,
   Mathlib/RingTheory/NoetherNormalization.lean): an injective finite
   `g : MvPolynomial (Fin s) K →ₐ[K] A`.
2. Base change `L ⊗[K] -`: stays finite, and injective since `L` is flat over `K`. So
   `L ⊗[K] A` is finite over `MvPolynomial (Fin s) L` and contains it.
3. `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`
   (Mathlib/RingTheory/KrullDimension/Polynomial.lean): `dim K[x₁..xₛ] = s`, same over `L`.
4. Missing: for an injective integral map `R → S`, `dim S = dim R`. Ingredients (going up,
   lying over, incomparability) are in Mathlib/RingTheory/Ideal/GoingUp.lean, but the
   dimension statement isn't (possible `ForMathlib` candidate).
Alternative, only for algebraic `L/K` (so not enough here, `K₁` is arbitrary): `A → L ⊗[K] A`
is flat, so `Algebra.HasGoingDown.of_flat` (Mathlib/RingTheory/Ideal/GoingDown.lean), and
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (Stacks 00ON,
Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean) gives `ht P = ht p + ht (P in the fibre)`.
The fibre `κ(p) ⊗[K] L` has dimension 0 only when `L/K` is algebraic.
-/
lemma dimension_isStableUnderBasechange (X : Over (Spec ↧K)) [LocallyOfFiniteType X.hom]
    (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    topologicalKrullDim X.left = topologicalKrullDim (X _ K₁).left := sorry

end
