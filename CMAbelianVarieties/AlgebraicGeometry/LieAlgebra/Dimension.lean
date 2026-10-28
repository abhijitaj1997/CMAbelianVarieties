/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.LieAlgebra.Defn
public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib

/-!
## Dimension of a group scheme

Need to fill in the details some day.

-/

@[expose] public section

open AlgebraicGeometry Order

/-!
### Krull dimension of a local ring vs. the dimension of its cotangent space

For `Lie G = (mₑ / mₑ²)^∨`, these give `ringKrullDim 𝒪_{G,e} ≤ dim Lie G`, with equality iff
`𝒪_{G,e}` is a regular local ring (assuming `𝒪_{G,e}` is Noetherian).
-/

/- `ringKrullDim R ≤ spanFinrank m`, for `R` Noetherian local (Krull's height theorem).
That is, the Krull dimension is less than the smallest number of generators of the
maximal ideal of `R` -/
#check ringKrullDim_le_spanFinrank_maximalIdeal


/- `spanFinrank m = dim_κ (m / m²)`, for `R` Noetherian -/
#check IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace

/- `R` is regular iff `dim_κ (m / m²) = ringKrullDim R` -/
#check IsRegularLocalRing.iff_finrank_cotangentSpace

#check smooth_of_grpObj

#check Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential

/-!
### Strategy: `dim Lie G` via Kähler differentials

Let `G` be a group scheme over `K`, and write `A = 𝒪_{G,e}`, `m = mₑ`, `κ = A / m`. The key
point is that `e` is a `K`-rational point, so `κ = K` and `K ⟶ A ⟶ κ` is the identity
(in `LieAlgebra/Defn.lean` this is `π_hζ : π G ≫ hζ G = 𝟙 _`).

**Step A: `m / m² ≅ κ ⊗[A] Ω[A⁄K]`.** No smoothness needed, only that `e` is rational.
The conormal sequence of `A ↠ κ` is exact:
  `m / m² ⟶ κ ⊗[A] Ω[A⁄K] ⟶ Ω[κ⁄K] ⟶ 0`.
* Since `κ = K`, we have `Ω[κ⁄K] = 0`, so the first map `d` is surjective.
* The composition `K ⟶ A ⟶ A / m²` is a section of `A / m² ↠ κ`, and such a section gives
  a retraction of `d`, so `d` is injective.
Hence `Lie G = (m / m²)^∨ ≅ (κ ⊗[A] Ω[A⁄K])^∨`. In Mathlib:
* `KaehlerDifferential.kerCotangentToTensor` is the map `d : I / I² ⟶ B ⊗[A] Ω[A⁄R]`.
* `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` is the exactness.
* `retractionKerCotangentToTensorEquivSection` : retractions of `d` correspond to sections of
  `A / I² ⟶ B`.
Note that `der φ a = φ [a - π (hζ a)]` in `LieAlgebra/Defn.lean` is this isomorphism done by hand.

**Step B: smoothness gives `dim_κ (κ ⊗[A] Ω[A⁄K]) = n`.**
If `G` is `SmoothOfRelativeDimension n` over `K`, then `e` has an affine neighbourhood `Spec B`
with `K ⟶ B` standard smooth of relative dimension `n`. Then `Ω[B⁄K]` is free of rank `n`
(`IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`), Kähler differentials commute
with localization, so `Ω[A⁄K]` is free of rank `n`, and `κ ⊗[A] Ω[A⁄K] ≅ κⁿ`.

**A + B : `dim Lie G = n`.** All ingredients are in Mathlib, but the scheme-level glue (from
`SmoothOfRelativeDimension n` to an affine open around `e`, and then to the stalk) is not.

**Step C: regularity and `ringKrullDim A`.** Steps A and B say nothing about `ringKrullDim A`.
* `ringKrullDim A ≤ n` is free: `ringKrullDim_le_spanFinrank_maximalIdeal` and
  `spanFinrank m = dim_κ (m / m²) = n` (needs `A` Noetherian, true as `G` is locally of finite
  type).
* `ringKrullDim A ≥ n` needs dimension theory that is *not* in Mathlib, e.g. "standard smooth of
  relative dimension `n` implies the local rings at closed points have dimension `n`" (via étale
  maps preserving local dimension, and `dim K[x₁, …, xₙ]_m = n`).
* Given `ringKrullDim A = n`, regularity of `A` follows from
  `IsRegularLocalRing.iff_finrank_cotangentSpace`.

**Consequences for this project.**
* `dim Lie G = n` (with `n` the relative dimension) only needs Steps A and B.
* `dim Lie G = topologicalKrullDim G` (the dimension used in `CMStructure`) also needs Step C,
  and homogeneity of `G` to pass from `𝒪_{G,e}` to `G` (see
  `topologicalKrullDim_eq_iSup_ringKrullDim_stalk`).
* For abelian varieties, smoothness itself comes from `smooth_of_grpObj` (after translating
  `GrpObj` to `AddGrpObj` with `to_additive`, as in `IntHom.lean`); `LocallyOfFiniteType` and
  `GeometricallyReduced` are inferred from `IsProper` and `GeometricallyIntegral`.
-/

open CategoryTheory

variable {K : Type*} [Field K]

/-
hey claude, some places need the fact that the dimension of an ableian variety is finite, and they
are using the following lemma for it. Consider maybe creating a separate file somewhere else for
that, because this is result is way too strong. Maybe create a `Basic.lean`, and add the dimension
stuff and the commutativity to it.

At the very least I should probably use the the CM Structure for the finiteness (using the second
conditon)
-/
/-- The dimension of a group scheme `G` over `K` equals the dimension of its Lie algebra. -/
theorem topologicalKrullDim_eq_finrank_Lie (G : Over (Spec ↧K)) [LocallyOfFiniteType G.hom]
    [GeometricallyReduced G.hom] [AddGrpObj G] :
    topologicalKrullDim G.left = Module.finrank (κ_ G) (Lie G) := by
  sorry

-- proof written by Claude
theorem topologicalKrullDim_eq_finrank_baseFiled_Lie (G : Over (Spec ↧K))
    [LocallyOfFiniteType G.hom] [GeometricallyReduced G.hom] [AddGrpObj G] :
    topologicalKrullDim G.left = Module.finrank K (Lie G) := by
  rw [topologicalKrullDim_eq_finrank_Lie, Module.finrank, Module.finrank,
    rank_eq_of_equiv_equiv (π_κ G) (AddEquiv.refl _) (π_κ G).bijective fun r m ↦ ?_]
  change r • m = (π_κ G).symm (π_κ G r) • m
  rw [RingEquiv.symm_apply_apply]
