module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
## Goal

The goal of this section is to have some basic facts about invertible
sheaves/line bundles

-/

@[expose] public section

/-! ### Locally free sheaves (vector bundles)

Mathlib defines locally free sheaves of modules in
`Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean`, for a general sheaf of rings
on a site. For a scheme `X`, `X.Modules` is `SheafOfModules X.ringCatSheaf`
(`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`), so a vector bundle on `X` is
`M : X.Modules` with `[M.IsLocallyFree]`. -/

#check @SheafOfModules.IsLocallyFree
#check @SheafOfModules.LocalGeneratorsData.IsLocallyFreeData
#check @AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry SheafOfModules
#check SheafOfModules.IsLocallyFree


variable {X : Scheme} (M : X.Modules)

#check fullyFaithfulForget
#check ((forget X.ringCatSheaf).obj M)
