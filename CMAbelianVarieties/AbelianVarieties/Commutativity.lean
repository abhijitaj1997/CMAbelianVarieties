/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
import all Mathlib.AlgebraicGeometry.Group.Abelian

/-!

## Commutativity of abelian varieties

Mathlib proves that abelian varieties are commutative only for (multiplicative)
group objects. In this file we transfer this result to additive group objects.

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

variable {K : Type*} [Field K]
variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

-- Claude solved this problem!
/- Mathlib proves commutativity of abelian varieties only for `GrpObj`. `to_additive` skips it
because `Scheme` counts as a "fixed type", so we mark `Scheme` as translatable and additivize the
proof (see the `to_additive` docstring, section Troubleshooting). -/
attribute [to_additive_do_translate] Scheme Scheme.instCategory
attribute [to_additive (attr := instance) isClosedImmersion_zero_left]
  instIsClosedImmersionLeftSchemeOneOverSpecOf
attribute [to_additive] isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed
attribute [to_additive] isCommMonObj_of_isProper_of_geometricallyIntegral

/-- Abelian varieties are commutative. -/
instance : IsCommAddMonObj A := isCommAddMonObj_of_isProper_of_geometricallyIntegral A
