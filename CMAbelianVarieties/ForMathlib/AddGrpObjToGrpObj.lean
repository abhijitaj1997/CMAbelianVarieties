/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Viewing an additive group object as a multiplicative one

`AddGrpObj X` and `GrpObj X` have the same fields under different names. Given an additive group
object we build the corresponding multiplicative one (as a `def`, not an instance, so that the two
structures never compete during instance search). This lets us transfer results that Mathlib only
states multiplicatively, e.g. commutativity of abelian varieties.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

/-- An additive group object `X`, viewed as a (multiplicative) group object. -/
abbrev AddGrpObj.toGrpObj (X : C) [AddGrpObj X] : GrpObj X where
  one := AddMonObj.zero
  mul := AddMonObj.add
  one_mul := AddMonObj.zero_add X
  mul_one := AddMonObj.add_zero X
  mul_assoc := AddMonObj.add_assoc X
  inv := AddGrpObj.neg
  left_inv := AddGrpObj.left_neg X
  right_inv := AddGrpObj.right_neg X

/-- If the multiplicative group object associated to `X` is commutative, then so is `X`. -/
lemma IsCommAddMonObj.of_isCommMonObj [BraidedCategory C] (X : C) [AddGrpObj X]
    (h : letI := AddGrpObj.toGrpObj X; IsCommMonObj X) : IsCommAddMonObj X :=
  letI := AddGrpObj.toGrpObj X
  ⟨IsCommMonObj.mul_comm X⟩

end CategoryTheory
