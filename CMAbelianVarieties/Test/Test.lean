module

public import Mathlib

open CategoryTheory Limits

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [HasPullbacks C]

#synth HasPullbacks (Grp C)
--#synth HasPullbacks (AddGrp C) -- Error
