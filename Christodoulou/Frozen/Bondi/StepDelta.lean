/-
# `Christodoulou.Bondi.stepDelta`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Radial.Mean
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi


@[expose] noncomputable def stepDelta (x : ℝ) : ℝ :=
  min 1 (1 / (2 * (1 + exp (π * x ^ 2 / 12) *
    (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)))))

end Christodoulou.Bondi
