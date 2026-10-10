/-
# `Christodoulou.Bondi.stepValueBound`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Radial.Mean
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] noncomputable def stepValueBound (x d T : ℝ) : ℝ :=
  exp (π * x ^ 2 / 12 * T) * (d + T * (π * x ^ 3 / 6))

end Christodoulou.Bondi
