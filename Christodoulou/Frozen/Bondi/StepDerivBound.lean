/-
# `Christodoulou.Bondi.stepDerivBound`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.StepValueBound



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] noncomputable def stepDerivBound (x d T : ℝ) : ℝ :=
  exp (2 * (π * x ^ 2 / 12) * T) *
    (d + T * (7 * π * x ^ 3 / 12 + π * x ^ 2 / 2 * stepValueBound x d T))

end Christodoulou.Bondi
