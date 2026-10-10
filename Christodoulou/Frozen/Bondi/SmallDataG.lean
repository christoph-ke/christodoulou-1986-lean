/-
# `Christodoulou.Bondi.smallDataG`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Radial.Mean
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The function G of (9.3). -/
@[expose] noncomputable def smallDataG (x : ℝ) : ℝ :=
  x / (2 + π / 6 * x ^ 2) *
    (exp (-(4 * π / 3) * x ^ 2) - π / 8 * x ^ 2 * (2 + π / 6 * x ^ 2))

end Christodoulou.Bondi
