/-
# `Christodoulou.Bondi.contractionFactor`

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

/-- The contraction factor s of (9.26). -/
@[expose] noncomputable def contractionFactor (x : ℝ) : ℝ :=
  π / 3 * x ^ 2 * (37 / 6 + 2 * π * x ^ 2) * exp (5 * π / 9 * x ^ 2)

end Christodoulou.Bondi
