/-
# `Christodoulou.Bondi.stepEta`

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


@[expose] noncomputable def stepEta (x d : ℝ) : ℝ :=
  let L := π * x ^ 2 / 12
  let F := π * x ^ 3 / 6
  let B := π * x ^ 2 / 2
  let D := 7 * π * x ^ 3 / 12
  let Mstar := exp L * (d + F)
  let Cstar := exp (2 * L) * (4 * d * L + F + D + B * Mstar)
  min 1 ((x - 2 * d) / (2 * (1 + Cstar)))

end Christodoulou.Bondi
