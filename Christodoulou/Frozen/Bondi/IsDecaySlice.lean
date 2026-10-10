/-
# `Christodoulou.Bondi.IsDecaySlice`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Radial.Mean
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Christodoulou.Frozen.Bondi.IsSlice



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The data class of [P] Theorem 1 (p. 348) for one radial slice: `h ∈ C¹[0,∞)`,
`h = O(r⁻³)` and `∂h/∂r = O(r⁻⁴)` as `r → ∞`. -/
@[expose] def IsDecaySlice (h : C(ℝ≥0, ℝ)) : Prop :=
  IsSlice h ∧ deriv (fun s : ℝ => h (Real.toNNReal s)) =O[atTop] (fun s : ℝ => s ^ (-4 : ℤ))

end Christodoulou.Bondi
