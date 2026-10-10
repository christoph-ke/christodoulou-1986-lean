/-
# `Christodoulou.Bondi.xi`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.GBar
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `ξ = ∫₀^r ḡ (h − h̄) dr/r`, [P] (4.2), on the slice class `IsSlice`. -/
@[expose] noncomputable def xi (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) : ℝ :=
  ∫ s in (0 : ℝ)..(r : ℝ),
    gBar h hh (Real.toNNReal s) * (h (Real.toNNReal s) - mean h (Real.toNNReal s)) / s

end Christodoulou.Bondi
