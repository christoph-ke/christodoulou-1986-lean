/-
# `Christodoulou.Bondi.g`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.IsSlice
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `g = exp[−4π ∫_r^∞ (h − h̄)² ds/s]`, [P] (3.11), on the slice class `IsSlice`. -/
@[expose] noncomputable def g (h : C(ℝ≥0, ℝ)) (_hh : IsSlice h) (r : ℝ≥0) : ℝ :=
  Real.exp (-(4 * π) *
    ∫ s in Ioi (r : ℝ), (h (Real.toNNReal s) - mean h (Real.toNNReal s)) ^ 2 / s)

end Christodoulou.Bondi
