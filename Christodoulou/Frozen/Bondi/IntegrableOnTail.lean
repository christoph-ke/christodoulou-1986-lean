/-
# `Christodoulou.Bondi.integrableOn_tail`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsSlice
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Christodoulou.Bondi.Provider.IntegrableOnTail



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- Well-definedness of (3.11): the integrand `(h − h̄)²/s` is integrable on `(r, ∞)`. -/
theorem integrableOn_tail (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) :
    IntegrableOn (fun s : ℝ => (h (Real.toNNReal s) - mean h (Real.toNNReal s)) ^ 2 / s)
      (Ioi (r : ℝ)) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.integrableOn_tail



end Christodoulou.Bondi

