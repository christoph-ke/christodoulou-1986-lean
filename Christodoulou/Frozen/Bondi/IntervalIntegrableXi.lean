/-
# `Christodoulou.Bondi.intervalIntegrable_xi`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.GBar
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Christodoulou.Bondi.Provider.IntervalIntegrableXi



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- Well-definedness of (4.2): the integrand `ḡ (h − h̄)/s` is interval integrable on `[0, r]`. -/
theorem intervalIntegrable_xi (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) :
    IntervalIntegrable
      (fun s : ℝ => gBar h hh (Real.toNNReal s) *
        (h (Real.toNNReal s) - mean h (Real.toNNReal s)) / s) volume 0 (r : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.intervalIntegrable_xi



end Christodoulou.Bondi

