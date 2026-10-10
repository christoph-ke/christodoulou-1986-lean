/-
# `Christodoulou.Bondi.mass_eq_integral`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.Provider.MassEqIntegral



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem mass_eq_integral (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) :
    mass h hh r = 2 * π * ∫ s in (0 : ℝ)..(r : ℝ),
      gBar h hh (Real.toNNReal s) / g h hh (Real.toNNReal s) *
        (h (Real.toNNReal s) - mean h (Real.toNNReal s)) ^ 2 :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.mass_eq_integral



end Christodoulou.Bondi

