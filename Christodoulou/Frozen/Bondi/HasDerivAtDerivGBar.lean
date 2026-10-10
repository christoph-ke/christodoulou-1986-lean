/-
# `Christodoulou.Bondi.hasDerivAt_deriv_gBar`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.GBar
import Christodoulou.Bondi.Provider.HasDerivAtDerivGBar



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem hasDerivAt_deriv_gBar (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (deriv fun s : ℝ => gBar h hh (Real.toNNReal s))
      (-2 * (g h hh r - gBar h hh r) / (r : ℝ) ^ 2
        + 4 * π * g h hh r * (h r - mean h r) ^ 2 / (r : ℝ) ^ 2) (r : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivAt_deriv_gBar



end Christodoulou.Bondi

