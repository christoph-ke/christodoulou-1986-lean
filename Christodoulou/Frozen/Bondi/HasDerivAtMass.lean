/-
# `Christodoulou.Bondi.hasDerivAt_mass`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.Provider.HasDerivAtMass



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem hasDerivAt_mass (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => mass h hh (Real.toNNReal s))
      (2 * π * (gBar h hh r / g h hh r) * (h r - mean h r) ^ 2) (r : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivAt_mass



end Christodoulou.Bondi

