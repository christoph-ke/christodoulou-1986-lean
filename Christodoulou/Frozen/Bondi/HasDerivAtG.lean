/-
# `Christodoulou.Bondi.hasDerivAt_g`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.G
import Christodoulou.Bondi.Provider.HasDerivAtG



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem hasDerivAt_g (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => g h hh (Real.toNNReal s))
      (4 * π * g h hh r * (h r - mean h r) ^ 2 / (r : ℝ)) (r : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivAt_g



end Christodoulou.Bondi

