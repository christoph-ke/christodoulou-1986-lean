/-
# `Christodoulou.Bondi.scaleInvariantSize_radialScale`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.ScaleInvariantSize
public import Christodoulou.Frozen.Bondi.RadialScale
import Christodoulou.Bondi.Provider.ScaleInvariantSizeRadialScale



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem scaleInvariantSize_radialScale {b : ℝ≥0} (hb : 0 < b) {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data) (hs : IsDecaySlice (radialScale b data)) :
    scaleInvariantSize (radialScale b data) hs = scaleInvariantSize data hdata :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.scaleInvariantSize_radialScale



end Christodoulou.Bondi

