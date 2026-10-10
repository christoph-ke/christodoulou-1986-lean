/-
# `Christodoulou.Bondi.initialSize_radialScale`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Frozen.Bondi.InitialSize
public import Christodoulou.Frozen.Bondi.ScaledInitialSize
import Christodoulou.Bondi.Provider.InitialSizeRadialScale



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem initialSize_radialScale {a : ℝ≥0} (ha : 0 < a) {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data) (hs : IsDecaySlice (radialScale a data)) :
    initialSize (radialScale a data) hs = scaledInitialSize a ha data hdata :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.initialSize_radialScale



end Christodoulou.Bondi

