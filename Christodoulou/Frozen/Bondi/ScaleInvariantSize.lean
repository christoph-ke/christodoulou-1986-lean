/-
# `Christodoulou.Bondi.scaleInvariantSize`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.ScaledInitialSize



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


@[expose] noncomputable def scaleInvariantSize (data : C(ℝ≥0, ℝ))
    (hdata : IsDecaySlice data) : ℝ :=
  ⨅ a : {a : ℝ≥0 // 0 < a}, scaledInitialSize a a.2 data hdata

end Christodoulou.Bondi
