/-
# `Christodoulou.Bondi.exists_scaledInitialSize_lt`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.ScaleInvariantSize
import Christodoulou.Bondi.Provider.ExistsScaledInitialSizeLt



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem exists_scaledInitialSize_lt {data : C(ℝ≥0, ℝ)} (hdata : IsDecaySlice data)
    {δ : ℝ} (h : scaleInvariantSize data hdata < δ) :
    ∃ (a : ℝ≥0) (ha : 0 < a), scaledInitialSize a ha data hdata < δ :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.exists_scaledInitialSize_lt



end Christodoulou.Bondi

