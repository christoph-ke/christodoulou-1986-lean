/-
# `Christodoulou.Bondi.scaleInvariantSize_le_initialSize`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.ScaleInvariantSize
public import Christodoulou.Frozen.Bondi.InitialSize
import Christodoulou.Bondi.Provider.ScaleInvariantSizeLeInitialSize



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem scaleInvariantSize_le_initialSize (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) :
    0 ≤ scaleInvariantSize data hdata ∧
      scaleInvariantSize data hdata ≤ initialSize data hdata :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.scaleInvariantSize_le_initialSize



end Christodoulou.Bondi

