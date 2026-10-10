/-
# `Christodoulou.Bondi.initialSize_characterization`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.InitialSize
public import Christodoulou.Frozen.Bondi.InitialBound
import Christodoulou.Bondi.Provider.InitialSizeCharacterization



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- Characterization of `initialSize`: nonnegative, and `InitialBound data d ↔ initialSize ≤
d`. -/
theorem initialSize_characterization (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) :
    0 ≤ initialSize data hdata ∧ ∀ d : ℝ,
      InitialBound data d ↔ initialSize data hdata ≤ d :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.initialSize_characterization



end Christodoulou.Bondi

