/-
# `Christodoulou.Bondi.translatedDataField_memXPrimeBall`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.TranslatedDataField
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.InitialBound
import Christodoulou.Bondi.Provider.TranslatedDataFieldMemXPrimeBall



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The seed (9.2) lies in the X′ ball of radius d. -/
theorem translatedDataField_memXPrimeBall {T : ℝ≥0} {d : ℝ}
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) (hbound : InitialBound data d) :
    MemXPrimeBall T d (translatedDataField T data) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.translatedDataField_memXPrimeBall



end Christodoulou.Bondi

