/-
# `Christodoulou.Bondi.translatedDataField_apply`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.TranslatedDataField
import Christodoulou.Bondi.Provider.TranslatedDataFieldApply



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The seed (9.2) on the strip. -/
theorem translatedDataField_apply (T : ℝ≥0) (data : C(ℝ≥0, ℝ))
    (u r : ℝ≥0) (hu : u ≤ T) :
    translatedDataField T data (u, r) = data (r + u / 2) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.translatedDataField_apply



end Christodoulou.Bondi

