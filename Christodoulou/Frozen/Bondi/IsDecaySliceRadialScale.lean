/-
# `Christodoulou.Bondi.isDecaySlice_radialScale`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.Provider.IsDecaySliceRadialScale



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem isDecaySlice_radialScale {b : ℝ≥0} (hb : 0 < b) {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data) : IsDecaySlice (radialScale b data) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.isDecaySlice_radialScale



end Christodoulou.Bondi

