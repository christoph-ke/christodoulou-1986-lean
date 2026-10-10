/-
# `Christodoulou.Bondi.bondiMass_fieldScale`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.FieldScale
import Christodoulou.Bondi.Provider.BondiMassFieldScale



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem bondiMass_fieldScale {b : ℝ≥0} (hb : 0 < b) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u : ℝ≥0)
    (hs : IsSlice ((fieldScale b H).curry u)) (hs' : IsSlice (H.curry (b * u))) :
    bondiMass ((fieldScale b H).curry u) hs = (b : ℝ)⁻¹ * bondiMass (H.curry (b * u)) hs' :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.bondiMass_fieldScale



end Christodoulou.Bondi

