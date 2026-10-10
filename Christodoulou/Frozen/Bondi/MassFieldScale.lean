/-
# `Christodoulou.Bondi.mass_fieldScale`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.FieldScale
import Christodoulou.Bondi.Provider.MassFieldScale



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem mass_fieldScale {b : ℝ≥0} (hb : 0 < b) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u r : ℝ≥0)
    (hs : IsSlice ((fieldScale b H).curry u)) (hs' : IsSlice (H.curry (b * u))) :
    mass ((fieldScale b H).curry u) hs r = (b : ℝ)⁻¹ * mass (H.curry (b * u)) hs' (b * r) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.mass_fieldScale



end Christodoulou.Bondi

