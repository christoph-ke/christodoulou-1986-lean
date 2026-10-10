/-
# `Christodoulou.Bondi.bondiMass_spec`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.Provider.BondiMassSpec



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


theorem bondiMass_spec (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) :
    BddAbove (Set.range (mass h hh)) ∧
      Tendsto (mass h hh) atTop (𝓝 (bondiMass h hh)) ∧ 0 ≤ bondiMass h hh :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.bondiMass_spec



end Christodoulou.Bondi

