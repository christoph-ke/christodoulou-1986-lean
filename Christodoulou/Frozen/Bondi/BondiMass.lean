/-
# `Christodoulou.Bondi.bondiMass`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.Mass



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


@[expose] noncomputable def bondiMass (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) : ℝ :=
  sSup (Set.range (mass h hh))

end Christodoulou.Bondi
