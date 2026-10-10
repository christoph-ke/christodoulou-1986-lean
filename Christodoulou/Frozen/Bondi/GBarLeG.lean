/-
# `Christodoulou.Bondi.gBar_le_g`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.GBar
import Christodoulou.Bondi.Provider.GBarLeG



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem gBar_le_g (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) :
    gBar h hh r ≤ g h hh r :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.gBar_le_g



end Christodoulou.Bondi

