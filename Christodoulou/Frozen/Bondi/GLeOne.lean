/-
# `Christodoulou.Bondi.g_le_one`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.G
import Christodoulou.Bondi.Provider.GLeOne



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem g_le_one (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) : g h hh r ≤ 1 :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.g_le_one



end Christodoulou.Bondi

