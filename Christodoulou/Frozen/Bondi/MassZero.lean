/-
# `Christodoulou.Bondi.mass_zero`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.Provider.MassZero



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem mass_zero (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) : mass h hh 0 = 0 :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.mass_zero



end Christodoulou.Bondi

