/-
# `Christodoulou.Bondi.monotone_mass`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.Provider.MonotoneMass



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem monotone_mass (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) : Monotone (mass h hh) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.monotone_mass



end Christodoulou.Bondi

