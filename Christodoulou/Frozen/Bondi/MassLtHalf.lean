/-
# `Christodoulou.Bondi.mass_lt_half`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.Provider.MassLtHalf



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem mass_lt_half (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) (hr : 0 < r) :
    mass h hh r < (r : ℝ) / 2 :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.mass_lt_half



end Christodoulou.Bondi

