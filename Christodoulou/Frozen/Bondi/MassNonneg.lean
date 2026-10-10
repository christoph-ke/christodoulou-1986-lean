/-
# `Christodoulou.Bondi.mass_nonneg`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.Provider.MassNonneg



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem mass_nonneg (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) : 0 ≤ mass h hh r :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.mass_nonneg



end Christodoulou.Bondi

