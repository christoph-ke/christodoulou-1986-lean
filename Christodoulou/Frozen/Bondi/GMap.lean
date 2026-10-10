/-
# `Christodoulou.Bondi.gMap`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.G
public import Christodoulou.Frozen.Bondi.ContinuousG



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `g` as a continuous radial function. -/
@[expose] noncomputable def gMap (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) : C(ℝ≥0, ℝ) :=
  ⟨g h hh, continuous_g h hh⟩

end Christodoulou.Bondi
