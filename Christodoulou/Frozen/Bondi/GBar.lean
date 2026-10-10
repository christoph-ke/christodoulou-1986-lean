/-
# `Christodoulou.Bondi.gBar`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.GMap
public import Christodoulou.Frozen.Radial.Mean



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `ḡ`, [P] (3.12): the radial mean of `g`. -/
@[expose] noncomputable def gBar (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) : ℝ :=
  mean (gMap h hh) r

end Christodoulou.Bondi
