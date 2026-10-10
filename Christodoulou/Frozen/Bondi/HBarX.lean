/-
# `Christodoulou.Bondi.hBarX`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Radial.Mean
public import Mathlib.Topology.CompactOpen



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] noncomputable def hBarX (u₀ : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u r : ℝ≥0) : ℝ :=
  mean (H.curry (min u u₀)) r

end Christodoulou.Bondi
