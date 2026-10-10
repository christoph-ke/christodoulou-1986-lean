/-
# `Christodoulou.Bondi.constantDataField`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Radial.Mean



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] def constantDataField (data : C(ℝ≥0, ℝ)) : C(ℝ≥0 × ℝ≥0, ℝ) :=
  ⟨fun p => data p.2, data.continuous.comp continuous_snd⟩

end Christodoulou.Bondi
