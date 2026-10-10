/-
# `Christodoulou.Bondi.linearStepMap`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.ContinuousLinearStep



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] noncomputable def linearStepMap {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ)) :
    C(ℝ≥0 × ℝ≥0, ℝ) :=
  ⟨fun p => linearStep hH data p.1 p.2, continuous_linearStep hH data⟩

end Christodoulou.Bondi
