/-
# `Christodoulou.Bondi.continuous_linearStep`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.Provider.ContinuousLinearStep



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem continuous_linearStep {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ)) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => linearStep hH data p.1 p.2) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.continuous_linearStep



end Christodoulou.Bondi

