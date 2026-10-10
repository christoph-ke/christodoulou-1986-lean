/-
# `Christodoulou.Bondi.linearStep_value_bound`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearStep
public import Christodoulou.Frozen.Bondi.StepValueBound
import Christodoulou.Bondi.Provider.LinearStepValueBound



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem linearStep_value_bound {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ)) (d : ℝ)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| ≤ d)
    (u r : ℝ≥0) :
    (1 + (r : ℝ)) ^ 3 * |linearStep hH data u r| ≤ stepValueBound x d u₀ :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.linearStep_value_bound



end Christodoulou.Bondi

