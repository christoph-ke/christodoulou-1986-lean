/-
# `Christodoulou.Bondi.linearStep_time_bound`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.Provider.LinearStepTimeBound



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi

/-- (7.60), [P] p. 349, for one step whose input and output lie in the same ball: the time
derivative within `[0, u₀]` is at most `½ x (1 + (π/3) x²) / (1 + r)³`. -/
theorem linearStep_time_bound {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (hS : MemXBall u₀ x (linearStepMap hH data))
    (u r : ℝ≥0) (hu : u ≤ u₀) :
    |derivWithin (fun t : ℝ => linearStep hH data t.toNNReal r) (Icc 0 (u₀ : ℝ)) u| ≤
      1 / 2 * x * (1 + π / 3 * x ^ 2) / (1 + (r : ℝ)) ^ 3 :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.linearStep_time_bound



end Christodoulou.Bondi

