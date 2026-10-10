/-
# `Christodoulou.Bondi.stepDelta_pos_and_bound`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.StepDelta
import Christodoulou.Bondi.Provider.StepDeltaPosAndBound



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi

/-- `δ(x) > 0`, and for `0 ≤ T < δ(x)` the contraction factor of `linearStep_y_lipschitz` is at
most `½`. -/
theorem stepDelta_pos_and_bound (x : ℝ) :
    0 < stepDelta x ∧ ∀ T : ℝ, 0 ≤ T → T < stepDelta x →
      T * exp (π * x ^ 2 / 12 * T) * (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)) ≤ 1 / 2 :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.stepDelta_pos_and_bound



end Christodoulou.Bondi

