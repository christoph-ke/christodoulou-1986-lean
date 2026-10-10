module
public import Christodoulou.Frozen.Bondi.SmallDataDelta
import Christodoulou.Bondi.SmallDataRoots



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem smallDataDelta_pos_and_witness {x₁ : ℝ≥0}
    (hx₁ : 0 < x₁ := by assumption) :
    0 < smallDataDelta x₁ ∧ ∀ d : ℝ, 0 ≤ d → d < smallDataDelta x₁ →
      ∃ x : ℝ, 0 < x ∧ x < x₁ ∧ d ≤ smallDataG x :=
  XSR.smallDataDelta_pos_and_witness x₁ hx₁

end Christodoulou.Bondi.Provider
