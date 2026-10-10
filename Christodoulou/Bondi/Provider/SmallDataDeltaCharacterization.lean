module
public import Christodoulou.Frozen.Bondi.SmallDataDelta
import Christodoulou.Bondi.SmallDataScalars



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem smallDataDelta_characterization {x₁ : ℝ≥0} :
    ∃ z ∈ Icc 0 (x₁ : ℝ), smallDataDelta x₁ = smallDataG z ∧
      ∀ x ∈ Icc 0 (x₁ : ℝ), smallDataG x ≤ smallDataDelta x₁ :=
  XSD.smallDataDelta_characterization x₁

end Christodoulou.Bondi.Provider
