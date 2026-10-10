module
public import Christodoulou.Frozen.Bondi.ContractionFactor
import Christodoulou.Bondi.SmallDataRoots



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem existsUnique_contraction_radius :
    ∃! x₁ : ℝ≥0, 0 < x₁ ∧ contractionFactor x₁ = 1 :=
  XSR.existsUnique_contraction_radius 

end Christodoulou.Bondi.Provider
