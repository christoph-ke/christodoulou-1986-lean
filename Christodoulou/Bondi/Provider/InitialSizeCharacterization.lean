module
public import Christodoulou.Frozen.Bondi.InitialSize
public import Christodoulou.Frozen.Bondi.InitialBound
import Christodoulou.Bondi.XPrimeBasics



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem initialSize_characterization {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption) :
    0 ≤ initialSize data hdata ∧ ∀ d : ℝ,
      InitialBound data d ↔ initialSize data hdata ≤ d :=
  XPB.initialSize_characterization data hdata

end Christodoulou.Bondi.Provider
