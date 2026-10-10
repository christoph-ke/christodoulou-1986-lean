module
public import Christodoulou.Frozen.Bondi.Characteristic
import Christodoulou.Bondi.CharacteristicDependence



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem continuous_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} :
    Continuous (fun p : ℝ × Icc (0 : ℝ) u₀ × ℝ≥0 => characteristic hH p.2.1 p.2.2 p.1) :=
  XDep.continuous_characteristic hH

end Christodoulou.Bondi.Provider
