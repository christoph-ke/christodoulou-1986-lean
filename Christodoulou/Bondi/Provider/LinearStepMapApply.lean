module
public import Christodoulou.Frozen.Bondi.LinearStepMap



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem linearStepMap_apply {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {data : C(ℝ≥0, ℝ)} {u r : ℝ≥0} :
    linearStepMap hH data (u, r) = linearStep hH data u r :=
  rfl

end Christodoulou.Bondi.Provider
