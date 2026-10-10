module
public import Christodoulou.Frozen.Bondi.GBarX
import Christodoulou.Bondi.GBarBasic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem gBarX_pos {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H}
    {u r : ℝ≥0} : 0 < gBarX hH u r :=
  gBar_pos _ _ r

end Christodoulou.Bondi.Provider
