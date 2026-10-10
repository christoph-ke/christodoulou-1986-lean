module
public import Christodoulou.Frozen.Bondi.GBarX
import Christodoulou.Bondi.XBallContinuity



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem continuous_gBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H} :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => gBarX hH p.1 p.2) :=
  XBall.continuous_gBarX hH

end Christodoulou.Bondi.Provider
