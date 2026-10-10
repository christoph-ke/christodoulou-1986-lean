module
public import Christodoulou.Frozen.Bondi.DerivGBarX
import Christodoulou.Bondi.XBallDeriv



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem derivGBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H}
    {u r : ℝ≥0} : derivGBarX hH u r ≤ π / 3 * x ^ 2 * (r : ℝ) / (1 + (r : ℝ)) ^ 3 :=
  XBall.derivGBarX_le hH u r

end Christodoulou.Bondi.Provider
