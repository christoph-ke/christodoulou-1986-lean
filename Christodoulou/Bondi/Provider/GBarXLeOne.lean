module
public import Christodoulou.Frozen.Bondi.GBarX
import Christodoulou.Frozen.Bondi.GBarLeG
import Christodoulou.Frozen.Bondi.GLeOne



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem gBarX_le_one {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H}
    {u r : ℝ≥0} : gBarX hH u r ≤ 1 :=
  (gBar_le_g _ _ r).trans (g_le_one _ _ r)

end Christodoulou.Bondi.Provider
