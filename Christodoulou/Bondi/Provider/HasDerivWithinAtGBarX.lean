module
public import Christodoulou.Frozen.Bondi.GBarX
public import Christodoulou.Frozen.Bondi.DerivGBarX
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Christodoulou.Bondi.XBallDeriv



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem hasDerivWithinAt_gBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u r : ℝ≥0} :
    HasDerivWithinAt (fun s : ℝ => gBarX hH u (Real.toNNReal s)) (derivGBarX hH u r) (Ici 0)
      (r : ℝ) :=
  XBall.hasDerivWithinAt_gBarX hH u r

end Christodoulou.Bondi.Provider
