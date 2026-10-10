module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
import Christodoulou.Bondi.LinearStepRegularity



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem hasDerivWithinAt_linearStep {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {data : C(ℝ≥0, ℝ)}
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) := by assumption)
    {u r : ℝ≥0} :
    HasDerivWithinAt (fun s : ℝ => linearStep hH data u (Real.toNNReal s))
      (derivLinearStep hH data hdata u r) (Ici 0) (r : ℝ) :=
  XReg.hasDerivWithinAt_linearStep hH data hdata u r

end Christodoulou.Bondi.Provider
