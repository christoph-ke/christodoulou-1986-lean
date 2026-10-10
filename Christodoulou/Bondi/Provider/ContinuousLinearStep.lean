module
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.LinearStepRegularity



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem continuous_linearStep {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {data : C(ℝ≥0, ℝ)} :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => linearStep hH data p.1 p.2) :=
  XReg.continuous_linearStep hH data

end Christodoulou.Bondi.Provider
