module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
import Christodoulou.Bondi.LinearStepRegularity



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem continuous_derivLinearStep {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {data : C(ℝ≥0, ℝ)}
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) := by assumption) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => derivLinearStep hH data hdata p.1 p.2) :=
  XReg.continuous_derivLinearStep hH data hdata

end Christodoulou.Bondi.Provider
