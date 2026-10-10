module
public import Christodoulou.Frozen.Bondi.Characteristic
public import Christodoulou.Frozen.Bondi.LinearCoeff
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Christodoulou.Bondi.CharacteristicDependence



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem continuous_exp_integral_linearCoeff {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} :
    Continuous (fun p : ℝ × Icc (0 : ℝ) u₀ × ℝ≥0 =>
      exp (∫ s in p.1..(p.2.1 : ℝ),
        linearCoeff hH (Real.toNNReal s) (Real.toNNReal (characteristic hH p.2.1 p.2.2 s)))) :=
  XDep.continuous_exp_integral_linearCoeff hH

end Christodoulou.Bondi.Provider
