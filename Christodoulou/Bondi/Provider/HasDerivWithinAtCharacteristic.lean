module
public import Christodoulou.Frozen.Bondi.Characteristic
public import Christodoulou.Frozen.Bondi.LinearCoeff
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Christodoulou.Bondi.CharacteristicDependence



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem hasDerivWithinAt_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ) := by assumption) :
    HasDerivWithinAt (fun ρ : ℝ => characteristic hH u₁ (Real.toNNReal ρ) t)
      (exp (∫ s in t..(u₁ : ℝ),
        linearCoeff hH (Real.toNNReal s) (Real.toNNReal (characteristic hH u₁ r₁ s))))
      (Ici 0) (r₁ : ℝ) :=
  XDep.hasDerivWithinAt_characteristic hH u₁ r₁ ht

end Christodoulou.Bondi.Provider
