module
public import Christodoulou.Frozen.Bondi.Characteristic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Christodoulou.Bondi.CharacteristicDependence



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem characteristic_sub_mem_Icc {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ r₁' : ℝ≥0}
    (hr : r₁ ≤ r₁' := by assumption) {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ) := by assumption) :
    characteristic hH u₁ r₁' t - characteristic hH u₁ r₁ t ∈
      Icc ((r₁' : ℝ) - r₁) (exp (π / 12 * x ^ 2 * ((u₁ : ℝ) - t)) * ((r₁' : ℝ) - r₁)) :=
  XDep.characteristic_sub_mem_Icc hH u₁ hr ht

end Christodoulou.Bondi.Provider
