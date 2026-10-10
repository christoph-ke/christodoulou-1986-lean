module
public import Christodoulou.Frozen.Bondi.Characteristic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Christodoulou.Bondi.CharacteristicDependence



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem characteristic_sub_mem_Icc_of_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ u₁' : Icc (0 : ℝ) u₀}
    (hu : (u₁ : ℝ) ≤ u₁' := by assumption) {r₁ : ℝ≥0} {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ) := by assumption) :
    characteristic hH u₁' r₁ t - characteristic hH u₁ r₁ t ∈
      Icc 0 (exp (π / 12 * x ^ 2 * ((u₁ : ℝ) - t)) * (((u₁' : ℝ) - u₁) / 2)) :=
  XDep.characteristic_sub_mem_Icc_of_le hH hu r₁ ht

end Christodoulou.Bondi.Provider
