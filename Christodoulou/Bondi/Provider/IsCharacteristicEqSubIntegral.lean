module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Christodoulou.Bondi.CharacteristicIntegral



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem IsCharacteristic.eq_sub_integral {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ := by assumption) {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ) := by assumption) :
    χ t = χ 0 - 1 / 2 * ∫ s in (0 : ℝ)..t, gBarX hH (Real.toNNReal s) (Real.toNNReal (χ s)) :=
  XChar.eq_sub_integral hχ ht

end Christodoulou.Bondi.Provider
