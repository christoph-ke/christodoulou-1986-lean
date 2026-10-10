module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Bondi.CharacteristicBasic



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem IsCharacteristic.eqOn {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ ψ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ := by assumption)
    (hψ : IsCharacteristic hH u₁ r₁ ψ := by assumption) :
    EqOn χ ψ (Icc 0 (u₁ : ℝ)) :=
  XChar.eqOn hχ hψ

end Christodoulou.Bondi.Provider
