module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Bondi.CharacteristicBasic



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem IsCharacteristic.mem_Icc {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ := by assumption) {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ) := by assumption) :
    χ t ∈ Icc (r₁ : ℝ) (r₁ + ((u₁ : ℝ) - t) / 2) :=
  XChar.mem_Icc hχ ht

end Christodoulou.Bondi.Provider
