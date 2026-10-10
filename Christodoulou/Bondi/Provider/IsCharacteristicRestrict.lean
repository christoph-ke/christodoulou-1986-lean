module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Bondi.LinearStepBasic



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem IsCharacteristic.restrict {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ := by assumption) {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ) := by assumption) :
    IsCharacteristic hH ⟨t, ht.1, ht.2.trans u₁.2.2⟩ (Real.toNNReal (χ t)) χ :=
  XStep.restrict hχ ht

end Christodoulou.Bondi.Provider
