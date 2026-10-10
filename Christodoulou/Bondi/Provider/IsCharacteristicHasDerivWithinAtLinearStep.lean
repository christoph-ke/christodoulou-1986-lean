module
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.LinearStepODE



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem IsCharacteristic.hasDerivWithinAt_linearStep {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ := by assumption) {h₀ : C(ℝ≥0, ℝ)} {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ) := by assumption) :
    HasDerivWithinAt (fun s : ℝ => linearStep hH h₀ (Real.toNNReal s) (Real.toNNReal (χ s)))
      (linearCoeff hH (Real.toNNReal t) (Real.toNNReal (χ t)) *
          linearStep hH h₀ (Real.toNNReal t) (Real.toNNReal (χ t)) +
        linearSource hH (Real.toNNReal t) (Real.toNNReal (χ t)))
      (Icc 0 (u₁ : ℝ)) t :=
  XStep.hasDerivWithinAt_linearStep hχ h₀ ht

end Christodoulou.Bondi.Provider
