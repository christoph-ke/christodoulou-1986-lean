module
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.LinearStepBasic



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem IsCharacteristic.linearStep_eq {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ := by assumption) {h₀ : C(ℝ≥0, ℝ)} {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ) := by assumption) :
    linearStep hH h₀ (Real.toNNReal t) (Real.toNNReal (χ t)) =
      h₀ (Real.toNNReal (χ 0)) *
          exp (∫ s in (0 : ℝ)..t, linearCoeff hH (Real.toNNReal s) (Real.toNNReal (χ s))) +
        ∫ s in (0 : ℝ)..t,
          exp (∫ τ in s..t, linearCoeff hH (Real.toNNReal τ) (Real.toNNReal (χ τ))) *
            linearSource hH (Real.toNNReal s) (Real.toNNReal (χ s)) :=
  XStep.linearStep_eq hχ h₀ ht

end Christodoulou.Bondi.Provider
