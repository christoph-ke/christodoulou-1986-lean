module
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.LinearStepODE



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem eq_linearStep_of_hasDerivWithinAt {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {h₀ : C(ℝ≥0, ℝ)} {q : ℝ≥0 → ℝ≥0 → ℝ}
    (hq₀ : ∀ r, q 0 r = h₀ r := by assumption)
    (hq : ∀ (u₁ : Icc (0 : ℝ) u₀) (r₁ : ℝ≥0) (χ : ℝ → ℝ), IsCharacteristic hH u₁ r₁ χ →
      ∀ t ∈ Icc 0 (u₁ : ℝ),
        HasDerivWithinAt (fun s : ℝ => q (Real.toNNReal s) (Real.toNNReal (χ s)))
          (linearCoeff hH (Real.toNNReal t) (Real.toNNReal (χ t)) *
              q (Real.toNNReal t) (Real.toNNReal (χ t)) +
            linearSource hH (Real.toNNReal t) (Real.toNNReal (χ t)))
          (Icc 0 (u₁ : ℝ)) t := by assumption)
    {u : ℝ≥0} (hu : u ≤ u₀ := by assumption) {r : ℝ≥0} : q u r = linearStep hH h₀ u r :=
  XStep.eq_linearStep_of_hasDerivWithinAt hH h₀ hq₀ hq hu r

end Christodoulou.Bondi.Provider
