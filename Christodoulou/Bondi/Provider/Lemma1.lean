module
public import Christodoulou.Frozen.Bondi.StepEta
public import Christodoulou.Frozen.Bondi.ConstantDataField
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.IterationLemma1



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem lemma1 {d x₁ : ℝ}
    (hd : 0 ≤ d := by assumption)
    (hx : 2 * d < x₁ := by assumption) :
    ∃ η : ℝ, η = stepEta x₁ d ∧ 0 < η ∧
      ∀ (u₀ : ℝ≥0), (u₀ : ℝ) < η → ∀ (data : C(ℝ≥0, ℝ)), IsDecaySlice data →
        (∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
          (1 + (r : ℝ)) ^ 4 *
            |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d) →
        ∃ h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ), ∃ hb : ∀ n, MemXBall u₀ x₁ (h n),
          h 0 = constantDataField data ∧
          (∀ n, h (n + 1) = linearStepMap (hb n) data) ∧
          (∀ n r, h n (0, r) = data r) :=
  XL1.lemma1 d x₁ hd hx

end Christodoulou.Bondi.Provider
