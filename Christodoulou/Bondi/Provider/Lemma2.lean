module
public import Christodoulou.Frozen.Bondi.StepDelta
public import Christodoulou.Frozen.Bondi.XBallIterate
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.Lemma2Proof



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem lemma2 {x₁ : ℝ} :
    ∃ δ : ℝ, δ = stepDelta x₁ ∧ 0 < δ ∧
      ∀ (d : ℝ) (hd : 0 ≤ d) (hx : 2 * d < x₁) (u₀ : ℝ≥0)
        (hT : (u₀ : ℝ) < stepEta x₁ d), (u₀ : ℝ) < δ →
      ∀ (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
        (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
          (1 + (r : ℝ)) ^ 4 *
            |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d)
        (n : ℕ) (y : ℝ),
      (∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 *
        |(xBallIterate hd hx hT data hdata hbound (n + 1)).val (u, r) -
          (xBallIterate hd hx hT data hdata hbound n).val (u, r)| ≤ y) →
      ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 *
        |(xBallIterate hd hx hT data hdata hbound (n + 2)).val (u, r) -
          (xBallIterate hd hx hT data hdata hbound (n + 1)).val (u, r)| ≤ y / 2 :=
  XL2.lemma2 x₁

end Christodoulou.Bondi.Provider
