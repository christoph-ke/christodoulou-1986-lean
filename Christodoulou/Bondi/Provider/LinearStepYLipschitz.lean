module
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.Lemma2Proof



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem linearStep_y_lipschitz {u₀ : ℝ≥0}
    {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {hK : MemXBall u₀ x K}
    {data : C(ℝ≥0, ℝ)}
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0) := by assumption)
    (hSK : MemXBall u₀ x (linearStepMap hK data) := by assumption)
    {y : ℝ}
    (hy : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y :=
      by assumption)
    {u r : ℝ≥0}
    (hu : u ≤ u₀ := by assumption) :
    (1 + (r : ℝ)) ^ 3 * |linearStep hH data u r - linearStep hK data u r| ≤
      (u₀ : ℝ) * exp (π * x ^ 2 / 12 * (u₀ : ℝ)) *
        (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)) * y :=
  XL2.linearStep_y_lipschitz hH hK data hdata hSK hy u r hu

end Christodoulou.Bondi.Provider
