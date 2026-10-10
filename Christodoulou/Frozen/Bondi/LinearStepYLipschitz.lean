/-
# `Christodoulou.Bondi.linearStep_y_lipschitz`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.Provider.LinearStepYLipschitz



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi

/-- The local (9.37)–(9.38): the linear step is Lipschitz in the field, in the norm of `Y`, with
constant `u₀ e^{(π/12) x² u₀} π x² (37/6 + 2π x²)`, when the output of `K` lies in the same ball. -/
theorem linearStep_y_lipschitz {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (hSK : MemXBall u₀ x (linearStepMap hK data)) {y : ℝ}
    (hy : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y)
    (u r : ℝ≥0) (hu : u ≤ u₀) :
    (1 + (r : ℝ)) ^ 3 * |linearStep hH data u r - linearStep hK data u r| ≤
      (u₀ : ℝ) * exp (π * x ^ 2 / 12 * (u₀ : ℝ)) *
        (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)) * y :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.linearStep_y_lipschitz



end Christodoulou.Bondi

