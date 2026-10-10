/-
# `Christodoulou.Bondi.lemma2`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.StepDelta
public import Christodoulou.Frozen.Bondi.XBallIterate
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.Provider.Lemma2



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi

/-- **Lemma 2**, [P] p. 349: there is `δ = δ(x₁) > 0` such that, under the hypotheses of Lemma 1,
`u₀ < δ` makes the iterates contract in `Y`: `‖h_{n+2} − h_{n+1}‖_Y ≤ ½ ‖h_{n+1} − h_n‖_Y`,
written as an implication between upper bounds of the weighted supremum. -/
theorem lemma2 (x₁ : ℝ) :
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
-- Proof.
  by exact Christodoulou.Bondi.Provider.lemma2



end Christodoulou.Bondi

