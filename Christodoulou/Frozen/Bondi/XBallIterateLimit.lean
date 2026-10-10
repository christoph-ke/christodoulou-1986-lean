/-
# `Christodoulou.Bondi.xBallIterate_limit`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.StepDelta
public import Christodoulou.Frozen.Bondi.XBallIterate
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Christodoulou.Bondi.Provider.XBallIterateLimit



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The limit of the iterates, [P] p. 349 (proof of Theorem 1): if `u₀ < min{η, δ}`, the
iterates converge in `Y` at the geometric rate of Lemma 2 to a field `H` in the closed ball of
radius `x₁` in `X`, their radial derivatives converge uniformly on the strip, and `H` is a fixed
point of the linear step taking the given data. -/
theorem xBallIterate_limit {u₀ : ℝ≥0} {d x₁ : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x₁) (hT : (u₀ : ℝ) < stepEta x₁ d)
    (hδ : (u₀ : ℝ) < stepDelta x₁)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d) :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), ∃ hH : MemXBall u₀ x₁ H,
      (∀ n : ℕ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 *
        |(xBallIterate hd hx hT data hdata hbound n).val (u, r) - H (u, r)| ≤ 4 * x₁ / 2 ^ n) ∧
      TendstoUniformlyOn
        (fun n (p : ℝ × ℝ) => derivWithin
          (fun s : ℝ => (xBallIterate hd hx hT data hdata hbound n).val
            (p.1.toNNReal, s.toNNReal)) (Ici 0) p.2)
        (fun p : ℝ × ℝ => derivWithin (fun s : ℝ => H (p.1.toNNReal, s.toNNReal)) (Ici 0) p.2)
        atTop (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) ∧
      linearStepMap hH data = H ∧
      ∀ r : ℝ≥0, H (0, r) = data r :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.xBallIterate_limit



end Christodoulou.Bondi

