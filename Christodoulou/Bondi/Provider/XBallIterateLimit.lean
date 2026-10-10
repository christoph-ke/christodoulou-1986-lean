module
public import Christodoulou.Frozen.Bondi.StepDelta
public import Christodoulou.Frozen.Bondi.XBallIterate
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Christodoulou.Bondi.IterateLimit



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem xBallIterate_limit {u₀ : ℝ≥0}
    {d x₁ : ℝ}
    (hd : 0 ≤ d := by assumption)
    (hx : 2 * d < x₁ := by assumption)
    (hT : (u₀ : ℝ) < stepEta x₁ d := by assumption)
    (hδ : (u₀ : ℝ) < stepDelta x₁ := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d :=
      by assumption) :
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
  XLim.xBallIterate_limit hd hx hT hδ data hdata hbound

end Christodoulou.Bondi.Provider
