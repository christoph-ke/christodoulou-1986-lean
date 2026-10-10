module
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.StepDelta
public import Christodoulou.Frozen.Bondi.StepEta
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Frozen.Bondi.XBallIterateLimit
import Christodoulou.Frozen.Bondi.IsClassicalSolutionOfLinearStepMapEq
import Christodoulou.Frozen.Bondi.StepEtaPosAndBound
import Christodoulou.Frozen.Bondi.StepDeltaPosAndBound
import Christodoulou.Bondi.IterationBounds



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XT1

/-- Theorem 1 with explicit constants, including the degenerate strip `u₀ = 0`. -/
theorem theorem1_of_lt {u₀ : ℝ≥0} {d x₁ : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x₁) (hT : (u₀ : ℝ) < stepEta x₁ d)
    (hδ : (u₀ : ℝ) < stepDelta x₁)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d) :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), MemXBall u₀ x₁ H ∧ IsClassicalSolution u₀ H ∧
      ∀ r : ℝ≥0, H (0, r) = data r := by
  obtain ⟨H, hH, _, _, hfix, hzero⟩ :=
    Christodoulou.Bondi.xBallIterate_limit hd hx hT hδ data hdata hbound
  exact ⟨H, hH,
    Christodoulou.Bondi.isClassicalSolution_of_linearStepMap_eq hH data hdata.1.1 hfix,
    hzero⟩

/-- Theorem 1: decaying data have a classical solution with uniform radial derivative decay. -/
theorem theorem1 (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) :
    ∃ u₀ : ℝ≥0, 0 < u₀ ∧ ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), IsClassicalSolution u₀ H ∧
      (∀ r : ℝ≥0, H (0, r) = data r) ∧
      ∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
        |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r| ≤
          C * (1 + (r : ℝ)) ^ (-4 : ℤ) := by
  obtain ⟨d, hd, hlub⟩ := XIt.isDecaySlice_exists_data_bound data hdata
  have hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d :=
    fun r => hlub.1 (Set.mem_range_self r)
  let x₁ := 2 * d + 1
  have hx : 2 * d < x₁ := by
    dsimp [x₁]
    linarith
  have hη := (stepEta_pos_and_bound d x₁ hd hx).1
  have hδ := (stepDelta_pos_and_bound x₁).1
  let u₀ : ℝ≥0 := ⟨min (stepEta x₁ d) (stepDelta x₁) / 2, by positivity⟩
  have hu₀ : 0 < u₀ := by
    change 0 < min (stepEta x₁ d) (stepDelta x₁) / 2
    positivity
  have hhalf : (u₀ : ℝ) < min (stepEta x₁ d) (stepDelta x₁) := by
    change min (stepEta x₁ d) (stepDelta x₁) / 2 < min (stepEta x₁ d) (stepDelta x₁)
    have hm : 0 < min (stepEta x₁ d) (stepDelta x₁) := lt_min hη hδ
    linarith only [hm]
  obtain ⟨H, hH, hsol, hzero⟩ := theorem1_of_lt hd hx
    (hhalf.trans_le (min_le_left _ _)) (hhalf.trans_le (min_le_right _ _)) data hdata hbound
  refine ⟨u₀, hu₀, H, hsol, hzero, x₁, ?_⟩
  intro u hu r
  have hw : 0 < (1 + (r : ℝ)) ^ 4 := by positivity
  have hb := hH.2.2 u hu r
  have hq : (1 + (r : ℝ)) ^ 4 *
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r| ≤ x₁ :=
    (le_add_of_nonneg_left (by positivity)).trans hb
  rw [zpow_neg, ← div_eq_mul_inv]
  apply (le_div_iff₀ hw).mpr
  simpa only [mul_comm] using hq

end XT1
end Christodoulou.Bondi
