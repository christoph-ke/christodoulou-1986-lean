module
public import Christodoulou.Frozen.Bondi.XBallIterate
import Christodoulou.Frozen.Bondi.StepEtaPosAndBound
import Christodoulou.Frozen.Bondi.LinearStepMapApply
import Christodoulou.Frozen.Bondi.LinearStepZero



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
namespace XL1

/-- The iterates satisfy the source recursion and take the given data at `u = 0`. -/
theorem xBallIterate_rec {u₀ : ℝ≥0} {d x : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x) (hT : (u₀ : ℝ) < stepEta x d)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d) :
    (xBallIterate hd hx hT data hdata hbound 0).val = constantDataField data ∧
    (∀ n, (xBallIterate hd hx hT data hdata hbound (n + 1)).val =
      linearStepMap (xBallIterate hd hx hT data hdata hbound n).property data) ∧
    (∀ n r, (xBallIterate hd hx hT data hdata hbound n).val (0, r) = data r) := by
  refine ⟨rfl, fun n => rfl, ?_⟩
  intro n r
  cases n with
  | zero => rfl
  | succ n =>
    change linearStepMap (xBallIterate hd hx hT data hdata hbound n).property
      data (0, r) = data r
    rw [linearStepMap_apply, linearStep_zero]

/-- Every named iterate belongs to the X-ball on the prescribed strip. -/
theorem xBallIterate_memXBall {u₀ : ℝ≥0} {d x : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x) (hT : (u₀ : ℝ) < stepEta x d)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d) (n : ℕ) :
    MemXBall u₀ x (xBallIterate hd hx hT data hdata hbound n).val := by
  exact (xBallIterate hd hx hT data hdata hbound n).property

/-- Lemma 1: the explicit positive time gives a sequence in the closed X-ball. -/
theorem lemma1 (d x₁ : ℝ) (hd : 0 ≤ d) (hx : 2 * d < x₁) :
    ∃ η : ℝ, η = stepEta x₁ d ∧ 0 < η ∧
      ∀ (u₀ : ℝ≥0), (u₀ : ℝ) < η → ∀ (data : C(ℝ≥0, ℝ)), IsDecaySlice data →
        (∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
          (1 + (r : ℝ)) ^ 4 *
            |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d) →
        ∃ h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ), ∃ hb : ∀ n, MemXBall u₀ x₁ (h n),
          h 0 = constantDataField data ∧
          (∀ n, h (n + 1) = linearStepMap (hb n) data) ∧
          (∀ n r, h n (0, r) = data r) := by
  refine ⟨stepEta x₁ d, rfl, (stepEta_pos_and_bound d x₁ hd hx).1, ?_⟩
  intro u₀ hT data hdata hbound
  let b := xBallIterate hd hx hT data hdata hbound
  refine ⟨fun n => (b n).val, fun n => (b n).property, ?_⟩
  exact xBallIterate_rec hd hx hT data hdata hbound

/-- Lemma 1 specialized to the exact weighted data supremum in (7.4). -/
theorem lemma1_exact (d x₁ : ℝ) (hd : 0 ≤ d) (hx : 2 * d < x₁) :
    ∃ η : ℝ, η = stepEta x₁ d ∧ 0 < η ∧
      ∀ (u₀ : ℝ≥0), (u₀ : ℝ) < η → ∀ (data : C(ℝ≥0, ℝ)), IsDecaySlice data →
        IsLUB (Set.range (fun r : ℝ≥0 =>
          (1 + (r : ℝ)) ^ 3 * |data r| + (1 + (r : ℝ)) ^ 4 *
            |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r|)) d →
        ∃ h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ), ∃ hb : ∀ n, MemXBall u₀ x₁ (h n),
          h 0 = constantDataField data ∧
          (∀ n, h (n + 1) = linearStepMap (hb n) data) ∧
          (∀ n r, h n (0, r) = data r) := by
  obtain ⟨η, hη, hηpos, hseq⟩ := lemma1 d x₁ hd hx
  refine ⟨η, hη, hηpos, ?_⟩
  intro u₀ hT data hdata hlub
  exact hseq u₀ hT data hdata (fun r => hlub.1 (Set.mem_range_self r))

end XL1
end Christodoulou.Bondi
