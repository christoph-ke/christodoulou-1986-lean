module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXBall
import Christodoulou.Frozen.Bondi.ClassicalDifferenceIntegralLe
import Christodoulou.Bondi.Theorem2Helpers

/-!
# Uniqueness in a common X-ball

Two classical solutions with equal initial data in a common X-ball agree on the closed strip.
The proof consumes the frozen homogeneous integral inequality and the Picard majorant helper.
-/

public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XU2

/-- Classical solutions in a common X-ball with equal initial data agree on the closed strip. -/
theorem theorem2_of_memXBall {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (hcH : IsClassicalSolution u₀ H) (hcK : IsClassicalSolution u₀ K)
    (hdata : ∀ r : ℝ≥0, H (0, r) = K (0, r)) :
    ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, H (u, r) = K (u, r) := by
  let F := fun (u r : ℝ≥0) => (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)|
  have hnonneg (u : ℝ≥0) (_hu : u ≤ u₀) (r : ℝ≥0) : 0 ≤ F u r := by
    dsimp [F]
    positivity
  have hbound (u : ℝ≥0) (hu : u ≤ u₀) (r : ℝ≥0) : F u r ≤ 2 * x := by
    have hbH := hH.2.2 u hu r
    have hbK := hK.2.2 u hu r
    have hHval : (1 + (r : ℝ)) ^ 3 * |H (u, r)| ≤ x :=
      (le_add_of_nonneg_right (by positivity)).trans hbH
    have hKval : (1 + (r : ℝ)) ^ 3 * |K (u, r)| ≤ x :=
      (le_add_of_nonneg_right (by positivity)).trans hbK
    calc
      F u r ≤ (1 + (r : ℝ)) ^ 3 * (|H (u, r)| + |K (u, r)|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
      _ ≤ 2 * x := by
        rw [mul_add]
        linarith only [hHval, hKval]
  have hz := XT2H.majorant_picard_zero hnonneg hbound
    (fun v hv φ hφ hb r =>
      Christodoulou.Bondi.classical_difference_integral_le hH hK hcH hcK hdata v hv φ
        (hφ.intervalIntegrable_of_Icc v.coe_nonneg) hb r)
  intro u hu r
  have hw : (1 + (r : ℝ)) ^ 3 ≠ 0 := ne_of_gt (by positivity)
  have he : |H (u, r) - K (u, r)| = 0 := (mul_eq_zero.mp (hz u hu r)).resolve_left hw
  exact sub_eq_zero.mp (abs_eq_zero.mp he)

end XU2
end Christodoulou.Bondi
