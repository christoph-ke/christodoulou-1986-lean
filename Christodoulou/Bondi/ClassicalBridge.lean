module
public import Christodoulou.Bondi.Theorem2Helpers
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Frozen.Bondi.EqLinearStepOfHasDerivWithinAt



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XCB

/-- A classical solution with uniform weighted radial derivative decay lies in an X-ball. -/
theorem exists_memXBall_of_isClassicalSolution {u₀ : ℝ≥0}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution u₀ H)
    (hderiv : ∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r| ≤
        C * (1 + (r : ℝ)) ^ (-4 : ℤ)) :
    ∃ x : ℝ, MemXBall u₀ x H := by
  obtain ⟨C, hC⟩ := hH.2.1
  obtain ⟨D, hD⟩ := hderiv
  refine ⟨C + D, XT2H.classical_slice hH, XT2H.classical_radial_continuous hH, ?_⟩
  intro u hu r
  have hw : 0 < 1 + (r : ℝ) := by positivity
  have hv := mul_le_mul_of_nonneg_left (hC u hu r) (pow_pos hw 3).le
  have hd := mul_le_mul_of_nonneg_left (hD u hu r) (pow_pos hw 4).le
  simp only [zpow_neg, zpow_ofNat] at hv hd
  have hv' : (1 + (r : ℝ)) ^ 3 * |H (u, r)| ≤ C := by
    convert hv using 1
    field_simp
  have hd' : (1 + (r : ℝ)) ^ 4 *
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r| ≤ D := by
    convert hd using 1
    field_simp
  exact add_le_add hv' hd'

/-- A classical solution equals its own linear step throughout the closed strip. -/
theorem linearStep_eq_of_isClassicalSolution {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (hclass : IsClassicalSolution u₀ H) (u : ℝ≥0) (hu : u ≤ u₀) (r : ℝ≥0) :
    linearStep hH (H.curry 0) u r = H (u, r) := by
  symm
  exact eq_linearStep_of_hasDerivWithinAt hH (H.curry 0) (q := fun u r => H (u, r)) (fun _ => rfl)
    (fun _ _ _ hc _ ht => XT2H.classical_characteristic_derivative hH hclass hc ht) hu r

end XCB
end Christodoulou.Bondi
