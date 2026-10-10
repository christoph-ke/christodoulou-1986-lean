module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
import Christodoulou.Frozen.Bondi.ExistsMemXBallOfIsClassicalSolution
import Christodoulou.Frozen.Bondi.Theorem2OfMemXBall
import Christodoulou.Bondi.Theorem2Helpers



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XT2


theorem theorem2 {u₀ : ℝ≥0} {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hcH : IsClassicalSolution u₀ H) (hcK : IsClassicalSolution u₀ K)
    (hHderiv : ∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r| ≤
        C * (1 + (r : ℝ)) ^ (-4 : ℤ))
    (hKderiv : ∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |derivWithin (fun s : ℝ => K (u, s.toNNReal)) (Ici 0) r| ≤
        C * (1 + (r : ℝ)) ^ (-4 : ℤ))
    (hdata : ∀ r : ℝ≥0, H (0, r) = K (0, r)) :
    ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, H (u, r) = K (u, r) := by
  obtain ⟨x, hx⟩ := exists_memXBall_of_isClassicalSolution hcH hHderiv
  obtain ⟨y, hy⟩ := exists_memXBall_of_isClassicalSolution hcK hKderiv
  exact theorem2_of_memXBall (XT2H.memXBall_mono_radius hx (le_max_left x y))
    (XT2H.memXBall_mono_radius hy (le_max_right x y)) hcH hcK hdata

end XT2
end Christodoulou.Bondi
