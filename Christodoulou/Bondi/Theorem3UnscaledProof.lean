module
public import Christodoulou.Frozen.Bondi.SmallDataDelta
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.InitialSize
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Frozen.Bondi.ExistsUniqueContractionRadius
import Christodoulou.Frozen.Bondi.SmallDataDeltaPosAndWitness
import Christodoulou.Frozen.Bondi.ContractionFactorStrictMonoOn
import Christodoulou.Frozen.Bondi.InitialSizeCharacterization
import Christodoulou.Frozen.Bondi.GlobalExistsOfG

/-!
# Theorem 3: the unscaled analytic core

Assemble the author-approved unscaled statement from the sealed contraction radius,
small-data witness, initial-size characterization, and global-existence exports.
The full Theorem 3, including scaling, final mass, and geodesic completeness, remains open.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XT3

/-- Small initial size gives a global classical solution with explicit unscaled decay. -/
theorem theorem3_unscaled : ∃ δ : ℝ, 0 < δ ∧
    (∃ x₁ : ℝ≥0, 0 < x₁ ∧ contractionFactor x₁ = 1 ∧ δ = smallDataDelta x₁) ∧
    ∀ (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data), initialSize data hdata < δ →
      ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), ∃ x : ℝ, 0 < x ∧
        (∀ T : ℝ≥0, IsClassicalSolution T H ∧ MemXPrimeBall T x H) ∧
        (∀ r, H (0, r) = data r) ∧
        ∀ u r : ℝ≥0,
          |H (u, r)| ≤ 8 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
          |radialDerivative H u r| ≤ 16 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ) := by
  obtain ⟨x₁, ⟨hx₁, hs₁⟩, _⟩ := existsUnique_contraction_radius
  obtain ⟨hδ, hwitness⟩ := smallDataDelta_pos_and_witness x₁ hx₁
  refine ⟨smallDataDelta x₁, hδ, ⟨x₁, hx₁, hs₁, rfl⟩, ?_⟩
  intro data hdata hsmall
  obtain ⟨hd, hbound⟩ := initialSize_characterization data hdata
  obtain ⟨x, hx, hxx₁, hG⟩ := hwitness (initialSize data hdata) hd hsmall
  have hq : contractionFactor x < 1 :=
    lt_of_lt_of_eq
      (contractionFactor_strictMonoOn hx.le (NNReal.coe_nonneg x₁) hxx₁) hs₁
  obtain ⟨H, hH⟩ := global_exists_of_G hx hd hG hq data hdata
    ((hbound (initialSize data hdata)).2 le_rfl)
  exact ⟨H, x, hx, hH⟩

end XT3
end Christodoulou.Bondi
