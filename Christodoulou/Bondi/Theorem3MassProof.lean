module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.Theorem3Analytic
public import Christodoulou.Frozen.Bondi.TendstoBondiMassZeroOfDecay
public import Christodoulou.Frozen.Bondi.IsClassicalSolutionIsSlice

/-!
# Theorem 3 with vanishing limiting Bondi mass

The sealed analytic existence theorem supplies the solution and its decay. The sealed
decay limit theorem then gives vanishing Bondi mass, preserving the analytic theorem's
small-data threshold and its witness.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XT3M

/-- The analytic conclusion of Theorem 3, together with Bondi mass tending to zero. -/
theorem theorem3_mass_zero : ∃ δ : ℝ, 0 < δ ∧
    (∃ x₁ : ℝ≥0, 0 < x₁ ∧ contractionFactor x₁ = 1 ∧ δ = smallDataDelta x₁) ∧
    ∀ (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data), scaleInvariantSize data hdata < δ →
      ∃ H : C(ℝ≥0 × ℝ≥0, ℝ),
        (∀ T : ℝ≥0, IsClassicalSolution T H) ∧
        (∀ r, H (0, r) = data r) ∧
        (∃ C : ℝ, ∀ u r : ℝ≥0,
          |H (u, r)| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
          |radialDerivative H u r| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ)) ∧
        ∃ hs : ∀ u : ℝ≥0, IsSlice (H.curry u),
          Tendsto (fun u : ℝ≥0 => bondiMass (H.curry u) (hs u)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hx₁, hsol⟩ := Christodoulou.Bondi.theorem3_analytic
  refine ⟨δ, hδ, hx₁, ?_⟩
  intro data hdata hsmall
  obtain ⟨H, hT, hinit, C, hdecay⟩ := hsol data hdata hsmall
  have hs : ∀ u : ℝ≥0, IsSlice (H.curry u) := fun u =>
    (hT (u + 1)).isSlice u (le_add_of_nonneg_right zero_le_one)
  refine ⟨H, hT, hinit, ⟨C, hdecay⟩, hs, ?_⟩
  exact tendsto_bondiMass_zero_of_decay H hs (fun u r => (hdecay u r).2)

end XT3M
end Christodoulou.Bondi
