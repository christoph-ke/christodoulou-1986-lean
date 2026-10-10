/-
# `Christodoulou.Bondi.theorem3_bondi`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.SmallDataDelta
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.ScaleInvariantSize
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.Provider.Theorem3Bondi



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- Global small-data existence: the conclusion of `theorem3_mass_zero` together with Bondi's theorem for
the global solution (M nonincreasing on [0, ∞), tending to M₁ = 0). NOT claimed: the future
timelike and null geodesic completeness (deferred), uniqueness, the differentiability of M. -/
theorem theorem3_bondi : ∃ δ : ℝ, 0 < δ ∧
    (∃ x₁ : ℝ≥0, 0 < x₁ ∧ contractionFactor x₁ = 1 ∧ δ = smallDataDelta x₁) ∧
    ∀ (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data), scaleInvariantSize data hdata < δ →
      ∃ H : C(ℝ≥0 × ℝ≥0, ℝ),
        (∀ T : ℝ≥0, IsClassicalSolution T H) ∧
        (∀ r, H (0, r) = data r) ∧
        (∃ C : ℝ, ∀ u r : ℝ≥0,
          |H (u, r)| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
          |radialDerivative H u r| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ)) ∧
        ∃ hs : ∀ u : ℝ≥0, IsSlice (H.curry u),
          Antitone (fun u : ℝ≥0 => bondiMass (H.curry u) (hs u)) ∧
          Tendsto (fun u : ℝ≥0 => bondiMass (H.curry u) (hs u)) atTop (𝓝 0) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.theorem3_bondi



end Christodoulou.Bondi

