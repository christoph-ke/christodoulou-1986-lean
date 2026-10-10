/-
# `Christodoulou.Bondi.radialDerivative_weighted_iff_printed`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.Provider.RadialDerivativeWeightedIffPrinted



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem radialDerivative_weighted_iff_printed {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) :
    (∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
        |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ)) ↔
      ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
        |radialDerivative H u r| ≤ C * (r : ℝ) ^ (-4 : ℤ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.radialDerivative_weighted_iff_printed



end Christodoulou.Bondi

