/-
# `Christodoulou.Bondi.exists_memXBall_of_isClassicalSolution_printed`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.MemXBall
import Christodoulou.Bondi.Provider.ExistsMemXBallOfIsClassicalSolutionPrinted



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- A classical solution with the printed ∂_r h = O(r⁻⁴), uniformly in u, lies in an X-ball, so
the X-ball hypothesis of the later solution and mass results is available under the printed
hypothesis. -/
theorem exists_memXBall_of_isClassicalSolution_printed {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H)
    (hderiv : ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
      |radialDerivative H u r| ≤ C * (r : ℝ) ^ (-4 : ℤ)) :
    ∃ x : ℝ, MemXBall u₀ x H :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.exists_memXBall_of_isClassicalSolution_printed



end Christodoulou.Bondi

