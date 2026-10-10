/-
# `Christodoulou.Bondi.linearStep_deriv_bound`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
public import Christodoulou.Frozen.Bondi.StepDerivBound
import Christodoulou.Bondi.Provider.LinearStepDerivBound



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem linearStep_deriv_bound {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0)) (d : ℝ)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d)
    (u r : ℝ≥0) :
    (1 + (r : ℝ)) ^ 4 * |derivLinearStep hH data hdata u r| ≤
      stepDerivBound x d u₀ :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.linearStep_deriv_bound



end Christodoulou.Bondi

