/-
# `Christodoulou.Bondi.linearStep_zero`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.Provider.LinearStepZero



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The linear step takes the given data at `u = 0` ([P] p. 348). -/
theorem linearStep_zero {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (h₀ : C(ℝ≥0, ℝ)) (r : ℝ≥0) : linearStep hH h₀ 0 r = h₀ r :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.linearStep_zero



end Christodoulou.Bondi

