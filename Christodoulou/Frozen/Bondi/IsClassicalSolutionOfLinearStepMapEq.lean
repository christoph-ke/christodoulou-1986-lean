/-
# `Christodoulou.Bondi.isClassicalSolution_of_linearStepMap_eq`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
import Christodoulou.Bondi.Provider.IsClassicalSolutionOfLinearStepMapEq



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- [P] p. 351, end of the proof of Theorem 1: a field in the `X`-ball that is a fixed point of
the linear step is a classical solution of the nonlinear evolution equation (3.13). For `u₀ = 0`
the conclusion is the degenerate slice case. -/
theorem isClassicalSolution_of_linearStepMap_eq {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (hfix : linearStepMap hH data = H) :
    IsClassicalSolution u₀ H :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.isClassicalSolution_of_linearStepMap_eq



end Christodoulou.Bondi

