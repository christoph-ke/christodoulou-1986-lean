/-
# `Christodoulou.Bondi.linearStep_eq_of_isClassicalSolution`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.Provider.LinearStepEqOfIsClassicalSolution



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- Reconstruction for [P] p.351, Theorem 2, via (3.13), (5.1), (7.2). -/
theorem linearStep_eq_of_isClassicalSolution {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (hclass : IsClassicalSolution u₀ H) (u : ℝ≥0) (hu : u ≤ u₀) (r : ℝ≥0) :
    linearStep hH (H.curry 0) u r = H (u, r) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.linearStep_eq_of_isClassicalSolution



end Christodoulou.Bondi

