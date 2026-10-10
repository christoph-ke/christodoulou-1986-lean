/-
# `Christodoulou.Bondi.continuous_derivLinearStep`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
import Christodoulou.Bondi.Provider.ContinuousDerivLinearStep



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem continuous_derivLinearStep {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0)) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => derivLinearStep hH data hdata p.1 p.2) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.continuous_derivLinearStep



end Christodoulou.Bondi

