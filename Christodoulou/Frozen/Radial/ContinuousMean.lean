/-
# `Christodoulou.Radial.continuous_mean`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Radial.Mean
import Christodoulou.Radial.Provider.ContinuousMean



public section
open Set MeasureTheory
open scoped NNReal
namespace Christodoulou.Radial

theorem continuous_mean (f : C(ℝ≥0, ℝ)) : Continuous (mean f) :=
-- Proof.
  by exact Christodoulou.Radial.Provider.continuous_mean



end Christodoulou.Radial

