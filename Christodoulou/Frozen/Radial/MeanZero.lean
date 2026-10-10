/-
# `Christodoulou.Radial.mean_zero`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Radial.Mean
import Christodoulou.Radial.Provider.MeanZero



public section
open Set MeasureTheory
open scoped NNReal
namespace Christodoulou.Radial

theorem mean_zero (f : C(ℝ≥0, ℝ)) : mean f 0 = f 0 :=
-- Proof.
  by exact Christodoulou.Radial.Provider.mean_zero



end Christodoulou.Radial

