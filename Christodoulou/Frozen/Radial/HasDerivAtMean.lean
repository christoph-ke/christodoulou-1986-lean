/-
# `Christodoulou.Radial.hasDerivAt_mean`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Radial.Mean
import Christodoulou.Radial.Provider.HasDerivAtMean



public section
open Set MeasureTheory
open scoped NNReal
namespace Christodoulou.Radial

theorem hasDerivAt_mean (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => mean f (Real.toNNReal s))
      ((f r - mean f r) / (r : ℝ)) (r : ℝ) :=
-- Proof.
  by exact Christodoulou.Radial.Provider.hasDerivAt_mean



end Christodoulou.Radial

