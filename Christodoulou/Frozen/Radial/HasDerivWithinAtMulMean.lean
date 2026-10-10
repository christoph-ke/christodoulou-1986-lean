/-
# `Christodoulou.Radial.hasDerivWithinAt_mul_mean`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Radial.Mean
import Christodoulou.Radial.Provider.HasDerivWithinAtMulMean



public section
open Set MeasureTheory
open scoped NNReal
namespace Christodoulou.Radial

theorem hasDerivWithinAt_mul_mean (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => s * mean f (Real.toNNReal s)) (f r)
      (Ici 0) (r : ℝ) :=
-- Proof.
  by exact Christodoulou.Radial.Provider.hasDerivWithinAt_mul_mean



end Christodoulou.Radial

