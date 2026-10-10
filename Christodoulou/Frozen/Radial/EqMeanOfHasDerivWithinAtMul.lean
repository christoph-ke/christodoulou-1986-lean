/-
# `Christodoulou.Radial.eq_mean_of_hasDerivWithinAt_mul`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Radial.Mean
import Christodoulou.Radial.Provider.EqMeanOfHasDerivWithinAtMul



public section
open Set MeasureTheory
open scoped NNReal
namespace Christodoulou.Radial

theorem eq_mean_of_hasDerivWithinAt_mul (f φ : C(ℝ≥0, ℝ))
    (hφ : ∀ r : ℝ≥0, HasDerivWithinAt (fun s : ℝ => s * φ (Real.toNNReal s)) (f r)
      (Ici 0) (r : ℝ)) :
    ⇑φ = mean f :=
-- Proof.
  by exact Christodoulou.Radial.Provider.eq_mean_of_hasDerivWithinAt_mul



end Christodoulou.Radial

