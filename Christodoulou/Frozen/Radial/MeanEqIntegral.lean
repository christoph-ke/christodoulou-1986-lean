/-
# `Christodoulou.Radial.mean_eq_integral`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Radial.Mean
import Christodoulou.Radial.Provider.MeanEqIntegral



public section
open Set MeasureTheory
open scoped NNReal
namespace Christodoulou.Radial

theorem mean_eq_integral (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) (hr : 0 < r) :
    mean f r = (r : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(r : ℝ), f (Real.toNNReal s) :=
-- Proof.
  by exact Christodoulou.Radial.Provider.mean_eq_integral



end Christodoulou.Radial

