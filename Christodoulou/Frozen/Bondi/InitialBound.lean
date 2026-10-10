/-
# `Christodoulou.Bondi.InitialBound`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Radial.Mean
public import Mathlib.Analysis.Calculus.Deriv.Basic



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The weighted data sum of (7.4) is at most d. -/
@[expose] def InitialBound (data : C(ℝ≥0, ℝ)) (d : ℝ) : Prop :=
  ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
    (1 + (r : ℝ)) ^ 4 * |derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) r| ≤ d

end Christodoulou.Bondi
