/-
# `Christodoulou.Bondi.radialDerivative`

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

/-- The radial derivative within [0, ∞) (one-sided at the centre, as in `MemXBall`). -/
@[expose] noncomputable def radialDerivative (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u r : ℝ≥0) : ℝ :=
  derivWithin (fun z : ℝ => H (u, z.toNNReal)) (Ici 0) r

end Christodoulou.Bondi
