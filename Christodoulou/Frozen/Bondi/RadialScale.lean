/-
# `Christodoulou.Bondi.radialScale`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Radial.Mean



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


@[expose] noncomputable def radialScale (b : ℝ≥0) (h : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun r => h (b * r), h.continuous.comp (continuous_const.mul continuous_id)⟩

end Christodoulou.Bondi
