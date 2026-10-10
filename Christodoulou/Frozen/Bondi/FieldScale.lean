/-
# `Christodoulou.Bondi.fieldScale`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Radial.Mean



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


@[expose] noncomputable def fieldScale (b : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) :
    C(ℝ≥0 × ℝ≥0, ℝ) :=
  ⟨fun p => H (b * p.1, b * p.2), H.continuous.comp
    ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))⟩

end Christodoulou.Bondi
