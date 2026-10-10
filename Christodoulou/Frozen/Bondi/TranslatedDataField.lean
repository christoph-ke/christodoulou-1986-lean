/-
# `Christodoulou.Bondi.translatedDataField`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Radial.Mean



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- The 0th iterate (9.2), h₀(u, r) = h(0, r + u/2), on [0, T] and time-clamped beyond it. -/
@[expose] noncomputable def translatedDataField (T : ℝ≥0) (data : C(ℝ≥0, ℝ)) : C(ℝ≥0 × ℝ≥0, ℝ) :=
  ⟨fun p => data (p.2 + min p.1 T / 2), by fun_prop⟩

end Christodoulou.Bondi
