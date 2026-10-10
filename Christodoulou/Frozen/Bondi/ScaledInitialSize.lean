/-
# `Christodoulou.Bondi.scaledInitialSize`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Mathlib.Analysis.Calculus.Deriv.Basic



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi


@[expose] noncomputable def scaledInitialSize (a : ℝ≥0) (_ha : 0 < a) (data : C(ℝ≥0, ℝ))
    (_hdata : IsDecaySlice data) : ℝ :=
  sSup (Set.range (fun r : ℝ≥0 => (1 + (r : ℝ) / (a : ℝ)) ^ 3 * |data r| +
    (1 + (r : ℝ) / (a : ℝ)) ^ 4 *
      |(a : ℝ) * derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) r|))

end Christodoulou.Bondi
