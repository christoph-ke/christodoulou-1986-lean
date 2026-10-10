/-
# `Christodoulou.Bondi.deriv2GBarX`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.DerivGBarX
public import Christodoulou.Frozen.Bondi.DerivHBarX
public import Christodoulou.Frozen.Bondi.GX



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] noncomputable def deriv2GBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) : ℝ :=
  if r = 0 then
    π / 3 * gX hH u 0 * derivWithin (fun s : ℝ => H (min u u₀, Real.toNNReal s)) (Ici 0) 0 ^ 2
  else -2 * derivGBarX hH u r / (r : ℝ) + 4 * π * gX hH u r * derivHBarX hH u r ^ 2

end Christodoulou.Bondi
