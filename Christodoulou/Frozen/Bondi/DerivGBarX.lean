/-
# `Christodoulou.Bondi.derivGBarX`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.GX
public import Christodoulou.Frozen.Bondi.GBarX



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `∂_r ḡ(u, r) = (g − ḡ)/r` for `r > 0` ((3.8) applied to `g`), with the value `0` at the centre
written explicitly. -/
@[expose] noncomputable def derivGBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) : ℝ :=
  if r = 0 then 0 else (gX hH u r - gBarX hH u r) / (r : ℝ)

end Christodoulou.Bondi
