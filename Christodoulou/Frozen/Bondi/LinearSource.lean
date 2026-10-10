/-
# `Christodoulou.Bondi.linearSource`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.LinearCoeff
public import Christodoulou.Frozen.Bondi.HBarX



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The source term `f = −(1/2r)(g − ḡ) h̄` of (7.2), [P] p. 354 (`f_n`) and p. 351 (`f`). -/
@[expose] noncomputable def linearSource {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u r : ℝ≥0) : ℝ :=
  -linearCoeff hH u r * hBarX u₀ H u r

end Christodoulou.Bondi
