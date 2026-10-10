/-
# `Christodoulou.Bondi.derivHBarX`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.HBarX
public import Mathlib.Analysis.Calculus.Deriv.Basic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] noncomputable def derivHBarX {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (_hH : MemXBall u₀ x H) (u r : ℝ≥0) : ℝ :=
  if r = 0 then
    derivWithin (fun s : ℝ => H (min u u₀, Real.toNNReal s)) (Ici 0) 0 / 2
  else (H (min u u₀, r) - hBarX u₀ H u r) / (r : ℝ)

end Christodoulou.Bondi
