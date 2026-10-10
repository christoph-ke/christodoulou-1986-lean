/-
# `Christodoulou.Bondi.IsSlice`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Radial.Mean
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Asymptotics.Defs



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The slice class used for `g`, `ḡ` and `m`: `h ∈ C¹[0,∞)` and `h = O(r⁻³)` as `r → ∞`
(the first two conditions of the data class of [P] Theorem 1, p. 348). -/
@[expose] def IsSlice (h : C(ℝ≥0, ℝ)) : Prop :=
  ContDiffOn ℝ 1 (fun s : ℝ => h (Real.toNNReal s)) (Ici 0) ∧
  (fun s : ℝ => h (Real.toNNReal s)) =O[atTop] (fun s : ℝ => s ^ (-3 : ℤ))

end Christodoulou.Bondi
