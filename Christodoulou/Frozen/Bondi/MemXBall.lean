/-
# `Christodoulou.Bondi.MemXBall`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.IsSlice
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.CompactOpen



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `H` lies in the closed ball of radius `x` of the space `X` of [P] (7.1), p. 348, on the strip
`[0, u₀] × [0, ∞)`: each slice `H(u, ·)` is `C¹` on `[0, ∞)` (one-sided at `r = 0`), its partial
derivative `∂_r H` (the derivative within `[0, ∞)` of the real lift) is continuous on the closed
strip, and `(1 + r)³ |H| + (1 + r)⁴ |∂_r H| ≤ x` there (the printed sum norm). No evolution
equation is assumed: this is the class of the iterates `h_n` of (7.2)–(7.3) (Lemma 1). Values of
`H` for `u > u₀` are not constrained. -/
@[expose] def MemXBall (u₀ : ℝ≥0) (x : ℝ) (H : C(ℝ≥0 × ℝ≥0, ℝ)) : Prop :=
  (∀ u : ℝ≥0, u ≤ u₀ → ContDiffOn ℝ 1 (fun s : ℝ => H (u, Real.toNNReal s)) (Ici 0)) ∧
    ContinuousOn
      (fun p : ℝ × ℝ => derivWithin (fun s : ℝ => H (Real.toNNReal p.1, Real.toNNReal s))
        (Ici 0) p.2)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) ∧
    ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      (1 + (r : ℝ)) ^ 3 * |H (u, r)|
        + (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => H (u, Real.toNNReal s)) (Ici 0) r| ≤ x

end Christodoulou.Bondi
