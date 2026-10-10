/-
# `Christodoulou.Bondi.IsClassicalSolution`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.G
public import Christodoulou.Frozen.Bondi.GBar
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.CompactOpen



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- A classical solution of the nonlinear evolution equation (3.13) on the strip
`[0, u₀] × [0, ∞)` ([P] p. 343 (3.13); p. 348, Sect. 7, para. 1; Theorem 1):
1. `h` is `C¹` on the closed strip (one-sided derivatives at its edges when `u₀ > 0`);
2. `h = O(r⁻³)` uniformly on the strip: one constant `C`, chosen before `u` and `r`
   (`O(r⁻³)` uniformly in `u` in Theorems 1 and 2, pp. 348, 351; Theorem 3, p. 351), so every
   slice `h(u, ·)`, `u ≤ u₀`, is in the slice class `IsSlice` (theorem
   `IsClassicalSolution.isSlice`) and `g`, `ḡ` are defined;
3. `Dh = (g − ḡ)(h − h̄)/(2r)`, `D = ∂_u − ½ ḡ ∂_r`, at every interior point `0 < u < u₀`, `r > 0`.
Values of `H` for `u > u₀` are not constrained. -/
@[expose] def IsClassicalSolution (u₀ : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) : Prop :=
  ContDiffOn ℝ 1 (fun p : ℝ × ℝ => H (Real.toNNReal p.1, Real.toNNReal p.2))
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) ∧
    (∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, |H (u, r)| ≤ C * (1 + (r : ℝ)) ^ (-3 : ℤ)) ∧
    ∀ u : ℝ≥0, 0 < u → u < u₀ → ∀ (hs : IsSlice (H.curry u)) (r : ℝ≥0), 0 < r →
      deriv (fun v : ℝ => H (Real.toNNReal v, r)) (u : ℝ)
          - 1 / 2 * gBar (H.curry u) hs r * deriv (fun s : ℝ => H (u, Real.toNNReal s)) (r : ℝ)
        = (g (H.curry u) hs r - gBar (H.curry u) hs r) * (H (u, r) - mean (H.curry u) r)
            / (2 * (r : ℝ))

end Christodoulou.Bondi
