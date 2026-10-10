/-
# `Christodoulou.Bondi.isPicardLindelof_charField`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.CharField
public import Mathlib.Analysis.ODE.PicardLindelof
import Christodoulou.Bondi.Provider.IsPicardLindelofCharField



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The characteristic field satisfies the hypotheses of Mathlib's Picard–Lindelöf theorem on the
whole time interval `[0, u₀]`, for every initial time `t₀`, every centre `z₀` and every initial
radius `ρ`: speed bound `1/2`, spatial Lipschitz constant `π x²/12`, field radius `ρ + u₀/2`. -/
theorem isPicardLindelof_charField {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (t₀ : Icc (0 : ℝ) u₀) (z₀ : ℝ) (ρ : ℝ≥0) :
    IsPicardLindelof (charField hH) t₀ z₀ (ρ + u₀ / 2) ρ (1 / 2)
      (Real.toNNReal (π / 12 * x ^ 2)) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.isPicardLindelof_charField



end Christodoulou.Bondi

