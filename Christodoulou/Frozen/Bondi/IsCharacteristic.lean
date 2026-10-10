/-
# `Christodoulou.Bondi.IsCharacteristic`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.CharField
public import Mathlib.Analysis.Calculus.Deriv.Basic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] def IsCharacteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) (r₁ : ℝ≥0) (χ : ℝ → ℝ) : Prop :=
  χ u₁ = r₁ ∧ ∀ t ∈ Icc (0 : ℝ) (u₁ : ℝ),
    HasDerivWithinAt χ (charField hH t (χ t)) (Icc 0 (u₁ : ℝ)) t

end Christodoulou.Bondi
