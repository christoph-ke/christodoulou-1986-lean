/-
# `Christodoulou.Bondi.IsIncomingRay`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.CharField



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] def IsIncomingRay {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (r₀ : ℝ≥0) (u₁ : ℝ) (χ : ℝ → ℝ) : Prop :=
  u₁ ∈ Icc (0 : ℝ) u₀ ∧ χ 0 = r₀ ∧
    (∀ t ∈ Icc (0 : ℝ) u₁, 0 ≤ χ t ∧ HasDerivWithinAt χ (charField hH t (χ t)) (Icc 0 u₁) t) ∧
    (u₁ = u₀ ∨ χ u₁ = 0)

end Christodoulou.Bondi
