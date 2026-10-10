/-
# `Christodoulou.Bondi.IsIncomingRay.antitoneOn_mass`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsClassicalSolutionIsSlice
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.IsIncomingRay
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.Provider.IsIncomingRayAntitoneOnMass



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem IsIncomingRay.antitoneOn_mass {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (hX : MemXBall u₀ x H) {r₀ : ℝ≥0} {u₁ : ℝ} {χ : ℝ → ℝ}
    (hχ : IsIncomingRay hX r₀ u₁ χ) :
    AntitoneOn (fun s : ℝ => mass (H.curry (min (Real.toNNReal s) u₀))
        (hH.isSlice _ (min_le_right _ _)) (Real.toNNReal (χ s))) (Icc 0 u₁) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.IsIncomingRay.antitoneOn_mass



end Christodoulou.Bondi

