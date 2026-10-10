/-
# `Christodoulou.Bondi.evolution_mean`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.Xi
import Christodoulou.Bondi.Provider.EvolutionMean



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem evolution_mean {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution u₀ H)
    (u : ℝ≥0) (hu : 0 < u) (hu₀ : u < u₀) (hs : IsSlice (H.curry u)) (r : ℝ≥0) (hr : 0 < r) :
    deriv (fun v : ℝ => mean (H.curry (Real.toNNReal v)) r) (u : ℝ)
        - 1 / 2 * gBar (H.curry u) hs r
          * deriv (fun s : ℝ => mean (H.curry u) (Real.toNNReal s)) (r : ℝ)
      = xi (H.curry u) hs r / (2 * (r : ℝ)) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.evolution_mean



end Christodoulou.Bondi

