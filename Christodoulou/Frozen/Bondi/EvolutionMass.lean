/-
# `Christodoulou.Bondi.evolution_mass`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.Xi
import Christodoulou.Bondi.Provider.EvolutionMass



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- [P] (4.6) in the printed form D m = −(π/g) ξ², D = ∂_u − ½ ḡ ∂_r (as `evolution_mean`). -/
theorem evolution_mass {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution u₀ H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) {C : ℝ}
    (hd : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ))
    (u : ℝ≥0) (hu : 0 < u) (hu₀ : u < u₀) (r : ℝ≥0) (hr : 0 < r) :
    deriv (fun v : ℝ => mass (H.curry (Real.toNNReal v)) (hs (Real.toNNReal v)) r) (u : ℝ)
        - 1 / 2 * gBar (H.curry u) (hs u) r
          * deriv (fun s : ℝ => mass (H.curry u) (hs u) (Real.toNNReal s)) (r : ℝ)
      = -(π / g (H.curry u) (hs u) r) * xi (H.curry u) (hs u) r ^ 2 :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.evolution_mass



end Christodoulou.Bondi

