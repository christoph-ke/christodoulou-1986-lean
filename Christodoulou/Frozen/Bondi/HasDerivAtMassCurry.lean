/-
# `Christodoulou.Bondi.hasDerivAt_mass_curry`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.Xi
import Christodoulou.Bondi.Provider.HasDerivAtMassCurry



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem hasDerivAt_mass_curry {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution u₀ H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) {C : ℝ}
    (hd : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ))
    (u : ℝ≥0) (hu : 0 < u) (hu₀ : u < u₀) (r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun v : ℝ => mass (H.curry (Real.toNNReal v)) (hs (Real.toNNReal v)) r)
      (1 / 2 * gBar (H.curry u) (hs u) r
          * (2 * π * (gBar (H.curry u) (hs u) r / g (H.curry u) (hs u) r)
            * (H (u, r) - mean (H.curry u) r) ^ 2)
        - π / g (H.curry u) (hs u) r * xi (H.curry u) (hs u) r ^ 2) (u : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivAt_mass_curry



end Christodoulou.Bondi

