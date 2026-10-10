module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.Xi
import Christodoulou.Bondi.MassEvolution



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem hasDerivAt_mass_curry {u₀ : ℝ≥0}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H := by assumption)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v) := by assumption)
    {C : ℝ}
    (hd : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ) := by assumption)
    {u : ℝ≥0}
    (hu : 0 < u := by assumption)
    (hu₀ : u < u₀ := by assumption)
    {r : ℝ≥0}
    (hr : 0 < r := by assumption) :
    HasDerivAt (fun v : ℝ => mass (H.curry (Real.toNNReal v)) (hs (Real.toNNReal v)) r)
      (1 / 2 * gBar (H.curry u) (hs u) r
          * (2 * π * (gBar (H.curry u) (hs u) r / g (H.curry u) (hs u) r)
            * (H (u, r) - mean (H.curry u) r) ^ 2)
        - π / g (H.curry u) (hs u) r * xi (H.curry u) (hs u) r ^ 2) (u : ℝ) :=
  XME.hasDerivAt_mass_curry hH hs hd u hu hu₀ r hr

end Christodoulou.Bondi.Provider
