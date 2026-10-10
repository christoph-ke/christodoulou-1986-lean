module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.G
public import Christodoulou.Frozen.Bondi.Xi
import Christodoulou.Bondi.MassCharacteristic



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem hasDerivAt_mass_characteristic {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H := by assumption)
    (hX : MemXBall u₀ x H := by assumption)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v) := by assumption)
    {u₁ : Icc (0 : ℝ) u₀}
    {r₁ : ℝ≥0}
    {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hX u₁ r₁ χ := by assumption)
    {t : ℝ}
    (ht : 0 < t := by assumption)
    (htu : t < u₁ := by assumption) :
    HasDerivAt (fun s : ℝ => mass (H.curry (Real.toNNReal s)) (hs (Real.toNNReal s))
        (Real.toNNReal (χ s)))
      (-(π / g (H.curry (Real.toNNReal t)) (hs (Real.toNNReal t)) (Real.toNNReal (χ t)))
        * xi (H.curry (Real.toNNReal t)) (hs (Real.toNNReal t)) (Real.toNNReal (χ t)) ^ 2) t :=
  XMC.hasDerivAt_mass_characteristic hH hX hs hχ ht htu

end Christodoulou.Bondi.Provider
