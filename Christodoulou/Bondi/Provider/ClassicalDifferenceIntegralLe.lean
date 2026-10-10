module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Radial.Mean
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Christodoulou.Bondi.DifferenceInequality



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem classical_difference_integral_le {u₀ : ℝ≥0}
    {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H := by assumption)
    (hK : MemXBall u₀ x K := by assumption)
    (hcH : IsClassicalSolution u₀ H := by assumption)
    (hcK : IsClassicalSolution u₀ K := by assumption)
    (hdata : ∀ r : ℝ≥0, H (0, r) = K (0, r) := by assumption)
    {v : ℝ≥0}
    (hv : v ≤ u₀ := by assumption)
    {φ : ℝ → ℝ}
    (hφ : IntervalIntegrable φ volume 0 (v : ℝ) := by assumption)
    (hbound : ∀ s : ℝ≥0, s ≤ v → ∀ r : ℝ≥0,
      (1 + (r : ℝ)) ^ 3 * |H (s, r) - K (s, r)| ≤ φ s := by assumption)
    {r : ℝ≥0} :
    (1 + (r : ℝ)) ^ 3 * |H (v, r) - K (v, r)| ≤
      exp (π * x ^ 2 / 12 * (u₀ : ℝ)) * (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)) *
        ∫ s in (0 : ℝ)..(v : ℝ), φ s :=
  XDI.classical_difference_integral_le hH hK hcH hcK hdata v hv φ hφ hbound r

end Christodoulou.Bondi.Provider
