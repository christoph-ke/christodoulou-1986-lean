module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.GBarX
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Christodoulou.Bondi.ClassicalUpgrade



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem classical_upgrade_of_characteristics {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    (hu₀ : 0 < u₀ := by assumption)
    {F : C(ℝ≥0 × ℝ≥0, ℝ)}
    {Q B : ℝ≥0 → ℝ≥0 → ℝ}
    (hQ : ContinuousOn (fun p : ℝ × ℝ => Q (Real.toNNReal p.1) (Real.toNNReal p.2))
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) := by assumption)
    (hB : ContinuousOn (fun p : ℝ × ℝ => B (Real.toNNReal p.1) (Real.toNNReal p.2))
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) := by assumption)
    (hrad : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      HasDerivWithinAt (fun s : ℝ => F (u, Real.toNNReal s)) (Q u r) (Ici 0) (r : ℝ) :=
        by assumption)
    (hcurve : ∀ (v : Icc (0 : ℝ) u₀) (r : ℝ≥0) (χ : ℝ → ℝ),
      IsCharacteristic hH v r χ → ∀ t ∈ Icc 0 (v : ℝ),
        HasDerivWithinAt (fun s : ℝ => F (Real.toNNReal s, Real.toNNReal (χ s)))
          (B (Real.toNNReal t) (Real.toNNReal (χ t))) (Icc 0 (v : ℝ)) t := by assumption) :
    (∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      HasDerivWithinAt (fun s : ℝ => F (Real.toNNReal s, r))
        (B u r + gBarX hH u r / 2 * Q u r) (Icc 0 (u₀ : ℝ)) (u : ℝ)) ∧
    ContinuousOn
      (fun p : ℝ × ℝ => derivWithin (fun s : ℝ => F (Real.toNNReal s, Real.toNNReal p.2))
        (Icc 0 (u₀ : ℝ)) p.1) (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => F (Real.toNNReal p.1, Real.toNNReal p.2))
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) :=
  XCl.classical_upgrade_of_characteristics hH hu₀ F Q B hQ hB hrad hcurve

end Christodoulou.Bondi.Provider
