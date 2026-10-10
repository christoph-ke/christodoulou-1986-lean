module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
public import Christodoulou.Frozen.Bondi.LinearSource
public import Christodoulou.Frozen.Bondi.GBarX
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Christodoulou.Bondi.LinearStepClassicalProof



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem linearStep_classical {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    (hu₀ : 0 < u₀ := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) := by assumption) :
    (∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      HasDerivWithinAt (fun s : ℝ => linearStep hH data (Real.toNNReal s) r)
        (gBarX hH u r / 2 * derivLinearStep hH data hdata u r +
          linearCoeff hH u r * linearStep hH data u r + linearSource hH u r)
        (Icc 0 (u₀ : ℝ)) (u : ℝ)) ∧
    ContinuousOn
      (fun p : ℝ × ℝ => derivWithin
        (fun s : ℝ => linearStep hH data (Real.toNNReal s) (Real.toNNReal p.2))
        (Icc 0 (u₀ : ℝ)) p.1) (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) ∧
    ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => linearStep hH data (Real.toNNReal p.1) (Real.toNNReal p.2))
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) :=
  XCl2.linearStep_classical hH hu₀ data hdata

end Christodoulou.Bondi.Provider
