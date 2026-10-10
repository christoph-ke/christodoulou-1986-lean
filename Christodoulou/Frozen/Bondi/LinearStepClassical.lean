/-
# `Christodoulou.Bondi.linearStep_classical`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
public import Christodoulou.Frozen.Bondi.LinearSource
public import Christodoulou.Frozen.Bondi.GBarX
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Christodoulou.Bondi.Provider.LinearStepClassical



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem linearStep_classical {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hu₀ : 0 < u₀)
    (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0)) :
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
-- Proof.
  by exact Christodoulou.Bondi.Provider.linearStep_classical



end Christodoulou.Bondi

