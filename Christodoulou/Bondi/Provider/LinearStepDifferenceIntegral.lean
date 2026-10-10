module
public import Christodoulou.Frozen.Bondi.Characteristic
public import Christodoulou.Frozen.Bondi.DerivLinearStep
public import Christodoulou.Frozen.Bondi.LinearStep
public import Christodoulou.Frozen.Bondi.LinearSource
public import Christodoulou.Frozen.Bondi.LinearCoeff
public import Christodoulou.Frozen.Bondi.GBarX
import Christodoulou.Bondi.StepDifference



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem linearStep_difference_integral {u₀ : ℝ≥0}
    {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {hK : MemXBall u₀ x K}
    {data : C(ℝ≥0, ℝ)}
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0) := by assumption)
    {v : Icc (0 : ℝ) u₀}
    {r : ℝ≥0} :
    let χ := characteristic hH v r
    let b := fun s : ℝ =>
      let u := s.toNNReal
      let ρ := (χ s).toNNReal
      (gBarX hH u ρ - gBarX hK u ρ) / 2 * derivLinearStep hK data hdata u ρ +
        (linearCoeff hH u ρ - linearCoeff hK u ρ) * linearStep hK data u ρ +
        linearSource hH u ρ - linearSource hK u ρ
    linearStep hH data (v : ℝ).toNNReal r - linearStep hK data (v : ℝ).toNNReal r =
      ∫ s in (0 : ℝ)..(v : ℝ),
        exp (∫ t in s..(v : ℝ), linearCoeff hH t.toNNReal (χ t).toNNReal) * b s :=
  XDiff.linearStep_difference_integral hH hK data hdata v r

end Christodoulou.Bondi.Provider
