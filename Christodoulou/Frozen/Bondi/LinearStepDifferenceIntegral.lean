/-
# `Christodoulou.Bondi.linearStep_difference_integral`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Characteristic
public import Christodoulou.Frozen.Bondi.DerivLinearStep
public import Christodoulou.Frozen.Bondi.LinearStep
public import Christodoulou.Frozen.Bondi.LinearSource
public import Christodoulou.Frozen.Bondi.LinearCoeff
public import Christodoulou.Frozen.Bondi.GBarX
import Christodoulou.Bondi.Provider.LinearStepDifferenceIntegral



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi

/-- The local (9.27), [P] p. 357, integrated along the characteristic of `H` with zero data at
`u = 0` (as at the end of the proof of Lemma 5, p. 360): the difference of the linear steps of two
fields with the same `C¹` data. -/
theorem linearStep_difference_integral {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (v : Icc (0 : ℝ) u₀) (r : ℝ≥0) :
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
-- Proof.
  by exact Christodoulou.Bondi.Provider.linearStep_difference_integral



end Christodoulou.Bondi

