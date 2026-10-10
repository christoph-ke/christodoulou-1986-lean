module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
public import Christodoulou.Frozen.Bondi.LinearSource
public import Christodoulou.Frozen.Bondi.GBarX
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Christodoulou.Frozen.Bondi.ClassicalUpgradeOfCharacteristics
import Christodoulou.Frozen.Bondi.HasDerivWithinAtLinearStep
import Christodoulou.Frozen.Bondi.ContinuousDerivLinearStep
import Christodoulou.Frozen.Bondi.ContinuousLinearStep
import Christodoulou.Frozen.Bondi.IsCharacteristicHasDerivWithinAtLinearStep
import Christodoulou.Frozen.Bondi.ContinuousDerivGBarX
import Christodoulou.Frozen.Bondi.LinearStepMap
import Christodoulou.Bondi.LinearStepBasic

/-!
# Classical regularity of the linear step

Apply the frozen classical upgrade to the continuous linear step, its continuous radial
derivative, and the continuous source `aS + f` supplied by the characteristic equation.
-/

public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi

/-- The linear step solves (7.2) classically on the strip, including its boundary. -/
theorem XCl2.linearStep_classical {u₀ : ℝ≥0} {x : ℝ}
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
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) := by
  let Q := derivLinearStep hH data hdata
  let B := fun u r => linearCoeff hH u r * linearStep hH data u r + linearSource hH u r
  have ha : Continuous (fun p : ℝ≥0 × ℝ≥0 => linearCoeff hH p.1 p.2) :=
    continuous_const.mul (continuous_derivGBarX hH)
  have hf : Continuous (fun p : ℝ≥0 × ℝ≥0 => linearSource hH p.1 p.2) :=
    ha.neg.mul (XStep.continuous_hBarX u₀ H)
  have hB : Continuous (fun p : ℝ≥0 × ℝ≥0 => B p.1 p.2) :=
    (ha.mul (continuous_linearStep hH data)).add hf
  have hnn : Continuous (fun p : ℝ × ℝ => (p.1.toNNReal, p.2.toNNReal)) :=
    (continuous_real_toNNReal.comp continuous_fst).prodMk
      (continuous_real_toNNReal.comp continuous_snd)
  have hs := classical_upgrade_of_characteristics hH hu₀ (linearStepMap hH data) Q B
    (((continuous_derivLinearStep hH data hdata).comp hnn).continuousOn)
    ((hB.comp hnn).continuousOn)
    (fun u _ r => hasDerivWithinAt_linearStep hH data hdata u r)
    (fun _ _ _ hχ _ ht => hχ.hasDerivWithinAt_linearStep data ht)
  refine ⟨?_, hs.2.1, hs.2.2⟩
  intro u hu r
  simpa only [linearStepMap, ContinuousMap.coe_mk, Q, B, add_assoc, add_left_comm,
    add_comm] using hs.1 u hu r

end Christodoulou.Bondi
