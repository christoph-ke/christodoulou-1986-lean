/-
# `Christodoulou.Bondi.hasDerivWithinAt_characteristic`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Characteristic
public import Christodoulou.Frozen.Bondi.LinearCoeff
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Christodoulou.Bondi.Provider.HasDerivWithinAtCharacteristic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem hasDerivWithinAt_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) (r₁ : ℝ≥0) {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    HasDerivWithinAt (fun ρ : ℝ => characteristic hH u₁ (Real.toNNReal ρ) t)
      (exp (∫ s in t..(u₁ : ℝ),
        linearCoeff hH (Real.toNNReal s) (Real.toNNReal (characteristic hH u₁ r₁ s))))
      (Ici 0) (r₁ : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivWithinAt_characteristic



end Christodoulou.Bondi

