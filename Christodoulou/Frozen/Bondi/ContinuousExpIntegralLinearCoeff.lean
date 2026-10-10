/-
# `Christodoulou.Bondi.continuous_exp_integral_linearCoeff`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Characteristic
public import Christodoulou.Frozen.Bondi.LinearCoeff
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Christodoulou.Bondi.Provider.ContinuousExpIntegralLinearCoeff



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem continuous_exp_integral_linearCoeff {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ × Icc (0 : ℝ) u₀ × ℝ≥0 =>
      exp (∫ s in p.1..(p.2.1 : ℝ),
        linearCoeff hH (Real.toNNReal s) (Real.toNNReal (characteristic hH p.2.1 p.2.2 s)))) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.continuous_exp_integral_linearCoeff



end Christodoulou.Bondi

