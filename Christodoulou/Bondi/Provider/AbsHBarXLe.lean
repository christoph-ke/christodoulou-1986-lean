module
public import Christodoulou.Frozen.Bondi.HBarX
public import Christodoulou.Frozen.Bondi.MemXBall
import Christodoulou.Bondi.CoefficientRegularity



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem abs_hBarX_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H := by assumption) {u r : ℝ≥0} : |hBarX u₀ H u r| ≤ x / (1 + (r : ℝ)) :=
  XCoef.abs_hBarX_le hH u r

end Christodoulou.Bondi.Provider
