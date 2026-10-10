module
public import Christodoulou.Frozen.Bondi.ConstantDataField
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.IterationBounds



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem memXBall_constantDataField {u₀ : ℝ≥0}
    {d : ℝ}
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d := by assumption) :
    MemXBall u₀ d (constantDataField data) :=
  XIt.memXBall_constantDataField u₀ d data hdata hbound

end Christodoulou.Bondi.Provider
