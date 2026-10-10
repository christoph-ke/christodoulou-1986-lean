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

theorem initial_memXBall {u₀ : ℝ≥0}
    {d x : ℝ}
    (hd : 0 ≤ d := by assumption)
    (hx : 2 * d < x := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d := by assumption) :
    MemXBall u₀ x (constantDataField data) :=
  XIt.initial_memXBall hd hx data hdata hbound

end Christodoulou.Bondi.Provider
