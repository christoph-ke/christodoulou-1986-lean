module
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.InitialBound
import Christodoulou.Bondi.WeightedTransport



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem linearStep_prime_bound {T : ℝ≥0}
    {x d : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXPrimeBall T x H := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hd : 0 ≤ d := by assumption)
    (hbound : InitialBound data d := by assumption) :
    MemXPrimeBall T
      ((2 + π / 6 * x ^ 2) * exp (4 * π / 3 * x ^ 2) * (d + π / 8 * x ^ 3))
      (linearStepMap hH.1 data) :=
  XWT.linearStep_prime_bound hH data hdata hd hbound

end Christodoulou.Bondi.Provider
