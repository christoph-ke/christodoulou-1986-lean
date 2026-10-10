module
public import Christodoulou.Frozen.Bondi.SmallDataG
public import Christodoulou.Frozen.Bondi.TranslatedDataField
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.InitialBound
import Christodoulou.Bondi.Lemma4Proof



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem lemma4 {T : ℝ≥0}
    {x d : ℝ}
    (hx : 0 < x := by assumption)
    (hd : 0 ≤ d := by assumption)
    (hsmall : d ≤ smallDataG x := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hbound : InitialBound data d := by assumption) :
    ∃! h : ℕ → {H : C(ℝ≥0 × ℝ≥0, ℝ) // MemXPrimeBall T x H},
      (h 0).val = translatedDataField T data ∧
      ∀ n, (h (n + 1)).val = linearStepMap (h n).property.1 data :=
  XL4.lemma4 hx hd hsmall data hdata hbound

end Christodoulou.Bondi.Provider
