module
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.YPrimeDistLe
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.Lemma5Proof



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem lemma5 {T : ℝ≥0}
    {x : ℝ}
    {x₁ : ℝ≥0}
    (hroot : contractionFactor x₁ = 1 := by assumption)
    (hx : 0 < x := by assumption)
    (hxx₁ : x < x₁ := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ) := by assumption)
    (hb : ∀ n, MemXPrimeBall T x (h n) := by assumption)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n).1 data := by assumption) :
    0 ≤ contractionFactor x ∧ contractionFactor x < 1 ∧
      ∀ n : ℕ, ∀ y : ℝ, YPrimeDistLe T (h (n + 1)) (h n) y →
        YPrimeDistLe T (h (n + 2)) (h (n + 1)) (contractionFactor x * y) :=
  XL5.lemma5 x₁ hroot hx hxx₁ data hdata h hb hstep

end Christodoulou.Bondi.Provider
