/-
# `Christodoulou.Bondi.lemma5`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.YPrimeDistLe
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.Provider.Lemma5



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- **Lemma 5**, [P] p. 357: for x < x₁ the iterates contract in Y′. -/
theorem lemma5 {T : ℝ≥0} {x : ℝ} (x₁ : ℝ≥0)
    (hroot : contractionFactor x₁ = 1) (hx : 0 < x) (hxx₁ : x < x₁)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ)) (hb : ∀ n, MemXPrimeBall T x (h n))
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n).1 data) :
    0 ≤ contractionFactor x ∧ contractionFactor x < 1 ∧
      ∀ n : ℕ, ∀ y : ℝ, YPrimeDistLe T (h (n + 1)) (h n) y →
        YPrimeDistLe T (h (n + 2)) (h (n + 1)) (contractionFactor x * y) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.lemma5



end Christodoulou.Bondi

