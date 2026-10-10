module
public import Christodoulou.Frozen.Bondi.LinearStepYPrimeLipschitz
public import Christodoulou.Frozen.Bondi.ContractionFactorStrictMonoOn
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Mathlib.Tactic.Positivity

/-!
# Lemma 5: contraction of the iterates in Y′

The contraction factor lies in `[0, 1)` below its root. The frozen weighted Lipschitz
estimate then gives the contraction of successive iterates on every finite strip.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

/-- Lemma 5: below the root of the contraction factor, the iterates contract in Y′. -/
theorem XL5.lemma5 {T : ℝ≥0} {x : ℝ} (x₁ : ℝ≥0)
    (hroot : contractionFactor x₁ = 1) (hx : 0 < x) (hxx₁ : x < x₁)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ)) (hb : ∀ n, MemXPrimeBall T x (h n))
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n).1 data) :
    0 ≤ contractionFactor x ∧ contractionFactor x < 1 ∧
      ∀ n : ℕ, ∀ y : ℝ, YPrimeDistLe T (h (n + 1)) (h n) y →
        YPrimeDistLe T (h (n + 2)) (h (n + 1)) (contractionFactor x * y) := by
  have hs_nonneg : 0 ≤ contractionFactor x := by
    unfold contractionFactor
    positivity
  have hs_lt : contractionFactor x < 1 := by
    calc
      contractionFactor x < contractionFactor x₁ :=
        contractionFactor_strictMonoOn hx.le x₁.coe_nonneg hxx₁
      _ = 1 := hroot
  refine ⟨hs_nonneg, hs_lt, ?_⟩
  intro n y hy
  have hSK : MemXPrimeBall T x (linearStepMap (hb n).1 data) := by
    rw [← hstep n]
    exact hb (n + 1)
  have hLip := linearStep_yPrime_lipschitz (hb (n + 1)) (hb n) data hdata.1.1 hSK hy
  simpa only [← hstep n, ← hstep (n + 1)] using hLip

end Christodoulou.Bondi
