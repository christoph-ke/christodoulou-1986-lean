module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Frozen.Bondi.ContinuousGBarX
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integral identities for characteristics

The fundamental theorem of calculus gives the terminal and initial integral forms of (5.1)
for every characteristic, including the endpoints and the zero-length time interval.
-/

public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi

private theorem integral_charField_eq_sub {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀}
    {r₁ : ℝ≥0} {χ : ℝ → ℝ} (hχ : IsCharacteristic hH u₁ r₁ χ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ u₁) :
    -(1 / 2) * ∫ s in a..b, gBarX hH (Real.toNNReal s) (Real.toNNReal (χ s)) =
      χ b - χ a := by
  have hsub : Icc a b ⊆ Icc 0 (u₁ : ℝ) := Icc_subset_Icc ha hb
  have hc : ContinuousOn χ (Icc a b) :=
    (HasDerivWithinAt.continuousOn hχ.2).mono hsub
  have hg : ContinuousOn
      (fun s => gBarX hH (Real.toNNReal s) (Real.toNNReal (χ s))) (Icc a b) :=
    (continuous_gBarX hH).comp_continuousOn
      (f := fun s : ℝ => (Real.toNNReal s, Real.toNNReal (χ s)))
      (continuous_real_toNNReal.continuousOn.prodMk
        (continuous_real_toNNReal.comp_continuousOn hc))
  calc
    -(1 / 2) * ∫ s in a..b, gBarX hH (Real.toNNReal s) (Real.toNNReal (χ s)) =
        ∫ s in a..b, charField hH s (χ s) := by
      exact (intervalIntegral.integral_const_mul (-(1 / 2))
        (fun s => gBarX hH (Real.toNNReal s) (Real.toNNReal (χ s)))).symm
    _ = χ b - χ a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
      · intro s hs
        exact (hχ.2 s (hsub ⟨hs.1.le, hs.2.le⟩)).hasDerivAt
          (Icc_mem_nhds (ha.trans_lt hs.1) (hs.2.trans_le hb))
      · exact (hg.const_mul (-(1 / 2))).intervalIntegrable_of_Icc hab

/-- The integral form of (5.1) from the terminal point ([P] p. 354:
`r(u) = r₁ + ½ ∫_u^{u₁} ḡ(u', r(u')) du'`), with the coefficient of the slice at time `s`. -/
theorem XChar.eq_add_integral {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    χ t = r₁ + 1 / 2 * ∫ s in t..(u₁ : ℝ), gBarX hH (Real.toNNReal s)
      (Real.toNNReal (χ s)) := by
  have hi := integral_charField_eq_sub hχ ht.1 ht.2 le_rfl
  rw [hχ.1] at hi
  linarith only [hi]

/-- (5.2), p. 346, from the initial point `r₀ = χ(0)`:
`χ(t) = r₀ − ½ ∫₀^t ḡ(u, χ(u)) du`. -/
theorem XChar.eq_sub_integral {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    χ t = χ 0 - 1 / 2 * ∫ s in (0 : ℝ)..t, gBarX hH (Real.toNNReal s)
      (Real.toNNReal (χ s)) := by
  have hi := integral_charField_eq_sub hχ le_rfl ht.1 ht.2
  linarith only [hi]

end Christodoulou.Bondi
