module
public import Christodoulou.Bondi.LinearODE
public import Christodoulou.Bondi.LinearStepBasic
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic

/-!
# The linear step along characteristics

The linear step solves (7.2) along every characteristic, including the interval endpoints.
Its differential equation yields the integral form and uniqueness for the prescribed data.
-/

public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi

/-- The linear step satisfies (7.2) along a characteristic, including at the endpoints. -/
theorem XStep.hasDerivWithinAt_linearStep {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0}
    {χ : ℝ → ℝ} (hχ : IsCharacteristic hH u₁ r₁ χ) (h₀ : C(ℝ≥0, ℝ)) {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    HasDerivWithinAt (fun s : ℝ => linearStep hH h₀ (Real.toNNReal s) (Real.toNNReal (χ s)))
      (linearCoeff hH (Real.toNNReal t) (Real.toNNReal (χ t)) *
          linearStep hH h₀ (Real.toNNReal t) (Real.toNNReal (χ t)) +
        linearSource hH (Real.toNNReal t) (Real.toNNReal (χ t)))
      (Icc 0 (u₁ : ℝ)) t := by
  have ha := continuousOn_linearCoeff hχ
  have hf := continuousOn_linearSource hχ
  have hd := LinODE.duhamel_deriv ha hf (h₀ (Real.toNNReal (χ 0))) ht
  have hE : ∀ s ∈ Icc 0 (u₁ : ℝ),
      linearStep hH h₀ (Real.toNNReal s) (Real.toNNReal (χ s)) =
        LinODE.duhamel (fun s => linearCoeff hH s.toNNReal (χ s).toNNReal)
          (fun s => linearSource hH s.toNNReal (χ s).toNNReal)
          (h₀ (Real.toNNReal (χ 0))) s :=
    fun s hs => linearStep_eq hχ h₀ hs
  rw [hE t ht]
  exact hd.congr hE (hE t ht)

/-- The linear step satisfies the integral form of (7.2) along a characteristic. -/
theorem XStep.linearStep_eq_add_integral {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0}
    {χ : ℝ → ℝ} (hχ : IsCharacteristic hH u₁ r₁ χ) (h₀ : C(ℝ≥0, ℝ)) {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    linearStep hH h₀ (Real.toNNReal t) (Real.toNNReal (χ t)) =
      h₀ (Real.toNNReal (χ 0)) +
        ∫ s in (0 : ℝ)..t,
          (linearCoeff hH (Real.toNNReal s) (Real.toNNReal (χ s)) *
              linearStep hH h₀ (Real.toNNReal s) (Real.toNNReal (χ s)) +
            linearSource hH (Real.toNNReal s) (Real.toNNReal (χ s))) := by
  have h := LinODE.linear_integral (continuousOn_linearCoeff hχ)
    (continuousOn_linearSource hχ) (fun s hs => hasDerivWithinAt_linearStep hχ h₀ hs) ht
  rw [Real.toNNReal_zero, linearStep_zero] at h
  exact h

/-- Prescribed initial data and (7.2) along every characteristic determine the linear step. -/
theorem XStep.eq_linearStep_of_hasDerivWithinAt {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (h₀ : C(ℝ≥0, ℝ)) {q : ℝ≥0 → ℝ≥0 → ℝ}
    (hq₀ : ∀ r, q 0 r = h₀ r)
    (hq : ∀ (u₁ : Icc (0 : ℝ) u₀) (r₁ : ℝ≥0) (χ : ℝ → ℝ), IsCharacteristic hH u₁ r₁ χ →
      ∀ t ∈ Icc 0 (u₁ : ℝ),
        HasDerivWithinAt (fun s : ℝ => q (Real.toNNReal s) (Real.toNNReal (χ s)))
          (linearCoeff hH (Real.toNNReal t) (Real.toNNReal (χ t)) *
              q (Real.toNNReal t) (Real.toNNReal (χ t)) +
            linearSource hH (Real.toNNReal t) (Real.toNNReal (χ t)))
          (Icc 0 (u₁ : ℝ)) t)
    {u : ℝ≥0} (hu : u ≤ u₀) (r : ℝ≥0) : q u r = linearStep hH h₀ u r := by
  set w : Icc (0 : ℝ) u₀ := ⟨u, u.2, by exact_mod_cast hu⟩
  have hc := isCharacteristic_characteristic hH w r
  have key := LinODE.linear_unique (continuousOn_linearCoeff hc) (hq w r _ hc)
    (fun t ht => hasDerivWithinAt_linearStep hc h₀ ht)
    (by simp only [Real.toNNReal_zero, hq₀, linearStep_zero])
    (show (u : ℝ) ∈ Icc 0 (w : ℝ) from ⟨u.2, le_rfl⟩)
  have h1 : characteristic hH w r (u : ℝ) = r := hc.1
  simpa only [h1, Real.toNNReal_coe] using key

end Christodoulou.Bondi
