module
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Scalar linear ODE calculus

The Duhamel formula solves `y′ = a y + f` on a closed interval with continuous coefficients.
Its derivatives are taken within the interval, including at the endpoints. Solutions with the
same initial value are unique, and the differential equation implies its integral form.
-/

public section

open Set MeasureTheory Real

namespace Christodoulou.Bondi.LinODE

/-- FTC on a closed interval, one-sided at the endpoints. -/
theorem primitive_deriv {T : ℝ} {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 T))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun v => ∫ s in (0 : ℝ)..v, F s) (F t) (Icc 0 T) t := by
  let : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    ((hF.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
    (hF.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hF t ht)

/-- The Duhamel (variation of constants) formula for `y′ = a y + f`, `y(0) = y₀`. -/
@[expose] noncomputable def duhamel (a f : ℝ → ℝ) (y₀ t : ℝ) : ℝ :=
  y₀ * exp (∫ s in (0 : ℝ)..t, a s) +
    ∫ s in (0 : ℝ)..t, exp (∫ τ in s..t, a τ) * f s

/-- The Duhamel formula takes the prescribed value at zero. -/
theorem duhamel_zero (a f : ℝ → ℝ) (y₀ : ℝ) : duhamel a f y₀ 0 = y₀ := by
  simp [duhamel]

private theorem duhamel_factor {T : ℝ} {a f : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    (y₀ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    duhamel a f y₀ t = exp (∫ s in (0 : ℝ)..t, a s) *
      (y₀ + ∫ s in (0 : ℝ)..t, exp (-(∫ τ in (0 : ℝ)..s, a τ)) * f s) := by
  have hi {v : ℝ} (hv : v ∈ Icc 0 T) : IntervalIntegrable a volume 0 v :=
    (ha.mono (Icc_subset_Icc_right hv.2)).intervalIntegrable_of_Icc hv.1
  have he {s : ℝ} (hs : s ∈ Icc 0 t) :
      (∫ τ in s..t, a τ) = (∫ τ in (0 : ℝ)..t, a τ) - ∫ τ in (0 : ℝ)..s, a τ := by
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (hi ⟨hs.1, hs.2.trans ht.2⟩) ((hi ⟨hs.1, hs.2.trans ht.2⟩).symm.trans (hi ht))
    linarith
  rw [duhamel, mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  · ring
  · apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    dsimp only
    rw [he hs, sub_eq_add_neg, Real.exp_add]
    ring

/-- The Duhamel formula solves the linear ODE, one-sided at the endpoints. -/
theorem duhamel_deriv {T : ℝ} {a f : ℝ → ℝ}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (y₀ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (duhamel a f y₀)
      (a t * duhamel a f y₀ t + f t) (Icc 0 T) t := by
  let A := fun v => ∫ s in (0 : ℝ)..v, a s
  have hA : ∀ v ∈ Icc 0 T, HasDerivWithinAt A (a v) (Icc 0 T) v :=
    fun v hv => primitive_deriv ha hv
  have hAc : ContinuousOn A (Icc 0 T) := HasDerivWithinAt.continuousOn hA
  have hB := primitive_deriv ((Real.continuous_exp.comp_continuousOn hAc.neg).mul hf) ht
  have hd := ((hA t ht).exp).mul (hB.const_add y₀)
  have hcancel : exp (A t) * exp (-A t) = 1 := by rw [← Real.exp_add]; simp
  have hd' : HasDerivWithinAt
      (fun v => exp (A v) * (y₀ + ∫ s in (0 : ℝ)..v, exp (-A s) * f s))
      (a t * duhamel a f y₀ t + f t) (Icc 0 T) t := by
    convert hd using 1
    · rfl
    · rw [duhamel_factor ha y₀ ht]
      dsimp only [A, Function.comp_apply, Pi.mul_apply, Pi.neg_apply] at *
      linear_combination -f t * hcancel
  exact hd'.congr (fun v hv => duhamel_factor ha y₀ hv) (duhamel_factor ha y₀ ht)

/-- Uniqueness for `y′ = a y + f` on `[0, T]` with continuous `a` (no hypothesis on `f`). -/
theorem linear_unique {T : ℝ} {a f y z : ℝ → ℝ}
    (ha : ContinuousOn a (Icc 0 T))
    (hy : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (a t * y t + f t) (Icc 0 T) t)
    (hz : ∀ t ∈ Icc 0 T, HasDerivWithinAt z (a t * z t + f t) (Icc 0 T) t)
    (hzero : y 0 = z 0) : EqOn y z (Icc 0 T) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  have hv : ∀ t ∈ Ico 0 T,
      LipschitzOnWith (Real.toNNReal K) (fun v => a t * v + f t) univ := by
    intro t ht
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro v w
    calc
      dist (a t * v + f t) (a t * w + f t) = |a t| * dist v w := by
        simp only [Real.dist_eq, add_sub_add_right_eq_sub, ← mul_sub, abs_mul]
      _ ≤ (Real.toNNReal K : ℝ) * dist v w :=
        mul_le_mul_of_nonneg_right
          ((hK t ⟨ht.1, ht.2.le⟩).trans (Real.le_coe_toNNReal K)) dist_nonneg
  exact ODE_solution_unique_of_mem_Icc_right hv (HasDerivWithinAt.continuousOn hy)
    (fun t ht => (hy t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) (fun _ _ => mem_univ _)
    (HasDerivWithinAt.continuousOn hz)
    (fun t ht => (hz t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) (fun _ _ => mem_univ _) hzero

/-- Integral form of `y′ = a y + f`. -/
theorem linear_integral {T : ℝ} {a f y : ℝ → ℝ}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (hy : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (a t * y t + f t) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    y t = y 0 + ∫ s in (0 : ℝ)..t, (a s * y s + f s) := by
  have hc := HasDerivWithinAt.continuousOn hy
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hc.mono (Icc_subset_Icc_right ht.2))
    (fun s hs => (hy s ⟨hs.1.le, hs.2.le.trans ht.2⟩).hasDerivAt
      (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2)))
    ((((ha.mul hc).add hf).mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
  linarith only [hi]


end Christodoulou.Bondi.LinODE
