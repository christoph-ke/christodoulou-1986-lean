module
public import Christodoulou.Frozen.Radial.MeanZero
public import Christodoulou.Frozen.Radial.MeanEqIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus



public section
open Set MeasureTheory
open scoped NNReal
namespace Christodoulou.Radial

/-- The real-line integrand `s ↦ f (max s 0)` of a radial slice; on `[0, ∞)` it is `f`. -/
@[expose] noncomputable def lift (f : C(ℝ≥0, ℝ)) : ℝ → ℝ := fun s => f (Real.toNNReal s)

theorem continuous_lift (f : C(ℝ≥0, ℝ)) : Continuous (lift f) :=
  f.continuous.comp continuous_real_toNNReal

@[simp] theorem lift_coe (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) : lift f r = f r := by
  simp [lift]

/-- The FTC for the radial primitive `s ↦ ∫₀ˢ f`. -/
theorem hasDerivAt_integral_lift (f : C(ℝ≥0, ℝ)) (x : ℝ) :
    HasDerivAt (fun s => ∫ t in (0 : ℝ)..s, lift f t) (lift f x) x :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_lift f).intervalIntegrable _ _)
    (continuous_lift f).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_lift f).continuousAt

/-- `r f̄(r) = ∫₀ʳ f` for every `r ≥ 0`, including the centre. -/
theorem coe_mul_mean (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) :
    (r : ℝ) * mean f r = ∫ s in (0 : ℝ)..(r : ℝ), lift f s := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [mean_zero]
  · have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    rw [mean_eq_integral f r (pos_iff_ne_zero.2 hr), ← mul_assoc, mul_inv_cancel₀ hr', one_mul]
    rfl

/-- On `[0, ∞)` the function `s ↦ s f̄(s)` coincides with the radial primitive of `f`. -/
theorem mul_mean_eqOn (f : C(ℝ≥0, ℝ)) :
    EqOn (fun s : ℝ => s * mean f (Real.toNNReal s)) (fun s => ∫ t in (0 : ℝ)..s, lift f t)
      (Ici 0) := by
  intro s hs
  have := coe_mul_mean f (Real.toNNReal s)
  rwa [Real.coe_toNNReal s hs] at this

/-- The mean as an average over the unit interval: `f̄(r) = ∫₀¹ f(r t) dt` for all `r ≥ 0`. -/
theorem mean_eq_integral_unitInterval (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) :
    mean f r = ∫ t in (0 : ℝ)..1, f (Real.toNNReal ((r : ℝ) * t)) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [mean_zero]
  · have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    rw [intervalIntegral.integral_comp_mul_left (fun s => f (Real.toNNReal s)) hr',
      mean_eq_integral f r (pos_iff_ne_zero.2 hr)]
    simp

end Christodoulou.Radial
