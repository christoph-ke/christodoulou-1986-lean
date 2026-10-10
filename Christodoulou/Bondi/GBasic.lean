module
public import Christodoulou.Frozen.Bondi.G
public import Christodoulou.Frozen.Bondi.IntegrableOnTail
public import Christodoulou.Frozen.Radial.MeanZero
public import Christodoulou.Frozen.Radial.ContinuousMean
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The integrand `(h − h̄)²/s` of (3.11), as a function on `ℝ`. -/
@[expose] noncomputable def tailIntegrand (h : C(ℝ≥0, ℝ)) (s : ℝ) : ℝ :=
  (h (Real.toNNReal s) - mean h (Real.toNNReal s)) ^ 2 / s

variable (h : C(ℝ≥0, ℝ))

theorem tailIntegrand_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ tailIntegrand h s :=
  div_nonneg (sq_nonneg _) hs

theorem tailIntegrand_of_nonpos {s : ℝ} (hs : s ≤ 0) : tailIntegrand h s = 0 := by
  simp [tailIntegrand, Real.toNNReal_of_nonpos hs, mean_zero]

theorem continuousOn_tailIntegrand : ContinuousOn (tailIntegrand h) (Ioi 0) :=
  (((h.continuous.comp continuous_real_toNNReal).sub
    ((continuous_mean h).comp continuous_real_toNNReal)).pow 2).continuousOn.div
    continuousOn_id fun _ hs => ne_of_gt hs

theorem measurable_tailIntegrand : Measurable (tailIntegrand h) :=
  (((h.continuous.comp continuous_real_toNNReal).sub
    ((continuous_mean h).comp continuous_real_toNNReal)).pow 2).measurable.div measurable_id

theorem integrable_tailIntegrand (hh : IsSlice h) : Integrable (tailIntegrand h) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ (integrableOn_tail h hh 0)
  exact integrableOn_zero.congr_fun (fun s hs => (tailIntegrand_of_nonpos h hs).symm)
    measurableSet_Iic

/-- The tail identity: `∫_(r,∞) F = ∫_(0,∞) F − ∫₀ʳ F` for `r ≥ 0`. -/
theorem setIntegral_Ioi_eq (hh : IsSlice h) {r : ℝ} (hr : 0 ≤ r) :
    ∫ s in Ioi r, tailIntegrand h s =
      (∫ s in Ioi (0 : ℝ), tailIntegrand h s) - ∫ s in (0 : ℝ)..r, tailIntegrand h s := by
  rw [intervalIntegral.integral_of_le hr, eq_sub_iff_add_eq, add_comm,
    ← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrable_tailIntegrand h hh).integrableOn (integrable_tailIntegrand h hh).integrableOn,
    Ioc_union_Ioi_eq_Ioi hr]

theorem g_eq (hh : IsSlice h) (r : ℝ≥0) :
    g h hh r = Real.exp (-(4 * π) * ((∫ s in Ioi (0 : ℝ), tailIntegrand h s) -
      ∫ s in (0 : ℝ)..(r : ℝ), tailIntegrand h s)) := by
  change Real.exp (-(4 * π) * ∫ s in Ioi (r : ℝ), tailIntegrand h s) = _
  rw [setIntegral_Ioi_eq h hh r.coe_nonneg]

theorem setIntegral_Ioi_nonneg (r : ℝ≥0) : 0 ≤ ∫ s in Ioi (r : ℝ), tailIntegrand h s :=
  setIntegral_nonneg measurableSet_Ioi fun _ hs => tailIntegrand_nonneg h (r.2.trans (le_of_lt hs))

end Christodoulou.Bondi
