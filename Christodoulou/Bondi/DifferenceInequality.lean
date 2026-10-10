module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXBall
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Christodoulou.Frozen.Bondi.LinearStepEqOfIsClassicalSolution
import Christodoulou.Frozen.Bondi.LinearStepDifferenceIntegral
import Christodoulou.Frozen.Bondi.HasDerivWithinAtLinearStep
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic
import Christodoulou.Frozen.Bondi.IsCharacteristicMemIcc
import Christodoulou.Bondi.CoefficientRegularity
import Christodoulou.Bondi.Theorem2Helpers

/-!
# Homogeneous integral inequality for classical solutions

The integrable-majorant reconstruction of the Theorem 2 proof sketch on [P] p. 351.
It consumes the frozen classical fixed-point bridge and difference integral formula, with
slice-local coefficient estimates from `Theorem2Helpers`.
-/

public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XDI

/-- Equal initial data give the homogeneous weighted difference inequality of Theorem 2. -/
theorem classical_difference_integral_le {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (hcH : IsClassicalSolution u₀ H) (hcK : IsClassicalSolution u₀ K)
    (hdata : ∀ r : ℝ≥0, H (0, r) = K (0, r))
    (v : ℝ≥0) (hv : v ≤ u₀) (φ : ℝ → ℝ) (hφ : IntervalIntegrable φ volume 0 (v : ℝ))
    (hbound : ∀ s : ℝ≥0, s ≤ v → ∀ r : ℝ≥0,
      (1 + (r : ℝ)) ^ 3 * |H (s, r) - K (s, r)| ≤ φ s) (r : ℝ≥0) :
    (1 + (r : ℝ)) ^ 3 * |H (v, r) - K (v, r)| ≤
      exp (π * x ^ 2 / 12 * (u₀ : ℝ)) * (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)) *
        ∫ s in (0 : ℝ)..(v : ℝ), φ s := by
  let data := H.curry 0
  have hd : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0) := hH.1 0 bot_le
  have hdataeq : data = K.curry 0 := by ext ρ; exact hdata ρ
  have hSH (u : ℝ≥0) (hu : u ≤ u₀) (ρ : ℝ≥0) :
      linearStep hH data u ρ = H (u, ρ) :=
    Christodoulou.Bondi.linearStep_eq_of_isClassicalSolution hH hcH u hu ρ
  have hSK (u : ℝ≥0) (hu : u ≤ u₀) (ρ : ℝ≥0) :
      linearStep hK data u ρ = K (u, ρ) := by
    rw [hdataeq]
    exact Christodoulou.Bondi.linearStep_eq_of_isClassicalSolution hK hcK u hu ρ
  have hQ (u : ℝ≥0) (hu : u ≤ u₀) (ρ : ℝ≥0) :
      derivLinearStep hK data hd u ρ =
        derivWithin (fun s : ℝ => K (u, s.toNNReal)) (Ici 0) ρ := by
    have hq := hasDerivWithinAt_linearStep hK data hd u ρ
    have he : (fun s : ℝ => linearStep hK data u s.toNNReal) =
        (fun s : ℝ => K (u, s.toNNReal)) := funext (fun s => hSK u hu s.toNNReal)
    rw [he] at hq
    exact (hq.derivWithin (uniqueDiffOn_Ici 0 ρ ρ.coe_nonneg)).symm
  let V : Icc (0 : ℝ) u₀ := ⟨v, v.coe_nonneg, hv⟩
  let χ := characteristic hH V r
  let b := fun s : ℝ =>
    (gBarX hH s.toNNReal (χ s).toNNReal - gBarX hK s.toNNReal (χ s).toNNReal) / 2 *
      derivLinearStep hK data hd s.toNNReal (χ s).toNNReal +
    (linearCoeff hH s.toNNReal (χ s).toNNReal - linearCoeff hK s.toNNReal (χ s).toNNReal) *
      linearStep hK data s.toNNReal (χ s).toNNReal +
    linearSource hH s.toNNReal (χ s).toNNReal - linearSource hK s.toNNReal (χ s).toNNReal
  let E := exp (π * x ^ 2 / 12 * (u₀ : ℝ))
  let C := π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)
  let w := (1 + (r : ℝ)) ^ 3
  have hw : 0 < w := by dsimp [w]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hE : 0 ≤ E := (exp_pos _).le
  have he (s : ℝ) (hs : s ∈ Icc 0 (v : ℝ)) :
      exp (∫ t in s..(v : ℝ), linearCoeff hH t.toNNReal (χ t).toNNReal) ≤ E := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s) (b := (v : ℝ))
      (f := fun t => linearCoeff hH t.toNNReal (χ t).toNNReal)
      (C := π * x ^ 2 / 12) (fun t _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (XCoef.linearCoeff_nonneg hH _ _)]
        convert XCoef.linearCoeff_le_uniform hH t.toNNReal (χ t).toNNReal using 1
        ring)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)] at hi
    apply exp_le_exp.mpr
    calc
      _ ≤ |∫ t in s..(v : ℝ), linearCoeff hH t.toNNReal (χ t).toNNReal| := le_abs_self _
      _ ≤ (π * x ^ 2 / 12) * ((v : ℝ) - s) := hi
      _ ≤ (π * x ^ 2 / 12) * (u₀ : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [show (v : ℝ) ≤ u₀ from hv, hs.1]
  have hb (s : ℝ) (hs : s ∈ Icc 0 (v : ℝ)) : |b s| ≤ C * φ s / w := by
    have hsv : s.toNNReal ≤ v := Real.toNNReal_le_iff_le_coe.mpr hs.2
    have hsT := hsv.trans hv
    have hφ0 : 0 ≤ φ s := by
      have hi := hbound s.toNNReal hsv 0
      rw [Real.coe_toNNReal _ hs.1] at hi
      exact (by positivity : 0 ≤ (1 + ((0 : ℝ≥0) : ℝ)) ^ 3 *
        |H (s.toNNReal, 0) - K (s.toNNReal, 0)|).trans hi
    have hi := XT2H.remainder_bound hH hK s.toNNReal hsT hφ0
      (fun ρ => by simpa only [Real.coe_toNNReal _ hs.1] using hbound s.toNNReal hsv ρ)
      (χ s).toNNReal
    have hr : (r : ℝ) ≤ (χ s).toNNReal :=
      ((isCharacteristic_characteristic hH V r).mem_Icc hs).1.trans (Real.le_coe_toNNReal _)
    dsimp only [b]
    rw [hQ _ hsT, hSK _ hsT]
    exact hi.trans (div_le_div_of_nonneg_left (mul_nonneg hC hφ0) hw
      (by dsimp only [w]; gcongr))
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) v.coe_nonneg
    (f := fun s => exp (∫ t in s..(v : ℝ), linearCoeff hH t.toNNReal (χ t).toNNReal) * b s)
    (g := fun s => E * C / w * φ s)
    (Filter.Eventually.of_forall (fun s hs => by
      have hs' : s ∈ Icc 0 (v : ℝ) := ⟨hs.1.le, hs.2⟩
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
      calc
        _ ≤ E * (C * φ s / w) := mul_le_mul (he s hs') (hb s hs') (abs_nonneg _) hE
        _ = _ := by ring))
    (hφ.const_mul _)
  have hformula := linearStep_difference_integral hH hK data hd V r
  change linearStep hH data (v : ℝ).toNNReal r - linearStep hK data (v : ℝ).toNNReal r =
    ∫ s in (0 : ℝ)..(v : ℝ),
      exp (∫ t in s..(v : ℝ), linearCoeff hH t.toNNReal (χ t).toNNReal) * b s at hformula
  rw [Real.toNNReal_coe, hSH v hv, hSK v hv] at hformula
  rw [← hformula, Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hi
  have hfinal := mul_le_mul_of_nonneg_left hi hw.le
  calc
    _ ≤ w * (E * C / w * ∫ s in (0 : ℝ)..(v : ℝ), φ s) := hfinal
    _ = _ := by dsimp [E, C]; field_simp

end XDI
end Christodoulou.Bondi
