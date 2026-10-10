module
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.InitialBound
import Christodoulou.Bondi.WeightedCoefficients
import Christodoulou.Bondi.LinearStepRegularity
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic
import Christodoulou.Frozen.Bondi.IsCharacteristicEqAddIntegral
import Christodoulou.Frozen.Bondi.IsCharacteristicMemIcc
import Christodoulou.Frozen.Bondi.IsCharacteristicLinearStepEq
import Christodoulou.Frozen.Bondi.HasDerivWithinAtLinearStep
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Christodoulou.Frozen.Bondi.ContinuousGBarX

/-!
# Weighted transport on arbitrary strips

The characteristic weight comparison (9.11) and integrable time majorant give the
uniform value and derivative estimates (9.15), (9.23), and their sum (9.24).
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XWT

private lemma time_integral {s v : ℝ} (hs : 0 ≤ s) (hsv : s ≤ v) :
    (∫ t in s..v, 1 / (1 + t / 2) ^ 7) ≤ 1 / 3 := by
  have hb (t : ℝ) (ht : 0 ≤ t) : 0 < 1 + t / 2 := by positivity
  have hd (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (fun z : ℝ => -(1 / 3) / (1 + z / 2) ^ 6)
        (1 / (1 + t / 2) ^ 7) t := by
    convert (hasDerivAt_const t (-(1 / 3) : ℝ)).div
      ((((hasDerivAt_id t).div_const 2).const_add 1).pow 6)
      (pow_ne_zero 6 (hb t ht).ne') using 1
    · rfl
    · dsimp
      field_simp
      ring
  have hc : ContinuousOn (fun t : ℝ => 1 / (1 + t / 2) ^ 7) (Icc s v) :=
    continuousOn_const.div ((continuousOn_const.add (continuousOn_id.div_const 2)).pow 7)
      (fun t ht => pow_ne_zero 7 (hb t (hs.trans ht.1)).ne')
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsv
    (f := fun z : ℝ => -(1 / 3) / (1 + z / 2) ^ 6)
    (fun t ht => (hd t (hs.trans ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => hd t (hs.trans ht.1.le)) (hc.intervalIntegrable_of_Icc hsv)
  rw [hi]
  have hp : 1 ≤ (1 + s / 2) ^ 6 := one_le_pow₀ (by linarith)
  have hq := div_le_self (by norm_num : (0 : ℝ) ≤ 1 / 3) hp
  have hv : 0 ≤ (1 / 3 : ℝ) / (1 + v / 2) ^ 6 := by positivity
  rw [neg_div, neg_div]
  linarith only [hq, hv]

private lemma weighted_integral {s v W C : ℝ} {f : ℝ → ℝ}
    (hs : 0 ≤ s) (hsv : s ≤ v) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (hf : ∀ t ∈ Icc s v, W * |f t| ≤ C / (1 + t / 2) ^ 7) :
    W * |∫ t in s..v, f t| ≤ C / 3 := by
  have hc : IntervalIntegrable (fun t : ℝ => C / (1 + t / 2) ^ 7)
      MeasureTheory.volume s v := by
    apply ContinuousOn.intervalIntegrable_of_Icc hsv
    exact continuousOn_const.div
      ((continuousOn_const.add (continuousOn_id.div_const 2)).pow 7)
      (fun t ht => by have := hs.trans ht.1; positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le hsv
    (f := fun t => W * f t) (g := fun t => C / (1 + t / 2) ^ 7)
    (Filter.Eventually.of_forall (fun t ht => by
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hW] using
        hf t ⟨ht.1.le, ht.2⟩)) hc
  rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hW] at hi
  calc
    _ ≤ ∫ t in s..v, C / (1 + t / 2) ^ 7 := hi
    _ = C * ∫ t in s..v, 1 / (1 + t / 2) ^ 7 := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      ext t
      ring
    _ ≤ C / 3 := by simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left (time_integral hs hsv) hC

variable {T : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}

private lemma characteristic_weight (hH : MemXPrimeBall T x H)
    {v : Icc (0 : ℝ) T} {r : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH.1 v r χ) {s : ℝ} (hs : s ∈ Icc 0 (v : ℝ)) :
    exp (-(π / 6) * x ^ 2) * (1 + (v : ℝ) / 2 + (r : ℝ)) ≤
      1 + s / 2 + χ s := by
  let k := exp (-(π / 6) * x ^ 2)
  have hk : k ≤ 1 := exp_le_one_iff.mpr (by
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg x))
  have hc : ContinuousOn χ (Icc s (v : ℝ)) :=
    (HasDerivWithinAt.continuousOn hχ.2).mono (Icc_subset_Icc_left hs.1)
  have hg := (continuous_gBarX hH.1).comp_continuousOn
    (continuous_real_toNNReal.continuousOn.prodMk
      (continuous_real_toNNReal.comp_continuousOn hc))
  have hi : k * ((v : ℝ) - s) ≤
      ∫ t in s..(v : ℝ), gBarX hH.1 t.toNNReal (χ t).toNNReal := by
    calc
      _ = ∫ _t in s..(v : ℝ), k := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on hs.2 intervalIntegrable_const
        (hg.intervalIntegrable_of_Icc hs.2)
        (fun t _ => (XWC.exp_lower (T := T) (x := x) t.toNNReal).trans
          (XWC.gBarX_lower hH _ _))
  have heq := hχ.eq_add_integral hs
  have hslack := mul_nonneg (sub_nonneg.mpr hk)
    (show 0 ≤ 1 + (r : ℝ) + s / 2 by have := hs.1; positivity)
  change k * _ ≤ _
  nlinarith only [hi, heq, hslack]

private lemma clamp_time {v : Icc (0 : ℝ) T} {s : ℝ}
    (hs : s ∈ Icc 0 (v : ℝ)) : ((min s.toNNReal T : ℝ≥0) : ℝ) = s := by
  rw [min_eq_left (show s.toNNReal ≤ T from
    (Real.toNNReal_le_iff_le_coe).mpr (hs.2.trans v.2.2)), Real.coe_toNNReal _ hs.1]

private lemma characteristic_exp_bound (hH : MemXPrimeBall T x H)
    {v : Icc (0 : ℝ) T} {r : ℝ≥0} {χ : ℝ → ℝ}
    (_hχ : IsCharacteristic hH.1 v r χ) {s : ℝ} (hs : s ∈ Icc 0 (v : ℝ)) :
    exp (∫ t in s..(v : ℝ), linearCoeff hH.1 t.toNNReal (χ t).toNNReal) ≤
      exp (π / 18 * x ^ 2) := by
  apply exp_le_exp.mpr
  have hb := weighted_integral hs.1 hs.2 (W := 1)
    (C := π / 6 * x ^ 2) zero_le_one (by positivity)
    (f := fun t => linearCoeff hH.1 t.toNNReal (χ t).toNNReal) (by
      intro t ht
      rw [one_mul, abs_of_nonneg (XWC.linearCoeff_nonneg hH _ _)]
      have hh := XWC.linearCoeff_le_uniform hH t.toNNReal (χ t).toNNReal
      dsimp only at hh
      rw [clamp_time ⟨hs.1.trans ht.1, ht.2⟩] at hh
      exact hh)
  exact (le_abs_self _).trans (by convert hb using 1 <;> ring)

private lemma transfer {W R k C z : ℝ} (n : ℕ) (hW : 0 ≤ W) (hk : 0 < k)
    (hR : k * W ≤ R) (hb : R ^ n * |z| ≤ C) :
    W ^ n * |z| ≤ C / k ^ n := by
  apply (le_div_iff₀ (pow_pos hk n)).mpr
  calc
    _ = (k * W) ^ n * |z| := by ring
    _ ≤ R ^ n * |z| := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg hk.le hW) hR n) (abs_nonneg _)
    _ ≤ C := hb

private lemma transfer_decay {W R k b C z : ℝ} (n : ℕ)
    (hW : 0 ≤ W) (hk : 0 < k) (hb : 0 < b) (hR : k * W ≤ R) (hRp : 0 < R)
    (hz : |z| ≤ C / (b ^ 7 * R ^ n)) :
    W ^ n * |z| ≤ (C / k ^ n) / b ^ 7 := by
  have hh : R ^ n * |z| ≤ C / b ^ 7 := by
    apply (le_div_iff₀ (pow_pos hb 7)).mpr
    have hz' := (le_div_iff₀ (mul_pos (pow_pos hb 7) (pow_pos hRp n))).mp hz
    nlinarith only [hz']
  convert transfer n hW hk hR hh using 1
  ring

private lemma formula_bound {v W k E d C z : ℝ} {A f : ℝ → ℝ} (n : ℕ)
    (hv : 0 ≤ v) (hW : 0 ≤ W) (hk : 0 < k) (hE : 0 ≤ E) (hd : 0 ≤ d) (hC : 0 ≤ C)
    (hz : W ^ n * |z| ≤ d / k ^ n)
    (hA : ∀ s ∈ Icc 0 v, exp (A s) ≤ E)
    (hf : ∀ s ∈ Icc 0 v, W ^ n * |f s| ≤ (C / k ^ n) / (1 + s / 2) ^ 7) :
    W ^ n * |z * exp (A 0) + ∫ s in (0 : ℝ)..v, exp (A s) * f s| ≤
      E / k ^ n * (d + C / 3) := by
  have hint : W ^ n * |∫ s in (0 : ℝ)..v, exp (A s) * f s| ≤
      (E * (C / k ^ n)) / 3 := by
    apply weighted_integral le_rfl hv (pow_nonneg hW n) (by positivity)
    intro s hs
    rw [abs_mul, abs_of_pos (exp_pos _)]
    calc
      _ = exp (A s) * (W ^ n * |f s|) := by ring
      _ ≤ E * ((C / k ^ n) / (1 + s / 2) ^ 7) :=
        mul_le_mul (hA s hs) (hf s hs) (by positivity) hE
      _ = _ := by ring
  calc
    _ ≤ W ^ n * (|z * exp (A 0)| + |∫ s in (0 : ℝ)..v, exp (A s) * f s|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (pow_nonneg hW n)
    _ = (W ^ n * |z|) * exp (A 0) +
        W ^ n * |∫ s in (0 : ℝ)..v, exp (A s) * f s| := by
      rw [abs_mul, abs_of_pos (exp_pos _)]
      ring
    _ ≤ (d / k ^ n) * E + (E * (C / k ^ n)) / 3 :=
      add_le_add (mul_le_mul hz (hA 0 ⟨le_rfl, hv⟩) (exp_pos _).le (by positivity)) hint
    _ = _ := by ring

private lemma exp_factor (c : ℝ) (n : ℕ) :
    exp (c * x ^ 2) / exp (-(π / 6) * x ^ 2) ^ n =
      exp ((c + n * (π / 6)) * x ^ 2) := by
  rw [← exp_nat_mul, ← exp_sub]
  congr 1
  ring

private lemma value_bound (hH : MemXPrimeBall T x H) (data : C(ℝ≥0, ℝ))
    {d : ℝ} (hd : 0 ≤ d) (hbound : InitialBound data d) (u r : ℝ≥0) :
    (1 + ((min u T : ℝ≥0) : ℝ) / 2 + (r : ℝ)) ^ 3 *
      |linearStep hH.1 data u r| ≤ exp (5 * π / 9 * x ^ 2) * (d + π / 18 * x ^ 3) := by
  let v : Icc (0 : ℝ) T :=
    ⟨min u T, (min u T).coe_nonneg, by exact_mod_cast min_le_right u T⟩
  let χ := characteristic hH.1 v r
  let k := exp (-(π / 6) * x ^ 2)
  let W := 1 + (v : ℝ) / 2 + (r : ℝ)
  have hχ : IsCharacteristic hH.1 v r χ := isCharacteristic_characteristic hH.1 v r
  have hx := XWC.x_nonneg hH
  have hk : 0 < k := exp_pos _
  have hW : 0 ≤ W := by dsimp [W]; have := v.2.1; positivity
  have hχ0 (s : ℝ) (hs : s ∈ Icc 0 (v : ℝ)) : 0 ≤ χ s :=
    r.coe_nonneg.trans (hχ.mem_Icc hs).1
  have hw (s : ℝ) (hs : s ∈ Icc 0 (v : ℝ)) :
      k * W ≤ 1 + s / 2 + χ s := characteristic_weight hH hχ hs
  have hd0 : W ^ 3 * |data (χ 0).toNNReal| ≤ d / k ^ 3 := by
    apply transfer 3 hW hk
      (show k * W ≤ 1 + ((χ 0).toNNReal : ℝ) by
        simpa only [Real.coe_toNNReal _ (hχ0 0 ⟨le_rfl, v.2.1⟩), zero_div, add_zero]
          using hw 0 ⟨le_rfl, v.2.1⟩)
    exact (le_add_of_nonneg_right (by positivity)).trans (hbound _)
  have hf (s : ℝ) (hs : s ∈ Icc 0 (v : ℝ)) :
      W ^ 3 * |linearSource hH.1 s.toNNReal (χ s).toNNReal| ≤
        ((π / 6 * x ^ 3) / k ^ 3) / (1 + s / 2) ^ 7 := by
    have hb := XWC.abs_linearSource_le hH s.toNNReal (χ s).toNNReal
    dsimp only at hb
    rw [clamp_time hs, Real.coe_toNNReal _ (hχ0 s hs)] at hb
    exact transfer_decay 3 hW hk (by have := hs.1; positivity) (hw s hs)
      (by have := hs.1; have := hχ0 s hs; positivity) hb
  have hformula := hχ.linearStep_eq data ⟨v.2.1, le_rfl⟩
  rw [hχ.1, Real.toNNReal_coe] at hformula
  have hvNN : (v : ℝ).toNNReal = min u T := by
    change (min (u : ℝ) (T : ℝ)).toNNReal = min u T
    rw [← NNReal.coe_min, Real.toNNReal_coe]
  rw [hvNN] at hformula
  have hclamp : linearStep hH.1 data (min u T) r = linearStep hH.1 data u r := by
    simp only [linearStep, NNReal.coe_min, min_assoc, min_self]
  rw [hclamp] at hformula
  rw [hformula]
  have hb := formula_bound 3 v.2.1 hW hk (exp_pos (π / 18 * x ^ 2)).le hd
    (show 0 ≤ π / 6 * x ^ 3 by positivity) hd0
    (fun s hs => characteristic_exp_bound hH hχ hs) hf
  have he : exp (π / 18 * x ^ 2) / k ^ 3 = exp (5 * π / 9 * x ^ 2) := by
    dsimp [k]
    rw [exp_factor]
    congr 1
    ring
  rw [he] at hb
  dsimp only [W, v] at hb
  simp only [NNReal.coe_min]
  convert hb using 1
  ring

private lemma product_decay {b R A M a S : ℝ} (hb : 0 < b) (hbR : b ≤ R)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (ha : |a| ≤ A / (b ^ 5 * R ^ 3))
    (hS : R ^ 3 * |S| ≤ M) : |a * S| ≤ A * M / (b ^ 7 * R ^ 4) := by
  have hR : 0 < R := hb.trans_le hbR
  have hS' : |S| ≤ M / R ^ 3 := (le_div_iff₀ (pow_pos hR 3)).mpr (by
    simpa only [mul_comm] using hS)
  rw [abs_mul]
  calc
    _ ≤ (A / (b ^ 5 * R ^ 3)) * (M / R ^ 3) :=
      mul_le_mul ha hS' (abs_nonneg _) (by positivity)
    _ = (A * M / (b ^ 7 * R ^ 4)) * (b / R) ^ 2 := by field_simp
    _ ≤ (A * M / (b ^ 7 * R ^ 4)) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_one₀ (by positivity) ((div_le_one hR).mpr hbR)
    _ = _ := mul_one _

private lemma derivative_bound (hH : MemXPrimeBall T x H) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    {d : ℝ} (hd : 0 ≤ d) (hbound : InitialBound data d) (u r : ℝ≥0) :
    (1 + ((min u T : ℝ≥0) : ℝ) / 2 + (r : ℝ)) ^ 4 *
      |derivLinearStep hH.1 data hdata u r| ≤
      exp (7 * π / 9 * x ^ 2) *
        (d + π / 6 * x ^ 2 * (7 / 6 * x +
          (d + π / 18 * x ^ 3) * exp (5 * π / 9 * x ^ 2))) := by
  let v : Icc (0 : ℝ) T :=
    ⟨min u T, (min u T).coe_nonneg, by exact_mod_cast min_le_right u T⟩
  let χ := characteristic hH.1 v r
  let k := exp (-(π / 6) * x ^ 2)
  let W := 1 + (v : ℝ) / 2 + (r : ℝ)
  let A := fun s : ℝ => ∫ t in s..(v : ℝ), linearCoeff hH.1 t.toNNReal (χ t).toNNReal
  let M := exp (5 * π / 9 * x ^ 2) * (d + π / 18 * x ^ 3)
  let C := π / 2 * x ^ 2 * M + 7 * π * x ^ 3 / 12
  let ar := fun s : ℝ => 1 / 2 * deriv2GBarX hH.1 s.toNNReal (χ s).toNNReal
  let S := fun s : ℝ => linearStep hH.1 data s.toNNReal (χ s).toNNReal
  let fr := fun s : ℝ => -ar s * hBarX T H s.toNNReal (χ s).toNNReal -
    linearCoeff hH.1 s.toNNReal (χ s).toNNReal * derivHBarX hH.1 s.toNNReal (χ s).toNNReal
  have hχ : IsCharacteristic hH.1 v r χ := isCharacteristic_characteristic hH.1 v r
  have hx := XWC.x_nonneg hH
  have hk : 0 < k := exp_pos _
  have hW : 0 ≤ W := by dsimp [W]; have := v.2.1; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hχ0 (s : ℝ) (hs : s ∈ Icc 0 (v : ℝ)) : 0 ≤ χ s :=
    r.coe_nonneg.trans (hχ.mem_Icc hs).1
  have hw (s : ℝ) (hs : s ∈ Icc 0 (v : ℝ)) :
      k * W ≤ 1 + s / 2 + χ s := characteristic_weight hH hχ hs
  have hd0 : W ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (χ 0)| ≤
      d / k ^ 4 := by
    have hh : (1 + ((χ 0).toNNReal : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (χ 0).toNNReal| ≤ d :=
      (le_add_of_nonneg_left (by positivity)).trans (hbound _)
    rw [Real.coe_toNNReal _ (hχ0 0 ⟨le_rfl, v.2.1⟩)] at hh
    apply transfer 4 hW hk _ hh
    simpa only [zero_div, add_zero] using hw 0 ⟨le_rfl, v.2.1⟩
  have hf (s : ℝ) (hs : s ∈ Icc 0 (v : ℝ)) :
      W ^ 4 * |ar s * S s + fr s| ≤ (C / k ^ 4) / (1 + s / 2) ^ 7 := by
    have hb : 0 < 1 + s / 2 := by have := hs.1; positivity
    have hR : 0 < 1 + s / 2 + χ s := by have := hχ0 s hs; positivity
    have ha : |ar s| ≤ (π / 2 * x ^ 2) / ((1 + s / 2) ^ 5 *
        (1 + s / 2 + χ s) ^ 3) := by
      have hh := XWC.abs_deriv2GBarX_le hH s.toNNReal (χ s).toNNReal
      dsimp only at hh
      rw [clamp_time hs, Real.coe_toNNReal _ (hχ0 s hs)] at hh
      dsimp only [ar]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      convert mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 1 / 2) using 1
      ring
    have hS : (1 + s / 2 + χ s) ^ 3 * |S s| ≤ M := by
      have hh := value_bound hH data hd hbound s.toNNReal (χ s).toNNReal
      rw [clamp_time hs, Real.coe_toNNReal _ (hχ0 s hs)] at hh
      exact hh
    have hp := product_decay hb (le_add_of_nonneg_right (hχ0 s hs))
      (show 0 ≤ π / 2 * x ^ 2 by positivity) hM ha hS
    have hfr := XWC.abs_deriv_linearSource_le hH s.toNNReal (χ s).toNNReal
    dsimp only at hfr
    rw [clamp_time hs, Real.coe_toNNReal _ (hχ0 s hs)] at hfr
    have hh : |ar s * S s + fr s| ≤ C / ((1 + s / 2) ^ 7 *
        (1 + s / 2 + χ s) ^ 4) := by
      calc
        _ ≤ |ar s * S s| + |fr s| := abs_add_le _ _
        _ ≤ (π / 2 * x ^ 2) * M / ((1 + s / 2) ^ 7 *
            (1 + s / 2 + χ s) ^ 4) +
            7 * π * x ^ 3 / (12 * (1 + s / 2) ^ 7 * (1 + s / 2 + χ s) ^ 4) :=
          add_le_add hp hfr
        _ = _ := by
          dsimp only [C]
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
    exact transfer_decay 4 hW hk hb (hw s hs) hR hh
  have he (s : ℝ) (hs : s ∈ Icc 0 (v : ℝ)) : exp (2 * A s) ≤ exp (π / 9 * x ^ 2) := by
    have hh := characteristic_exp_bound hH hχ hs
    calc
      _ = exp (A s) * exp (A s) := by rw [← exp_add]; congr 1; ring
      _ ≤ exp (π / 18 * x ^ 2) * exp (π / 18 * x ^ 2) :=
        mul_le_mul hh hh (exp_pos _).le (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hh := formula_bound 4 v.2.1 hW hk (exp_pos (π / 9 * x ^ 2)).le hd hC hd0 he hf
  have hexp : exp (π / 9 * x ^ 2) / k ^ 4 = exp (7 * π / 9 * x ^ 2) := by
    dsimp [k]
    rw [exp_factor]
    congr 1
    ring
  rw [hexp] at hh
  change W ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (χ 0) *
    exp (2 * A 0) + ∫ s in (0 : ℝ)..(v : ℝ), exp (2 * A s) * (ar s * S s + fr s)| ≤ _
  convert hh using 1
  dsimp [C, M]
  ring

private lemma simplify_924 {x d : ℝ} (hx : 0 ≤ x) (hd : 0 ≤ d) :
    exp (5 * π / 9 * x ^ 2) * (d + π / 18 * x ^ 3) +
      exp (7 * π / 9 * x ^ 2) *
        (d + π / 6 * x ^ 2 * (7 / 6 * x +
          (d + π / 18 * x ^ 3) * exp (5 * π / 9 * x ^ 2))) ≤
      (2 + π / 6 * x ^ 2) * exp (4 * π / 3 * x ^ 2) * (d + π / 8 * x ^ 3) := by
  have ha : exp (5 * π / 9 * x ^ 2) ≤ exp (4 * π / 3 * x ^ 2) := by
    apply exp_le_exp.mpr
    nlinarith [mul_nonneg pi_pos.le (sq_nonneg x)]
  have hb : exp (7 * π / 9 * x ^ 2) ≤ exp (4 * π / 3 * x ^ 2) := by
    apply exp_le_exp.mpr
    nlinarith [mul_nonneg pi_pos.le (sq_nonneg x)]
  have hab : exp (7 * π / 9 * x ^ 2) * exp (5 * π / 9 * x ^ 2) =
      exp (4 * π / 3 * x ^ 2) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    _ = exp (5 * π / 9 * x ^ 2) * (d + π / 18 * x ^ 3) +
        exp (7 * π / 9 * x ^ 2) * (d + 7 * π / 36 * x ^ 3) +
        (exp (7 * π / 9 * x ^ 2) * exp (5 * π / 9 * x ^ 2)) *
          (π / 6 * x ^ 2 * (d + π / 18 * x ^ 3)) := by ring
    _ ≤ exp (4 * π / 3 * x ^ 2) * (d + π / 18 * x ^ 3) +
        exp (4 * π / 3 * x ^ 2) * (d + 7 * π / 36 * x ^ 3) +
        exp (4 * π / 3 * x ^ 2) * (π / 6 * x ^ 2 * (d + π / 18 * x ^ 3)) := by
      rw [hab]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_right ha (by positivity)
        · exact mul_le_mul_of_nonneg_right hb (by positivity)
      · exact le_rfl
    _ ≤ ((2 + π / 6 * x ^ 2) * exp (4 * π / 3 * x ^ 2) * (d + π / 8 * x ^ 3)) := by
      have hp : 0 ≤ exp (4 * π / 3 * x ^ 2) * (5 * π ^ 2 * x ^ 5 / 432) := by positivity
      nlinarith only [hp]

/-- The weighted linear transport estimate (9.24), uniformly in the strip length. -/
theorem linearStep_prime_bound {T : ℝ≥0} {x d : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXPrimeBall T x H)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hd : 0 ≤ d) (hbound : InitialBound data d) :
    MemXPrimeBall T
      ((2 + π / 6 * x ^ 2) * exp (4 * π / 3 * x ^ 2) * (d + π / 8 * x ^ 3))
      (linearStepMap hH.1 data) := by
  have hreg := XReg.linearStep_radial_regular hH.1 data hdata.1.1
  have hsum (u : ℝ≥0) (hu : u ≤ T) (r : ℝ≥0) :
      primeWeight u r ^ 3 * |linearStepMap hH.1 data (u, r)| +
        primeWeight u r ^ 4 * |radialDerivative (linearStepMap hH.1 data) u r| ≤
        (2 + π / 6 * x ^ 2) * exp (4 * π / 3 * x ^ 2) * (d + π / 8 * x ^ 3) := by
    have hv := value_bound hH data hd hbound u r
    have hder := derivative_bound hH data hdata.1.1 hd hbound u r
    rw [min_eq_left hu] at hv hder
    have heq := (hasDerivWithinAt_linearStep hH.1 data hdata.1.1 u r).derivWithin
      (uniqueDiffOn_Ici 0 _ r.coe_nonneg)
    change primeWeight u r ^ 3 * |linearStep hH.1 data u r| +
      primeWeight u r ^ 4 *
        |derivWithin (fun s : ℝ => linearStep hH.1 data u s.toNNReal) (Ici 0) r| ≤ _
    rw [heq]
    have hw : primeWeight u r = 1 + (u : ℝ) / 2 + (r : ℝ) := by
      unfold primeWeight
      ring
    rw [hw]
    exact (add_le_add hv hder).trans (simplify_924 (XWC.x_nonneg hH) hd)
  refine ⟨⟨fun u _ => hreg.1 u, hreg.2, ?_⟩, hsum⟩
  intro u hu r
  apply le_trans _ (hsum u hu r)
  have hw : 1 + (r : ℝ) ≤ primeWeight u r := by
    dsimp only [primeWeight]
    have := u.coe_nonneg
    linarith only [this]
  exact add_le_add
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hw 3) (abs_nonneg _))
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hw 4) (abs_nonneg _))

end XWT
end Christodoulou.Bondi
