module
public import Christodoulou.Frozen.Bondi.ConstantDataField
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.DerivLinearStep
public import Christodoulou.Frozen.Bondi.StepValueBound
public import Christodoulou.Frozen.Bondi.StepDerivBound
public import Christodoulou.Frozen.Bondi.StepEta
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic
import Christodoulou.Frozen.Bondi.IsCharacteristicMemIcc
import Christodoulou.Frozen.Bondi.IsCharacteristicLinearStepEq
import Christodoulou.Frozen.Bondi.AbsDeriv2GBarXLe
import Christodoulou.Frozen.Bondi.AbsDerivLinearSourceLe
import Christodoulou.Frozen.Bondi.HasDerivWithinAtLinearStep
import Christodoulou.Bondi.LinearStepRegularity
import Christodoulou.Bondi.CoefficientRegularity
import Christodoulou.Bondi.LinearStepBasic

/-!
# Bounds and ball preservation for the linear iteration

The characteristic formulas give weighted bounds for the value and radial derivative.
The explicit time `stepEta` makes their sum smaller than the X-ball radius. Constant
initial fields and the linear step therefore lie in the same ball. The decay-slice
bridge supplies a finite least upper bound for the weighted initial data norm.
-/

public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi
namespace XIt


theorem memXBall_constantDataField (u₀ : ℝ≥0) (d : ℝ) (data : C(ℝ≥0, ℝ))
    (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d) :
    MemXBall u₀ d (constantDataField data) := by
  refine ⟨fun u _ => hdata.1.1, ?_, fun u _ r => hbound r⟩
  have hc := hdata.1.1.continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by norm_num)
  exact hc.comp continuous_snd.continuousOn (fun p hp => hp.2)

private lemma x_nonneg {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) : 0 ≤ x := by
  have h := hH.2.2 0 (show (0 : ℝ≥0) ≤ u₀ from bot_le) 0
  have h0 : 0 ≤ (1 + ((0 : ℝ≥0) : ℝ)) ^ 3 * |H (0, 0)| +
      (1 + ((0 : ℝ≥0) : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => H (0, Real.toNNReal s)) (Ici 0) 0| := by positivity
  exact h0.trans h

private lemma weight_transfer {r ρ z C : ℝ} {n k : ℕ} (hr : 0 ≤ r) (hρ : r ≤ ρ)
    (hn : n ≤ k) (hb : (1 + ρ) ^ k * |z| ≤ C) : (1 + r) ^ n * |z| ≤ C := by
  apply le_trans _ hb
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  exact (pow_le_pow_left₀ (show 0 ≤ 1 + r by linarith) (show 1 + r ≤ 1 + ρ by linarith) n).trans
    (pow_le_pow_right₀ (by linarith) hn)

private lemma weighted_integral_bound {v w C : ℝ} {f : ℝ → ℝ}
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hb : ∀ s ∈ Icc 0 v, w * |f s| ≤ C) :
    w * |∫ s in (0 : ℝ)..v, f s| ≤ v * C := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := v) (f := fun s => w * f s) (C := C) (fun s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
      exact hb s (Ioc_subset_Icc_self ((uIoc_of_le hv ▸ hs))))
  rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hw, sub_zero, abs_of_nonneg hv] at hi
  simpa only [mul_comm] using hi

private lemma characteristic_exp_bound {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H}
    {v : Icc (0 : ℝ) u₀} {r : ℝ≥0} {χ : ℝ → ℝ}
    (_hχ : IsCharacteristic hH v r χ) {s : ℝ} (hs : s ∈ Icc 0 (v : ℝ)) :
    exp (∫ τ in s..(v : ℝ), linearCoeff hH τ.toNNReal (χ τ).toNNReal) ≤
      exp (π * x ^ 2 / 12 * (u₀ : ℝ)) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := (v : ℝ))
    (f := fun τ => linearCoeff hH τ.toNNReal (χ τ).toNNReal)
    (C := π * x ^ 2 / 12) (fun τ _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (XCoef.linearCoeff_nonneg hH _ _)]
      convert XCoef.linearCoeff_le_uniform hH τ.toNNReal (χ τ).toNNReal using 1
      ring)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)] at hi
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |∫ τ in s..(v : ℝ), linearCoeff hH τ.toNNReal (χ τ).toNNReal| := le_abs_self _
    _ ≤ (π * x ^ 2 / 12) * ((v : ℝ) - s) := hi
    _ ≤ (π * x ^ 2 / 12) * (u₀ : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith only [v.2.2, hs.1]

/-- Value estimate requires only continuous data and its value bound. -/
theorem linearStep_value_bound {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ)) (d : ℝ)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| ≤ d)
    (u r : ℝ≥0) :
    (1 + (r : ℝ)) ^ 3 * |linearStep hH data u r| ≤ stepValueBound x d u₀ := by
  let v : Icc (0 : ℝ) u₀ :=
    ⟨min u u₀, (min u u₀).coe_nonneg, by exact_mod_cast min_le_right u u₀⟩
  let χ := characteristic hH v r
  have hχ : IsCharacteristic hH v r χ := isCharacteristic_characteristic hH v r
  have hformula := hχ.linearStep_eq data ⟨v.2.1, le_rfl⟩
  rw [hχ.1, Real.toNNReal_coe] at hformula
  have hvNN : (v : ℝ).toNNReal = min u u₀ := by
    change (min (u : ℝ) (u₀ : ℝ)).toNNReal = min u u₀
    rw [← NNReal.coe_min, Real.toNNReal_coe]
  rw [hvNN] at hformula
  have hclamp : linearStep hH data (min u u₀) r = linearStep hH data u r := by
    simp only [linearStep, NNReal.coe_min, min_assoc, min_self]
  rw [hclamp] at hformula
  let E := exp (π * x ^ 2 / 12 * (u₀ : ℝ))
  let F := π * x ^ 3 / 6
  let W := (1 + (r : ℝ)) ^ 3
  have hx0 := x_nonneg hH
  have hd : 0 ≤ d := by simpa using (abs_nonneg (data 0)).trans (by simpa using hbound 0)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hχr : ∀ s ∈ Icc 0 (v : ℝ), (r : ℝ) ≤ (χ s).toNNReal := by
    intro s hs
    rw [Real.coe_toNNReal _ (r.coe_nonneg.trans (hχ.mem_Icc hs).1)]
    exact (hχ.mem_Icc hs).1
  have hd0 : W * |data (χ 0).toNNReal| ≤ d :=
    weight_transfer r.coe_nonneg (hχr 0 ⟨le_rfl, v.2.1⟩) le_rfl (hbound _)
  have hsource : ∀ s ∈ Icc 0 (v : ℝ), W * |linearSource hH s.toNNReal (χ s).toNNReal| ≤ F := by
    intro s hs
    apply weight_transfer r.coe_nonneg (hχr s hs) (n := 3) (k := 3) le_rfl
    have hb := XCoef.abs_linearSource_le hH s.toNNReal (χ s).toNNReal
    have hp : 0 < (1 + ((χ s).toNNReal : ℝ)) ^ 3 := by positivity
    have hb' := (le_div_iff₀ (show 0 < 6 * (1 + ((χ s).toNNReal : ℝ)) ^ 3 by positivity)).mp hb
    dsimp only [F]
    nlinarith only [hb']
  have hexp : ∀ s ∈ Icc 0 (v : ℝ),
      exp (∫ τ in s..(v : ℝ), linearCoeff hH τ.toNNReal (χ τ).toNNReal) ≤ E :=
    fun s hs => characteristic_exp_bound hχ hs
  have hint : W * |∫ s in (0 : ℝ)..(v : ℝ),
      exp (∫ τ in s..(v : ℝ), linearCoeff hH τ.toNNReal (χ τ).toNNReal) *
        linearSource hH s.toNNReal (χ s).toNNReal| ≤ (v : ℝ) * (E * F) := by
    apply weighted_integral_bound v.2.1 hW
    intro s hs
    rw [abs_mul, abs_of_pos (exp_pos _)]
    calc
      _ = exp (∫ τ in s..(v : ℝ), linearCoeff hH τ.toNNReal (χ τ).toNNReal) *
          (W * |linearSource hH s.toNNReal (χ s).toNNReal|) := by ring
      _ ≤ E * F := mul_le_mul (hexp s hs) (hsource s hs) (by positivity) (exp_pos _).le
  rw [hformula]
  change W * |data (χ 0).toNNReal *
    exp (∫ s in (0 : ℝ)..(v : ℝ), linearCoeff hH s.toNNReal (χ s).toNNReal) +
    ∫ s in (0 : ℝ)..(v : ℝ),
      exp (∫ τ in s..(v : ℝ), linearCoeff hH τ.toNNReal (χ τ).toNNReal) *
        linearSource hH s.toNNReal (χ s).toNNReal| ≤ E * (d + (u₀ : ℝ) * F)
  calc
    _ ≤ W * (|data (χ 0).toNNReal *
        exp (∫ s in (0 : ℝ)..(v : ℝ), linearCoeff hH s.toNNReal (χ s).toNNReal)| +
        |∫ s in (0 : ℝ)..(v : ℝ),
          exp (∫ τ in s..(v : ℝ), linearCoeff hH τ.toNNReal (χ τ).toNNReal) *
            linearSource hH s.toNNReal (χ s).toNNReal|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hW
    _ ≤ E * d + (v : ℝ) * (E * F) := by
      rw [mul_add, abs_mul, abs_of_pos (exp_pos _)]
      apply add_le_add _ hint
      calc
        _ = (W * |data (χ 0).toNNReal|) *
            exp (∫ s in (0 : ℝ)..(v : ℝ), linearCoeff hH s.toNNReal (χ s).toNNReal) := by ring
        _ ≤ d * E := mul_le_mul hd0 (hexp 0 ⟨le_rfl, v.2.1⟩) (exp_pos _).le hd
        _ = E * d := mul_comm _ _
    _ ≤ E * d + (u₀ : ℝ) * (E * F) := by gcongr; exact v.2.2
    _ = _ := by ring


theorem linearStep_deriv_bound {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0)) (d : ℝ)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d)
    (u r : ℝ≥0) :
    (1 + (r : ℝ)) ^ 4 * |derivLinearStep hH data hdata u r| ≤
      stepDerivBound x d u₀ := by
  let v : Icc (0 : ℝ) u₀ :=
    ⟨min u u₀, (min u u₀).coe_nonneg, by exact_mod_cast min_le_right u u₀⟩
  let χ := characteristic hH v r
  let A := fun s : ℝ => ∫ τ in s..(v : ℝ), linearCoeff hH τ.toNNReal (χ τ).toNNReal
  let E := exp (2 * (π * x ^ 2 / 12) * (u₀ : ℝ))
  let B := π * x ^ 2 / 2
  let D := 7 * π * x ^ 3 / 12
  let M := stepValueBound x d u₀
  let W := (1 + (r : ℝ)) ^ 4
  have hχ : IsCharacteristic hH v r χ := isCharacteristic_characteristic hH v r
  have hx0 := x_nonneg hH
  have hvbound : ∀ ρ : ℝ≥0, (1 + (ρ : ℝ)) ^ 3 * |data ρ| ≤ d := by
    intro ρ
    exact (le_add_of_nonneg_right (by positivity)).trans (hbound ρ)
  have hdbound : ∀ ρ : ℝ≥0, (1 + (ρ : ℝ)) ^ 4 *
      |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) ρ| ≤ d := by
    intro ρ
    exact (le_add_of_nonneg_left (by positivity)).trans (hbound ρ)
  have hd : 0 ≤ d := by simpa using (abs_nonneg (data 0)).trans (by simpa using hvbound 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hM : 0 ≤ M := by dsimp [M, stepValueBound]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hχr : ∀ s ∈ Icc 0 (v : ℝ), (r : ℝ) ≤ (χ s).toNNReal := by
    intro s hs
    rw [Real.coe_toNNReal _ (r.coe_nonneg.trans (hχ.mem_Icc hs).1)]
    exact (hχ.mem_Icc hs).1
  have hexp : ∀ s ∈ Icc 0 (v : ℝ), exp (2 * A s) ≤ E := by
    intro s hs
    have hb := characteristic_exp_bound hχ hs
    calc
      exp (2 * A s) = exp (A s) * exp (A s) := by rw [← exp_add]; congr 1; ring
      _ ≤ exp (π * x ^ 2 / 12 * (u₀ : ℝ)) * exp (π * x ^ 2 / 12 * (u₀ : ℝ)) :=
        mul_le_mul hb hb (exp_pos _).le (exp_pos _).le
      _ = E := by dsimp [E]; rw [← exp_add]; congr 1; ring
  have hd0 : W * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (χ 0)| ≤ d := by
    have hc0 : ((χ 0).toNNReal : ℝ) = χ 0 :=
      Real.coe_toNNReal _ (r.coe_nonneg.trans (hχ.mem_Icc ⟨le_rfl, v.2.1⟩).1)
    have hb := weight_transfer r.coe_nonneg (hχr 0 ⟨le_rfl, v.2.1⟩) (n := 4) le_rfl
      (hdbound (χ 0).toNNReal)
    rwa [hc0] at hb
  let ar := fun s : ℝ => 1 / 2 * deriv2GBarX hH s.toNNReal (χ s).toNNReal
  let S := fun s : ℝ => linearStep hH data s.toNNReal (χ s).toNNReal
  let fr := fun s : ℝ => -ar s * hBarX u₀ H s.toNNReal (χ s).toNNReal -
    linearCoeff hH s.toNNReal (χ s).toNNReal * derivHBarX hH s.toNNReal (χ s).toNNReal
  have hprod : ∀ s ∈ Icc 0 (v : ℝ), W * |ar s * S s| ≤ B * M := by
    intro s hs
    have ha : (1 + ((χ s).toNNReal : ℝ)) ^ 3 * |ar s| ≤ B := by
      have hb := abs_deriv2GBarX_le hH s.toNNReal (χ s).toNNReal
      have hb' := (le_div_iff₀ (show 0 < (1 + ((χ s).toNNReal : ℝ)) ^ 3 by positivity)).mp hb
      dsimp only [ar, B]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      nlinarith only [hb']
    have hS : (1 + ((χ s).toNNReal : ℝ)) ^ 3 * |S s| ≤ M :=
      linearStep_value_bound hH data d hvbound _ _
    have hm := mul_le_mul ha hS (by positivity) hB
    have hb : (1 + ((χ s).toNNReal : ℝ)) ^ 6 * |ar s * S s| ≤ B * M := by
      rw [abs_mul]
      convert hm using 1
      ring
    exact weight_transfer r.coe_nonneg (hχr s hs) (n := 4) (k := 6) (by norm_num) hb
  have hfr : ∀ s ∈ Icc 0 (v : ℝ), W * |fr s| ≤ D := by
    intro s hs
    have hb := abs_deriv_linearSource_le hH s.toNNReal (χ s).toNNReal
    have hb' := (le_div_iff₀ (show 0 < 12 * (1 + ((χ s).toNNReal : ℝ)) ^ 4 by positivity)).mp hb
    have hh : (1 + ((χ s).toNNReal : ℝ)) ^ 4 * |fr s| ≤ D := by
      dsimp only [fr, ar, D]
      nlinarith only [hb']
    exact weight_transfer r.coe_nonneg (hχr s hs) (n := 4) le_rfl hh
  have hint : W * |∫ s in (0 : ℝ)..(v : ℝ), exp (2 * A s) * (ar s * S s + fr s)| ≤
      (v : ℝ) * (E * (B * M + D)) := by
    apply weighted_integral_bound v.2.1 hW
    intro s hs
    rw [abs_mul, abs_of_pos (exp_pos _)]
    have hb : W * |ar s * S s + fr s| ≤ B * M + D := by
      calc
        _ ≤ W * (|ar s * S s| + |fr s|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hW
        _ = W * |ar s * S s| + W * |fr s| := by ring
        _ ≤ _ := add_le_add (hprod s hs) (hfr s hs)
    calc
      _ = exp (2 * A s) * (W * |ar s * S s + fr s|) := by ring
      _ ≤ E * (B * M + D) := mul_le_mul (hexp s hs) hb (by positivity) (exp_pos _).le
  change W * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (χ 0) * exp (2 * A 0) +
    ∫ s in (0 : ℝ)..(v : ℝ), exp (2 * A s) * (ar s * S s + fr s)| ≤
      E * (d + (u₀ : ℝ) * (D + B * M))
  calc
    _ ≤ W * (|derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (χ 0) * exp (2 * A 0)| +
        |∫ s in (0 : ℝ)..(v : ℝ), exp (2 * A s) * (ar s * S s + fr s)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hW
    _ ≤ d * E + (v : ℝ) * (E * (B * M + D)) := by
      rw [mul_add, abs_mul, abs_of_pos (exp_pos _)]
      apply add_le_add _ hint
      calc
        _ = (W * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (χ 0)|) *
            exp (2 * A 0) := by ring
        _ ≤ d * E := mul_le_mul hd0 (hexp 0 ⟨le_rfl, v.2.1⟩) (exp_pos _).le hd
    _ ≤ d * E + (u₀ : ℝ) * (E * (B * M + D)) := by gcongr; exact v.2.2
    _ = _ := by ring

private lemma exp_linear_majorant (c T : ℝ) (hc : 0 ≤ c) (hT : 0 ≤ T)
    (hT1 : T ≤ 1) : exp (c * T) ≤ 1 + T * c * exp c := by
  have he := Real.add_one_le_exp (-(c * T))
  have hm := mul_le_mul_of_nonneg_right he (exp_pos (c * T)).le
  have hi : exp (-(c * T)) * exp (c * T) = 1 := by
    rw [← exp_add]; simp
  rw [hi] at hm
  have hb : exp (c * T) ≤ exp c := Real.exp_le_exp.mpr (by nlinarith)
  have hb' := mul_le_mul_of_nonneg_left hb (mul_nonneg hT hc)
  nlinarith only [hm, hb']


theorem stepEta_pos_and_bound (d x : ℝ) (hd : 0 ≤ d) (hx : 2 * d < x) :
    0 < stepEta x d ∧ ∀ T : ℝ, 0 ≤ T → T < stepEta x d →
      stepValueBound x d T + stepDerivBound x d T < x := by
  let L := π * x ^ 2 / 12
  let F := π * x ^ 3 / 6
  let B := π * x ^ 2 / 2
  let D := 7 * π * x ^ 3 / 12
  let Mstar := exp L * (d + F)
  let Cstar := exp (2 * L) * (4 * d * L + F + D + B * Mstar)
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hM : 0 ≤ Mstar := mul_nonneg (exp_pos _).le (add_nonneg hd hF)
  have hC : 0 ≤ Cstar := by dsimp [Cstar]; positivity
  change 0 < min 1 ((x - 2 * d) / (2 * (1 + Cstar))) ∧ _
  constructor
  · exact lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  intro T hT hη
  change T < min 1 ((x - 2 * d) / (2 * (1 + Cstar))) at hη
  have hT1 : T ≤ 1 := (lt_of_lt_of_le hη (min_le_left _ _)).le
  have hsmall : T * (2 * (1 + Cstar)) < x - 2 * d :=
    (lt_div_iff₀ (by positivity)).mp (lt_of_lt_of_le hη (min_le_right _ _))
  have heL := exp_linear_majorant L T hL hT hT1
  have he2L := exp_linear_majorant (2 * L) T (by positivity) hT hT1
  have heLT : exp (L * T) ≤ exp L := Real.exp_le_exp.mpr (by nlinarith)
  have heL2 : exp L ≤ exp (2 * L) := Real.exp_le_exp.mpr (by linarith)
  have heLT2 : exp (L * T) ≤ exp (2 * L) := heLT.trans heL2
  have hMb : stepValueBound x d T ≤ Mstar := by
    change exp (L * T) * (d + T * F) ≤ exp L * (d + F)
    exact mul_le_mul heLT (by nlinarith) (by positivity) (exp_pos _).le
  have hv : stepValueBound x d T ≤ d + T * exp (2 * L) * (d * L + F) := by
    change exp (L * T) * (d + T * F) ≤ _
    have h1 := mul_le_mul_of_nonneg_right heL hd
    have h2 := mul_le_mul_of_nonneg_right heLT2 (mul_nonneg hT hF)
    have h3 := mul_le_mul_of_nonneg_left heL2 (mul_nonneg hd (mul_nonneg hT hL))
    nlinarith only [h1, h2, h3]
  have hn : stepDerivBound x d T ≤ d + T * exp (2 * L) * (2 * d * L + D + B * Mstar) := by
    change exp (2 * L * T) * (d + T * (D + B * stepValueBound x d T)) ≤ _
    have h1 := mul_le_mul_of_nonneg_right he2L hd
    have h2 : exp (2 * L * T) ≤ exp (2 * L) := Real.exp_le_exp.mpr (by nlinarith)
    have h3 : D + B * stepValueBound x d T ≤ D + B * Mstar := by gcongr
    have h4 := mul_le_mul h2 h3 (by dsimp [stepValueBound]; positivity) (exp_pos _).le
    have h5 := mul_le_mul_of_nonneg_left h4 hT
    nlinarith only [h1, h5]
  have hsum : stepValueBound x d T + stepDerivBound x d T ≤ 2 * d + T * Cstar := by
    have hdl : 0 ≤ T * exp (2 * L) * d * L := by positivity
    dsimp [Cstar]
    nlinarith only [hv, hn, hdl]
  have htc : 0 ≤ T * Cstar := mul_nonneg hT hC
  linarith only [hsum, hsmall, hT, htc]


theorem linearStepMap_memXBall {u₀ : ℝ≥0} {d x : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x) (hT : (u₀ : ℝ) < stepEta x d)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d)
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) :
    MemXBall u₀ x (linearStepMap hH data) := by
  have hC := hdata.1.1
  have hreg := XReg.linearStep_radial_regular hH data hC
  refine ⟨fun u _ => hreg.1 u, hreg.2, ?_⟩
  intro u hu r
  have hdv : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| ≤ d := by
    intro r
    exact (le_add_of_nonneg_right (by positivity)).trans (hbound r)
  have hv := linearStep_value_bound hH data d hdv u r
  have hder := linearStep_deriv_bound hH data hC d hbound u r
  have heq := (hasDerivWithinAt_linearStep hH data hC u r).derivWithin
    (uniqueDiffOn_Ici 0 _ r.coe_nonneg)
  change (1 + (r : ℝ)) ^ 3 * |linearStep hH data u r| +
    (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => linearStep hH data u s.toNNReal) (Ici 0) r| ≤ x
  rw [heq]
  exact (add_le_add hv hder).trans ((stepEta_pos_and_bound d x hd hx).2 u₀ u₀.coe_nonneg hT).le


theorem initial_memXBall {u₀ : ℝ≥0} {d x : ℝ} (hd : 0 ≤ d) (hx : 2 * d < x)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d) :
    MemXBall u₀ x (constantDataField data) := by
  have hb := memXBall_constantDataField u₀ d data hdata hbound
  refine ⟨hb.1, hb.2.1, ?_⟩
  intro u hu r
  exact (hb.2.2 u hu r).trans (by linarith only [hd, hx])

private lemma weighted_bound_of_decay (f : ℝ → ℝ) (n : ℕ)
    (hc : ContinuousOn f (Ici 0))
    (hdec : Asymptotics.IsBigO Filter.atTop f (fun s : ℝ => s ^ (-(n : ℤ)))) :
    ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s → (1 + s) ^ n * |f s| ≤ C := by
  obtain ⟨c, hcpos, htail⟩ := Asymptotics.isBigO_iff'.mp hdec
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp htail
  let R' := max R 1
  have hcont : ContinuousOn (fun s : ℝ => (1 + s) ^ n * |f s|) (Icc 0 R') :=
    ((continuous_const.add continuous_id).pow n).continuousOn.mul
      (hc.mono Icc_subset_Ici_self).abs
  obtain ⟨m, hm⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max m (c * 2 ^ n), ?_⟩
  intro s hs
  by_cases hsR : s ≤ R'
  · exact (hm (Set.mem_image_of_mem _ ⟨hs, hsR⟩)).trans (le_max_left _ _)
  have hs1 : 1 ≤ s := (le_max_right R 1).trans (le_of_not_ge hsR)
  have hspos : 0 < s := by linarith
  have hb := hR s ((le_max_left R 1).trans (le_of_not_ge hsR))
  simp only [Real.norm_eq_abs, zpow_neg, zpow_natCast, abs_inv, abs_pow,
    abs_of_pos hspos] at hb
  have hp : (1 + s) ^ n ≤ (2 * s) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  have hb' : |f s| * s ^ n ≤ c :=
    (le_div_iff₀ (pow_pos hspos n)).mp (by simpa only [div_eq_mul_inv] using hb)
  have h1 := mul_le_mul_of_nonneg_right hp (abs_nonneg (f s))
  have h2 := mul_le_mul_of_nonneg_left hb' (show (0 : ℝ) ≤ 2 ^ n by positivity)
  apply le_trans _ (le_max_right _ _)
  rw [mul_pow] at h1
  nlinarith only [h1, h2]


theorem isDecaySlice_exists_data_bound (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) :
    ∃ d : ℝ, 0 ≤ d ∧ IsLUB (Set.range (fun r : ℝ≥0 =>
      (1 + (r : ℝ)) ^ 3 * |data r| + (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r|)) d := by
  let f := fun s : ℝ => data s.toNNReal
  have hC := hdata.1.1
  obtain ⟨C, hCbound⟩ := weighted_bound_of_decay f 3 hC.continuousOn (by
    simpa [f] using hdata.1.2)
  have hderC := hC.continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by norm_num)
  have hderdec : Asymptotics.IsBigO Filter.atTop (derivWithin f (Ici 0))
      (fun s : ℝ => s ^ (-(4 : ℤ))) := by
    apply hdata.2.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with s hs
    exact (derivWithin_of_mem_nhds (Ici_mem_nhds hs)).symm
  obtain ⟨D, hDbound⟩ := weighted_bound_of_decay (derivWithin f (Ici 0)) 4 hderC hderdec
  let S := Set.range (fun r : ℝ≥0 => (1 + (r : ℝ)) ^ 3 * |data r| +
    (1 + (r : ℝ)) ^ 4 * |derivWithin f (Ici 0) r|)
  have hS : BddAbove S := by
    refine ⟨C + D, ?_⟩
    rintro y ⟨r, rfl⟩
    have hv := hCbound r r.coe_nonneg
    simp only [f, Real.toNNReal_coe] at hv
    exact add_le_add hv (hDbound r r.coe_nonneg)
  have hne : S.Nonempty := Set.range_nonempty _
  have hlub : IsLUB S (sSup S) := isLUB_csSup hne hS
  refine ⟨sSup S, ?_, hlub⟩
  have h0 := hlub.1 (Set.mem_range_self (0 : ℝ≥0))
  exact (show (0 : ℝ) ≤ (1 + ((0 : ℝ≥0) : ℝ)) ^ 3 * |data 0| +
    (1 + ((0 : ℝ≥0) : ℝ)) ^ 4 * |derivWithin f (Ici 0) 0| by positivity).trans h0

end XIt
end Christodoulou.Bondi
