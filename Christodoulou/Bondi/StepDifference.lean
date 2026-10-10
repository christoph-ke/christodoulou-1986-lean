module
public import Christodoulou.Frozen.Bondi.Characteristic
public import Christodoulou.Frozen.Bondi.StepDelta
public import Christodoulou.Frozen.Bondi.LinearStepClassical
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.XBallIterateRec
import Christodoulou.Frozen.Bondi.HasDerivWithinAtLinearStep
import Christodoulou.Frozen.Bondi.GBarXPos
import Christodoulou.Frozen.Bondi.GBarXLeOne
import Christodoulou.Bondi.CoefficientRegularity
import Christodoulou.Frozen.Bondi.IsCharacteristicMemIcc
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic
import Christodoulou.Frozen.Bondi.LinearStepZero
import Christodoulou.Frozen.Bondi.ContinuousDerivLinearStep
import Christodoulou.Frozen.Bondi.ContinuousDerivGBarX
import Christodoulou.Frozen.Bondi.ContinuousGBarX
import Christodoulou.Bondi.LinearStepBasic
import Christodoulou.Bondi.LinearODE
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Differences and time bounds for the linear step

The explicit contraction time is positive. Composing the classical step equation with a
characteristic gives the difference integral (9.27) and its absolute bound. The same equation
gives the printed bound (7.60), including the degenerate strip and the initial constant iterate.
-/

public section

open Set MeasureTheory Real
open scoped NNReal ContDiff

namespace Christodoulou.Bondi
namespace XDiff

/-- The explicit contraction time is positive and gives contraction factor at most `½`. -/
theorem stepDelta_pos_and_bound (x : ℝ) :
    0 < stepDelta x ∧ ∀ T : ℝ, 0 ≤ T → T < stepDelta x →
      T * exp (π * x ^ 2 / 12 * T) * (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)) ≤ 1 / 2 := by
  let L := π * x ^ 2 / 12
  let C := π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp : 0 < 2 * (1 + exp L * C) := by positivity
  change 0 < min 1 (1 / (2 * (1 + exp L * C))) ∧ _
  refine ⟨lt_min (by norm_num) (div_pos (by norm_num) hp), ?_⟩
  intro T hT hδ
  change T < min 1 (1 / (2 * (1 + exp L * C))) at hδ
  have hT1 : T ≤ 1 := (hδ.trans_le (min_le_left _ _)).le
  have hsmall := (lt_div_iff₀ hp).mp (hδ.trans_le (min_le_right _ _))
  have he : exp (L * T) ≤ exp L :=
    exp_le_exp.mpr (by nlinarith only [hL, hT1])
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he hT) hC
  change T * exp (L * T) * C ≤ 1 / 2
  have htc : 0 ≤ T * exp L * C := by positivity
  linarith only [hb, hsmall, hT, htc]

private theorem x_nonneg {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) : 0 ≤ x := by
  have hb := hH.2.2 0 (by positivity) 0
  exact (by positivity : 0 ≤ (1 + ((0 : ℝ≥0) : ℝ)) ^ 3 * |H (0, 0)| +
    (1 + ((0 : ℝ≥0) : ℝ)) ^ 4 *
      |derivWithin (fun s : ℝ => H (0, s.toNNReal)) (Ici 0) 0|).trans hb

private theorem time_weight (r : ℝ) (hr : 0 ≤ r) :
    r / (1 + r) ^ 3 + r / (1 + r) ≤ 1 := by
  have hp : 0 < 1 + r := by positivity
  apply (mul_le_mul_iff_of_pos_right (pow_pos hp 3)).mp
  field_simp
  nlinarith [sq_nonneg r, mul_nonneg hr (sq_nonneg r)]

/-- The time derivative of a step in the same ball satisfies the printed bound (7.60). -/
theorem linearStep_time_bound {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (hS : MemXBall u₀ x (linearStepMap hH data))
    (u r : ℝ≥0) (hu : u ≤ u₀) :
    |derivWithin (fun t : ℝ => linearStep hH data t.toNNReal r) (Icc 0 (u₀ : ℝ)) u| ≤
      1 / 2 * x * (1 + π / 3 * x ^ 2) / (1 + (r : ℝ)) ^ 3 := by
  have hx := x_nonneg hH
  rcases eq_or_lt_of_le (show 0 ≤ u₀ from bot_le) with hzero | hpos
  · subst u₀
    have hu0 : u = 0 := le_antisymm hu bot_le
    subst u
    rw [NNReal.coe_zero, Icc_self]
    rw [derivWithin_zero_of_not_accPt (by
      rw [accPt_principal_iff_nhdsWithin]
      simp only [sdiff_self, nhdsWithin_empty]
      exact Filter.not_neBot.mpr rfl)]
    rw [abs_zero]
    positivity
  have hd := ((linearStep_classical hH hpos data hdata).1 u hu r).derivWithin
    (uniqueDiffOn_Icc (show (0 : ℝ) < u₀ from hpos) u ⟨u.coe_nonneg, hu⟩)
  rw [hd]
  let w := 1 + (r : ℝ)
  let S := linearStep hH data u r
  let q := derivLinearStep hH data hdata u r
  let a := linearCoeff hH u r
  have hw : 0 < w := by dsimp [w]; positivity
  have hw1 : 1 ≤ w := by dsimp [w]; linarith only [r.coe_nonneg]
  have hqeq := (hasDerivWithinAt_linearStep hH data hdata u r).derivWithin
    (uniqueDiffOn_Ici 0 r r.coe_nonneg)
  have hbudget := hS.2.2 u hu r
  change w ^ 3 * |S| + w ^ 4 *
    |derivWithin (fun s : ℝ => linearStep hH data u s.toNNReal) (Ici 0) r| ≤ x at hbudget
  rw [hqeq] at hbudget
  have hSv : |S| ≤ x / w ^ 3 := (le_div_iff₀ (pow_pos hw 3)).mpr (by
    nlinarith only [hbudget, mul_nonneg (pow_pos hw 4).le (abs_nonneg q)])
  have hqv : |q| ≤ x / w ^ 4 := (le_div_iff₀ (pow_pos hw 4)).mpr (by
    nlinarith only [hbudget, mul_nonneg (pow_pos hw 3).le (abs_nonneg S)])
  have ha0 : 0 ≤ a := XCoef.linearCoeff_nonneg hH u r
  have ha : a ≤ π / 6 * x ^ 2 * (r : ℝ) / w ^ 3 := XCoef.linearCoeff_le hH u r
  have hh : |hBarX u₀ H u r| ≤ x / w := XCoef.abs_hBarX_le hH u r
  have hg0 := (gBarX_pos hH u r).le
  have hg := gBarX_le_one hH u r
  have hfirst : |gBarX hH u r / 2 * q| ≤ x / (2 * w ^ 4) := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hg0 (by norm_num))]
    calc
      _ ≤ (1 / 2) * (x / w ^ 4) :=
        mul_le_mul (div_le_div_of_nonneg_right hg (by norm_num)) hqv
          (abs_nonneg q) (by norm_num)
      _ = _ := by field_simp
  have hrest : |a * (S - hBarX u₀ H u r)| ≤
      (π / 6 * x ^ 2 * (r : ℝ) / w ^ 3) * (x / w ^ 3 + x / w) := by
    rw [abs_mul, abs_of_nonneg ha0]
    exact mul_le_mul ha ((abs_sub _ _).trans (add_le_add hSv hh))
      (abs_nonneg _) (by positivity)
  have htotal : |gBarX hH u r / 2 * q + a * (S - hBarX u₀ H u r)| ≤
      x / (2 * w ^ 4) +
        (π / 6 * x ^ 2 * (r : ℝ) / w ^ 3) * (x / w ^ 3 + x / w) :=
    (abs_add_le _ _).trans (add_le_add hfirst hrest)
  have hweight := time_weight (r : ℝ) r.coe_nonneg
  change (r : ℝ) / w ^ 3 + (r : ℝ) / w ≤ 1 at hweight
  have ht := mul_le_mul_of_nonneg_left hweight
    (show 0 ≤ π / 6 * x ^ 3 by positivity)
  have hxw : x / (2 * w) ≤ x / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * w)).mpr
    nlinarith only [hx, hw1]
  have harith : (x / (2 * w ^ 4) +
      (π / 6 * x ^ 2 * (r : ℝ) / w ^ 3) * (x / w ^ 3 + x / w)) * w ^ 3 =
      x / (2 * w) + π / 6 * x ^ 3 * ((r : ℝ) / w ^ 3 + (r : ℝ) / w) := by
    field_simp
  have hfinal : x / (2 * w ^ 4) +
      (π / 6 * x ^ 2 * (r : ℝ) / w ^ 3) * (x / w ^ 3 + x / w) ≤
        1 / 2 * x * (1 + π / 3 * x ^ 2) / w ^ 3 := by
    apply (le_div_iff₀ (pow_pos hw 3)).mpr
    rw [harith]
    nlinarith only [ht, hxw]
  have he : gBarX hH u r / 2 * derivLinearStep hH data hdata u r +
      linearCoeff hH u r * linearStep hH data u r + linearSource hH u r =
      gBarX hH u r / 2 * q + a * (S - hBarX u₀ H u r) := by
    dsimp [q, a, S, linearSource]
    ring
  rw [he]
  exact htotal.trans hfinal

/-- Every canonical iterate, including the constant initial field, satisfies (7.60). -/
theorem xBallIterate_time_bound {u₀ : ℝ≥0} {d x : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x) (hT : (u₀ : ℝ) < stepEta x d)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d)
    (n : ℕ) (u r : ℝ≥0) (hu : u ≤ u₀) :
    |derivWithin (fun t : ℝ => (xBallIterate hd hx hT data hdata hbound n).val (t.toNNReal, r))
      (Icc 0 (u₀ : ℝ)) u| ≤
      1 / 2 * x * (1 + π / 3 * x ^ 2) / (1 + (r : ℝ)) ^ 3 := by
  have hrec := xBallIterate_rec hd hx hT data hdata hbound
  cases n with
  | zero =>
    rw [hrec.1]
    change |derivWithin (Function.const ℝ (data r)) (Icc 0 (u₀ : ℝ)) u| ≤ _
    simp only [derivWithin_const, Pi.zero_apply, abs_zero]
    have hx0 : 0 < x := by linarith only [hd, hx]
    positivity
  | succ n =>
    rw [hrec.2.1 n]
    exact linearStep_time_bound (xBallIterate hd hx hT data hdata hbound n).property
      data hdata.1.1 (by
        rw [← hrec.2.1 n]
        exact (xBallIterate hd hx hT data hdata hbound (n + 1)).property) u r hu

private theorem chain_rectangle {T : ℝ} (hT : 0 < T) {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ Ici 0)) {P Q : ℝ × ℝ → ℝ}
    (htime : ∀ p ∈ Icc 0 T ×ˢ Ici 0,
      HasDerivWithinAt (fun t => f (t, p.2)) (P p) (Icc 0 T) p.1)
    (hrad : ∀ p ∈ Icc 0 T ×ˢ Ici 0,
      HasDerivWithinAt (fun t => f (p.1, t)) (Q p) (Ici 0) p.2)
    {V : ℝ} {χ : ℝ → ℝ} {t c : ℝ}
    (hχ : HasDerivWithinAt χ c (Icc 0 V) t)
    (hmap : MapsTo (fun s => (s, χ s)) (Icc 0 V) (Icc 0 T ×ˢ Ici 0))
    (ht : t ∈ Icc 0 V) :
    HasDerivWithinAt (fun s => f (s, χ s)) (P (t, χ t) + c * Q (t, χ t))
      (Icc 0 V) t := by
  let p := (t, χ t)
  have hp : p ∈ Icc 0 T ×ˢ Ici 0 := hmap ht
  have hfd := (hf.differentiableOn (by norm_num : (1 : ℕ∞ω) ≠ 0) p hp).hasFDerivWithinAt
  let L := fderivWithin ℝ f (Icc 0 T ×ˢ Ici 0) p
  have hfst : HasDerivWithinAt (fun s => f (s, p.2)) (L (1, 0)) (Icc 0 T) p.1 := by
    apply hfd.comp_hasDerivWithinAt (t := Icc 0 T ×ˢ Ici 0) p.1
      ((hasDerivWithinAt_id p.1 (Icc 0 T)).prodMk (hasDerivWithinAt_const p.1 _ p.2))
      (fun s hs => ⟨hs, hp.2⟩)
  have hsnd : HasDerivWithinAt (fun s => f (p.1, s)) (L (0, 1)) (Ici 0) p.2 := by
    apply hfd.comp_hasDerivWithinAt (t := Icc 0 T ×ˢ Ici 0) p.2
      ((hasDerivWithinAt_const p.2 _ p.1).prodMk (hasDerivWithinAt_id p.2 (Ici 0)))
      (fun s hs => ⟨hp.1, hs⟩)
  have heP : L (1, 0) = P p :=
    (uniqueDiffOn_Icc hT p.1 hp.1).eq_deriv _ hfst (htime p hp)
  have heQ : L (0, 1) = Q p :=
    (uniqueDiffOn_Ici 0 p.2 hp.2).eq_deriv _ hsnd (hrad p hp)
  have hc := hfd.comp_hasDerivWithinAt t
    ((hasDerivWithinAt_id t (Icc 0 V)).prodMk hχ) hmap
  have he : L (1, c) = P p + c * Q p := by
    have hev : (1, c) = ((1, 0) : ℝ × ℝ) + c • ((0, 1) : ℝ × ℝ) := by ext <;> simp
    rw [hev, map_add, map_smul, heP, heQ, smul_eq_mul]
  change HasDerivWithinAt (fun s => f (s, χ s)) (L (1, c)) (Icc 0 V) t at hc
  rw [he] at hc
  exact hc


private theorem cross_step_deriv {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H}
    (hK : MemXBall u₀ x K) (hpos : 0 < u₀) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    {v : Icc (0 : ℝ) u₀} {r : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH v r χ) {t : ℝ} (ht : t ∈ Icc 0 (v : ℝ)) :
    HasDerivWithinAt (fun s : ℝ => linearStep hK data s.toNNReal (χ s).toNNReal)
      ((gBarX hK t.toNNReal (χ t).toNNReal -
          gBarX hH t.toNNReal (χ t).toNNReal) / 2 *
          derivLinearStep hK data hdata t.toNNReal (χ t).toNNReal +
        linearCoeff hK t.toNNReal (χ t).toNNReal *
          linearStep hK data t.toNNReal (χ t).toNNReal +
        linearSource hK t.toNNReal (χ t).toNNReal) (Icc 0 (v : ℝ)) t := by
  have hclass := linearStep_classical hK hpos data hdata
  let P := fun p : ℝ × ℝ => gBarX hK p.1.toNNReal p.2.toNNReal / 2 *
    derivLinearStep hK data hdata p.1.toNNReal p.2.toNNReal +
    linearCoeff hK p.1.toNNReal p.2.toNNReal *
      linearStep hK data p.1.toNNReal p.2.toNNReal +
    linearSource hK p.1.toNNReal p.2.toNNReal
  let Q := fun p : ℝ × ℝ =>
    derivLinearStep hK data hdata p.1.toNNReal p.2.toNNReal
  have htime : ∀ p ∈ Icc 0 (u₀ : ℝ) ×ˢ Ici 0,
      HasDerivWithinAt (fun t => linearStep hK data t.toNNReal p.2.toNNReal)
        (P p) (Icc 0 (u₀ : ℝ)) p.1 := by
    intro p hp
    have hu : p.1.toNNReal ≤ u₀ := Real.toNNReal_le_iff_le_coe.mpr hp.1.2
    simpa only [Real.coe_toNNReal _ hp.1.1] using hclass.1 p.1.toNNReal hu p.2.toNNReal
  have hrad : ∀ p ∈ Icc 0 (u₀ : ℝ) ×ˢ Ici 0,
      HasDerivWithinAt (fun t => linearStep hK data p.1.toNNReal t.toNNReal)
        (Q p) (Ici 0) p.2 := by
    intro p hp
    simpa only [Real.coe_toNNReal _ hp.2] using
      hasDerivWithinAt_linearStep hK data hdata p.1.toNNReal p.2.toNNReal
  have hmap : MapsTo (fun s => (s, χ s)) (Icc 0 (v : ℝ))
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) := by
    intro s hs
    exact ⟨⟨hs.1, hs.2.trans v.2.2⟩, r.coe_nonneg.trans (hχ.mem_Icc hs).1⟩
  have hc := chain_rectangle (show (0 : ℝ) < u₀ from hpos) hclass.2.2 htime hrad
    (hχ.2 t ht) hmap ht
  convert hc using 1
  dsimp [P, Q, charField]
  ring

/-- Two steps with common data differ by the local variation-of-constants integral (9.27). -/
theorem linearStep_difference_integral {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (v : Icc (0 : ℝ) u₀) (r : ℝ≥0) :
    let χ := characteristic hH v r
    let b := fun s : ℝ =>
      let u := s.toNNReal
      let ρ := (χ s).toNNReal
      (gBarX hH u ρ - gBarX hK u ρ) / 2 * derivLinearStep hK data hdata u ρ +
        (linearCoeff hH u ρ - linearCoeff hK u ρ) * linearStep hK data u ρ +
        linearSource hH u ρ - linearSource hK u ρ
    linearStep hH data (v : ℝ).toNNReal r - linearStep hK data (v : ℝ).toNNReal r =
      ∫ s in (0 : ℝ)..(v : ℝ),
        exp (∫ t in s..(v : ℝ), linearCoeff hH t.toNNReal (χ t).toNNReal) * b s := by
  dsimp only
  by_cases hv : (v : ℝ) = 0
  · simp only [hv, Real.toNNReal_zero, linearStep_zero, sub_self,
      intervalIntegral.integral_same]
  have hvpos : 0 < (v : ℝ) := lt_of_le_of_ne v.2.1 (Ne.symm hv)
  have hpos : 0 < u₀ := by exact_mod_cast hvpos.trans_le v.2.2
  let χ := characteristic hH v r
  have hχ : IsCharacteristic hH v r χ := isCharacteristic_characteristic hH v r
  let a := fun s : ℝ => linearCoeff hH s.toNNReal (χ s).toNNReal
  let b := fun s : ℝ =>
    (gBarX hH s.toNNReal (χ s).toNNReal -
        gBarX hK s.toNNReal (χ s).toNNReal) / 2 *
        derivLinearStep hK data hdata s.toNNReal (χ s).toNNReal +
      (linearCoeff hH s.toNNReal (χ s).toNNReal -
        linearCoeff hK s.toNNReal (χ s).toNNReal) *
        linearStep hK data s.toNNReal (χ s).toNNReal +
      linearSource hH s.toNNReal (χ s).toNNReal -
        linearSource hK s.toNNReal (χ s).toNNReal
  let W := fun s : ℝ => linearStep hH data s.toNNReal (χ s).toNNReal -
    linearStep hK data s.toNNReal (χ s).toNNReal
  have hp : ContinuousOn (fun s : ℝ => (s.toNNReal, (χ s).toNNReal))
      (Icc 0 (v : ℝ)) :=
    continuous_real_toNNReal.continuousOn.prodMk
      (continuous_real_toNNReal.comp_continuousOn (HasDerivWithinAt.continuousOn hχ.2))
  have haH : Continuous (fun p : ℝ≥0 × ℝ≥0 => linearCoeff hH p.1 p.2) :=
    continuous_const.mul (continuous_derivGBarX hH)
  have haK : Continuous (fun p : ℝ≥0 × ℝ≥0 => linearCoeff hK p.1 p.2) :=
    continuous_const.mul (continuous_derivGBarX hK)
  have hfH : Continuous (fun p : ℝ≥0 × ℝ≥0 => linearSource hH p.1 p.2) :=
    haH.neg.mul (XStep.continuous_hBarX u₀ H)
  have hfK : Continuous (fun p : ℝ≥0 × ℝ≥0 => linearSource hK p.1 p.2) :=
    haK.neg.mul (XStep.continuous_hBarX u₀ K)
  have ha : ContinuousOn a (Icc 0 (v : ℝ)) := haH.comp_continuousOn hp
  have hb : ContinuousOn b (Icc 0 (v : ℝ)) :=
    (((((continuous_gBarX hH).comp_continuousOn hp).sub
      ((continuous_gBarX hK).comp_continuousOn hp)).div_const 2).mul
      ((continuous_derivLinearStep hK data hdata).comp_continuousOn hp)).add
      (((haH.comp_continuousOn hp).sub (haK.comp_continuousOn hp)).mul
        ((continuous_linearStep hK data).comp_continuousOn hp)) |>.add
      (hfH.comp_continuousOn hp) |>.sub (hfK.comp_continuousOn hp)
  have hW : ∀ s ∈ Icc 0 (v : ℝ),
      HasDerivWithinAt W (a s * W s + b s) (Icc 0 (v : ℝ)) s := by
    intro s hs
    have hHder := cross_step_deriv hH hpos data hdata hχ hs
    have hKder := cross_step_deriv hK hpos data hdata hχ hs
    convert hHder.sub hKder using 1
    dsimp [W, a, b]
    ring
  have hzero : W 0 = LinODE.duhamel a b 0 0 := by
    simp only [W, Real.toNNReal_zero, linearStep_zero, sub_self, LinODE.duhamel_zero]
  have he := LinODE.linear_unique ha hW (fun s hs => LinODE.duhamel_deriv ha hb 0 hs)
    hzero (show (v : ℝ) ∈ Icc 0 (v : ℝ) from ⟨v.2.1, le_rfl⟩)
  change W v = _ at he
  dsimp only [W, LinODE.duhamel] at he
  rw [hχ.1, Real.toNNReal_coe, zero_mul, zero_add] at he
  exact he

/-- A pointwise source bound along the characteristic bounds the difference integral. -/
theorem abs_linearStep_sub_le {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (v : Icc (0 : ℝ) u₀) (r : ℝ≥0) (C : ℝ) :
    let χ := characteristic hH v r
    let b := fun s : ℝ =>
      let u := s.toNNReal
      let ρ := (χ s).toNNReal
      (gBarX hH u ρ - gBarX hK u ρ) / 2 * derivLinearStep hK data hdata u ρ +
        (linearCoeff hH u ρ - linearCoeff hK u ρ) * linearStep hK data u ρ +
        linearSource hH u ρ - linearSource hK u ρ
    (∀ s ∈ Icc 0 (v : ℝ), |b s| ≤ C / (1 + (r : ℝ)) ^ 3) →
      |linearStep hH data (v : ℝ).toNNReal r - linearStep hK data (v : ℝ).toNNReal r| ≤
        (v : ℝ) * exp (π * x ^ 2 / 12 * (u₀ : ℝ)) * C / (1 + (r : ℝ)) ^ 3 := by
  intro χ b hb
  have he : ∀ s ∈ Icc 0 (v : ℝ),
      exp (∫ t in s..(v : ℝ), linearCoeff hH t.toNNReal (χ t).toNNReal) ≤
        exp (π * x ^ 2 / 12 * (u₀ : ℝ)) := by
    intro s hs
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
      _ ≤ |∫ t in s..(v : ℝ), linearCoeff hH t.toNNReal (χ t).toNNReal| :=
        le_abs_self _
      _ ≤ (π * x ^ 2 / 12) * ((v : ℝ) - s) := hi
      _ ≤ (π * x ^ 2 / 12) * (u₀ : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [v.2.2, hs.1]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (v : ℝ))
    (f := fun s =>
      exp (∫ t in s..(v : ℝ), linearCoeff hH t.toNNReal (χ t).toNNReal) * b s)
    (C := exp (π * x ^ 2 / 12 * (u₀ : ℝ)) * (C / (1 + (r : ℝ)) ^ 3)) (fun s hs => by
      rw [uIoc_of_le v.2.1] at hs
      have hs' : s ∈ Icc 0 (v : ℝ) := ⟨hs.1.le, hs.2⟩
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
      exact mul_le_mul (he s hs') (hb s hs') (abs_nonneg _) (exp_pos _).le)
  rw [linearStep_difference_integral hH hK data hdata v r]
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg v.2.1] at hi
  convert hi using 1
  ring

end XDiff
end Christodoulou.Bondi
