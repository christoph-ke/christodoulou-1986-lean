module
public import Christodoulou.Frozen.Bondi.DerivLinearStep
import Christodoulou.Frozen.Bondi.LinearStepZero
import Christodoulou.Frozen.Bondi.IsCharacteristicHasDerivWithinAtLinearStep
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic
import Christodoulou.Frozen.Bondi.IsCharacteristicMemIcc
import Christodoulou.Frozen.Bondi.ContinuousCharacteristic
import Christodoulou.Frozen.Bondi.HasDerivWithinAtCharacteristic
import Christodoulou.Frozen.Bondi.ContinuousExpIntegralLinearCoeff
import Christodoulou.Frozen.Bondi.ContinuousDerivGBarX
import Christodoulou.Frozen.Bondi.AbsDeriv2GBarXLe
import Christodoulou.Frozen.Bondi.AbsDerivLinearSourceLe
import Christodoulou.Bondi.LinearODE
import Christodoulou.Bondi.LinearStepBasic
import Christodoulou.Bondi.CoefficientRegularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Deriv



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi
open Filter Topology

namespace Auxiliary

private lemma terminal_primitive_deriv {T : ℝ} {a : ℝ → ℝ}
    (ha : ContinuousOn a (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => ∫ τ in s..T, a τ) (-a t) (Icc 0 T) t := by
  have hd := (LinODE.primitive_deriv ha ht).const_sub (∫ τ in (0 : ℝ)..T, a τ)
  have heq (s : ℝ) (hs : s ∈ Icc 0 T) :
      (∫ τ in (0 : ℝ)..T, a τ) - (∫ τ in (0 : ℝ)..s, a τ) = ∫ τ in s..T, a τ := by
    have hi := ha.intervalIntegrable_of_Icc (μ := volume) (le_trans hs.1 hs.2)
    have his := (ha.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc (μ := volume) hs.1
    have hh := intervalIntegral.integral_add_adjacent_intervals his (his.symm.trans hi)
    linarith only [hh]
  exact hd.congr (fun s hs => (heq s hs).symm) (heq t ht).symm

private lemma jky_identity {T : ℝ} (hT : 0 ≤ T) {a b f Y : ℝ → ℝ}
    (ha : ContinuousOn a (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T))
    (hf : ContinuousOn f (Icc 0 T))
    (hY : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (a t * Y t + f t) (Icc 0 T) t) :
    let J := fun s => exp (∫ τ in s..T, a τ)
    let K := fun s => ∫ τ in s..T, b τ * J τ
    (∫ s in (0 : ℝ)..T, J s ^ 2 * b s * Y s) =
      J 0 * K 0 * Y 0 + ∫ s in (0 : ℝ)..T, J s * K s * f s := by
  dsimp only
  let J := fun s => exp (∫ τ in s..T, a τ)
  let K := fun s => ∫ τ in s..T, b τ * J τ
  have hJ (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt J (-a t * J t) (Icc 0 T) t := by
    convert (terminal_primitive_deriv ha ht).exp using 1
    simp only [J]
    ring
  have hJc := HasDerivWithinAt.continuousOn hJ
  have hK (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt K (-b t * J t) (Icc 0 T) t := by
    convert terminal_primitive_deriv (hb.mul hJc) ht using 1
    simp only [Pi.mul_apply]
    ring
  have hKc := HasDerivWithinAt.continuousOn hK
  have hYc := HasDerivWithinAt.continuousOn hY
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun s => J s * K s * Y s)
        (J t * K t * f t - J t ^ 2 * b t * Y t) (Icc 0 T) t := by
    convert ((hJ t ht).mul (hK t ht)).mul (hY t ht) using 1
    simp only [Pi.mul_apply]
    ring
  have hc : ContinuousOn (fun s => J s * K s * f s - J s ^ 2 * b s * Y s) (Icc 0 T) :=
    ((hJc.mul hKc).mul hf).sub (((hJc.pow 2).mul hb).mul hYc)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    ((hJc.mul hKc).mul hYc)
    (fun s hs => (hd s ⟨hs.1.le, hs.2.le⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2))
    (hc.intervalIntegrable_of_Icc hT)
  simp only [Pi.mul_apply] at hi
  have hI1 : IntervalIntegrable (fun s => J s * K s * f s) volume 0 T := by
    simpa only [Pi.mul_def] using
      (((hJc.mul hKc).mul hf).intervalIntegrable_of_Icc (μ := volume) hT)
  have hI2 : IntervalIntegrable (fun s => J s ^ 2 * b s * Y s) volume 0 T := by
    simpa only [Pi.mul_def, Pi.pow_def] using
      ((((hJc.pow 2).mul hb).mul hYc).intervalIntegrable_of_Icc (μ := volume) hT)
  rw [intervalIntegral.integral_sub hI1 hI2] at hi
  have hKT : K T = 0 := intervalIntegral.integral_same
  rw [hKT, mul_zero, zero_mul, zero_sub] at hi
  change (∫ s in (0 : ℝ)..T, J s ^ 2 * b s * Y s) = _
  linarith only [hi]

end Auxiliary


theorem XReg.derivLinearStep_eq_R14 {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0))
    (u r : ℝ≥0) :
    let v : Icc (0 : ℝ) u₀ :=
      ⟨min u u₀, (min u u₀).coe_nonneg, by exact_mod_cast min_le_right u u₀⟩
    let χ := characteristic hH v r
    let J := fun s : ℝ => exp
      (∫ τ in s..(v : ℝ), linearCoeff hH (Real.toNNReal τ) (Real.toNNReal (χ τ)))
    let K := fun s : ℝ => ∫ τ in s..(v : ℝ),
      (1 / 2 * deriv2GBarX hH (Real.toNNReal τ) (Real.toNNReal (χ τ))) * J τ
    derivLinearStep hH data hdata u r =
      derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) (χ 0) * (J 0) ^ 2 +
      data (Real.toNNReal (χ 0)) * J 0 * K 0 +
      ∫ s in (0 : ℝ)..(v : ℝ),
        (J s) ^ 2 *
          (-(1 / 2 * deriv2GBarX hH (Real.toNNReal s) (Real.toNNReal (χ s))) *
              hBarX u₀ H (Real.toNNReal s) (Real.toNNReal (χ s)) -
            linearCoeff hH (Real.toNNReal s) (Real.toNNReal (χ s)) *
              derivHBarX hH (Real.toNNReal s) (Real.toNNReal (χ s))) +
        J s * linearSource hH (Real.toNNReal s) (Real.toNNReal (χ s)) * K s := by
  let v : Icc (0 : ℝ) u₀ :=
    ⟨min u u₀, (min u u₀).coe_nonneg, by exact_mod_cast min_le_right u u₀⟩
  let χ := characteristic hH v r
  let a := fun s : ℝ => linearCoeff hH s.toNNReal (χ s).toNNReal
  let b := fun s : ℝ => 1 / 2 * deriv2GBarX hH s.toNNReal (χ s).toNNReal
  let f := fun s : ℝ => linearSource hH s.toNNReal (χ s).toNNReal
  let fp := fun s : ℝ => -b s * hBarX u₀ H s.toNNReal (χ s).toNNReal -
    a s * derivHBarX hH s.toNNReal (χ s).toNNReal
  let Y := fun s : ℝ => linearStep hH data s.toNNReal (χ s).toNNReal
  let J := fun s : ℝ => exp (∫ τ in s..(v : ℝ), a τ)
  let K := fun s : ℝ => ∫ τ in s..(v : ℝ), b τ * J τ
  let dp := derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (χ 0)
  have hχ := isCharacteristic_characteristic hH v r
  have hp : ContinuousOn (fun s : ℝ => (s.toNNReal, (χ s).toNNReal)) (Icc 0 (v : ℝ)) :=
    continuous_real_toNNReal.continuousOn.prodMk
      (continuous_real_toNNReal.comp_continuousOn (HasDerivWithinAt.continuousOn hχ.2))
  have ha : ContinuousOn a (Icc 0 (v : ℝ)) := XStep.continuousOn_linearCoeff hχ
  have hb : ContinuousOn b (Icc 0 (v : ℝ)) :=
    (XCoef.continuous_deriv_linearCoeff hH).comp_continuousOn hp
  have hf : ContinuousOn f (Icc 0 (v : ℝ)) := XStep.continuousOn_linearSource hχ
  have hfp : ContinuousOn fp (Icc 0 (v : ℝ)) :=
    (XCoef.continuous_deriv_linearSource hH).comp_continuousOn hp
  have hY (t : ℝ) (ht : t ∈ Icc 0 (v : ℝ)) :
      HasDerivWithinAt Y (a t * Y t + f t) (Icc 0 (v : ℝ)) t :=
    hχ.hasDerivWithinAt_linearStep data ht
  have hYc := HasDerivWithinAt.continuousOn hY
  have hJc : ContinuousOn J (Icc 0 (v : ℝ)) :=
    Real.continuous_exp.comp_continuousOn
      (HasDerivWithinAt.continuousOn (fun t ht => Auxiliary.terminal_primitive_deriv ha ht))
  have hKc : ContinuousOn K (Icc 0 (v : ℝ)) :=
    HasDerivWithinAt.continuousOn
      (fun t ht => Auxiliary.terminal_primitive_deriv (hb.mul hJc) ht)
  have hi := Auxiliary.jky_identity v.2.1 ha hb hf hY
  change (∫ s in (0 : ℝ)..(v : ℝ), J s ^ 2 * b s * Y s) =
    J 0 * K 0 * Y 0 + ∫ s in (0 : ℝ)..(v : ℝ), J s * K s * f s at hi
  have hY0 : Y 0 = data (χ 0).toNNReal := by
    simpa only [Y, Real.toNNReal_zero] using linearStep_zero hH data (χ 0).toNNReal
  have hexp (s : ℝ) : exp (2 * ∫ τ in s..(v : ℝ), a τ) = J s ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  change derivLinearStep hH data hdata u r =
    dp * J 0 ^ 2 + data (χ 0).toNNReal * J 0 * K 0 +
      ∫ s in (0 : ℝ)..(v : ℝ), J s ^ 2 * fp s + J s * f s * K s
  have hQ : derivLinearStep hH data hdata u r = dp * J 0 ^ 2 +
      ∫ s in (0 : ℝ)..(v : ℝ), (J s ^ 2 * b s * Y s + J s ^ 2 * fp s) := by
    unfold derivLinearStep
    change dp * exp (2 * ∫ τ in (0 : ℝ)..(v : ℝ), a τ) +
      (∫ s in (0 : ℝ)..(v : ℝ), exp (2 * ∫ τ in s..(v : ℝ), a τ) *
        (b s * Y s + fp s)) = _
    rw [hexp 0]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [hexp s]
    ring
  have hI1 : IntervalIntegrable (fun s => J s ^ 2 * b s * Y s) volume 0 v := by
    simpa only [Pi.mul_def, Pi.pow_def] using
      ((((hJc.pow 2).mul hb).mul hYc).intervalIntegrable_of_Icc (μ := volume) v.2.1)
  have hI2 : IntervalIntegrable (fun s => J s ^ 2 * fp s) volume 0 v := by
    simpa only [Pi.mul_def, Pi.pow_def] using
      (((hJc.pow 2).mul hfp).intervalIntegrable_of_Icc (μ := volume) v.2.1)
  have hI3 : IntervalIntegrable (fun s => J s * K s * f s) volume 0 v := by
    simpa only [Pi.mul_def] using
      (((hJc.mul hKc).mul hf).intervalIntegrable_of_Icc (μ := volume) v.2.1)
  rw [hQ, intervalIntegral.integral_add hI1 hI2, hi, hY0]
  have hsum : (∫ s in (0 : ℝ)..(v : ℝ), J s ^ 2 * fp s + J s * f s * K s) =
      (∫ s in (0 : ℝ)..(v : ℝ), J s ^ 2 * fp s) +
      ∫ s in (0 : ℝ)..(v : ℝ), J s * K s * f s := by
    calc
      _ = ∫ s in (0 : ℝ)..(v : ℝ), J s ^ 2 * fp s + J s * K s * f s := by
        apply intervalIntegral.integral_congr
        intro s hs
        ring
      _ = _ := intervalIntegral.integral_add hI2 hI3
  rw [hsum]
  ring

namespace Auxiliary
variable {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}

private noncomputable def chi (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    (ρ t : ℝ) : ℝ := characteristic hH v ρ.toNNReal t
private noncomputable def a (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    (ρ t : ℝ) : ℝ := linearCoeff hH t.toNNReal (chi hH v ρ t).toNNReal
private noncomputable def b (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    (ρ t : ℝ) : ℝ := 1 / 2 * deriv2GBarX hH t.toNNReal (chi hH v ρ t).toNNReal
private noncomputable def f (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    (ρ t : ℝ) : ℝ := linearSource hH t.toNNReal (chi hH v ρ t).toNNReal
private noncomputable def fp (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    (ρ t : ℝ) : ℝ := -(b hH v ρ t) * hBarX u₀ H t.toNNReal (chi hH v ρ t).toNNReal -
    a hH v ρ t * derivHBarX hH t.toNNReal (chi hH v ρ t).toNNReal
private noncomputable def J (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    (ρ t : ℝ) : ℝ := exp (∫ τ in t..(v : ℝ), a hH v ρ τ)
private noncomputable def K (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    (ρ t : ℝ) : ℝ := ∫ τ in t..(v : ℝ), b hH v ρ τ * J hH v ρ τ

private lemma continuous_chi (hH : MemXBall u₀ x H) :
    Continuous (fun p : (Icc (0 : ℝ) u₀ × ℝ) × ℝ => chi hH p.1.1 p.1.2 p.2) := by
  exact (continuous_characteristic hH).comp
    (continuous_snd.prodMk
      ((continuous_fst.comp continuous_fst).prodMk
        (continuous_real_toNNReal.comp (continuous_snd.comp continuous_fst))))

private lemma continuous_coord (hH : MemXBall u₀ x H) :
    Continuous (fun p : (Icc (0 : ℝ) u₀ × ℝ) × ℝ =>
      (p.2.toNNReal, (chi hH p.1.1 p.1.2 p.2).toNNReal)) :=
  (continuous_real_toNNReal.comp continuous_snd).prodMk
    (continuous_real_toNNReal.comp (continuous_chi hH))

private lemma continuous_a (hH : MemXBall u₀ x H) :
    Continuous (fun p : (Icc (0 : ℝ) u₀ × ℝ) × ℝ => a hH p.1.1 p.1.2 p.2) :=
  continuous_const.mul ((continuous_derivGBarX hH).comp (continuous_coord hH))
private lemma continuous_b (hH : MemXBall u₀ x H) :
    Continuous (fun p : (Icc (0 : ℝ) u₀ × ℝ) × ℝ => b hH p.1.1 p.1.2 p.2) :=
  (XCoef.continuous_deriv_linearCoeff hH).comp (continuous_coord hH)
private lemma continuous_f (hH : MemXBall u₀ x H) :
    Continuous (fun p : (Icc (0 : ℝ) u₀ × ℝ) × ℝ => f hH p.1.1 p.1.2 p.2) :=
  ((continuous_a hH).neg).mul ((XStep.continuous_hBarX u₀ H).comp (continuous_coord hH))
private lemma continuous_fp (hH : MemXBall u₀ x H) :
    Continuous (fun p : (Icc (0 : ℝ) u₀ × ℝ) × ℝ => fp hH p.1.1 p.1.2 p.2) :=
  (XCoef.continuous_deriv_linearSource hH).comp (continuous_coord hH)
private lemma continuous_J (hH : MemXBall u₀ x H) :
    Continuous (fun p : (Icc (0 : ℝ) u₀ × ℝ) × ℝ => J hH p.1.1 p.1.2 p.2) := by
  exact (continuous_exp_integral_linearCoeff hH).comp
    (continuous_snd.prodMk
      ((continuous_fst.comp continuous_fst).prodMk
        (continuous_real_toNNReal.comp (continuous_snd.comp continuous_fst))))

private lemma continuous_integral_endpoints {X : Type*} [TopologicalSpace X]
    {F : X → ℝ → ℝ} (hF : Continuous F.uncurry) {l r : X → ℝ}
    (hl : Continuous l) (hr : Continuous r) :
    Continuous (fun p => ∫ t in l p..r p, F p t) := by
  have h1 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := (0 : ℝ)) hF hr
  have h2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := (0 : ℝ)) hF hl
  have heq : (fun p => ∫ t in l p..r p, F p t) =
      fun p => (∫ t in (0 : ℝ)..r p, F p t) - ∫ t in (0 : ℝ)..l p, F p t := by
    funext p
    have hc : Continuous (F p) := hF.comp (Continuous.prodMk_right p)
    rw [intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable 0 (r p)) (hc.intervalIntegrable 0 (l p))]
  rw [heq]
  exact h1.sub h2

private lemma continuous_K (hH : MemXBall u₀ x H) :
    Continuous (fun p : (Icc (0 : ℝ) u₀ × ℝ) × ℝ => K hH p.1.1 p.1.2 p.2) := by
  unfold K
  apply continuous_integral_endpoints
    (X := (Icc (0 : ℝ) u₀ × ℝ) × ℝ)
    (F := fun p τ => b hH p.1.1 p.1.2 τ * J hH p.1.1 p.1.2 τ)
    (l := fun p => p.2) (r := fun p => (p.1.1 : ℝ))
  · exact ((continuous_b hH).comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).mul
      ((continuous_J hH).comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
  · exact continuous_snd
  · exact continuous_subtype_val.comp (continuous_fst.comp continuous_fst)

private lemma chi_nonneg (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀) (ρ : ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 (v : ℝ)) : 0 ≤ chi hH v ρ t :=
  ρ.toNNReal.coe_nonneg.trans ((isCharacteristic_characteristic hH v ρ.toNNReal).mem_Icc ht).1

private lemma hasDerivAt_chi (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : t ∈ Icc 0 (v : ℝ)) :
    HasDerivAt (fun z => chi hH v z t) (J hH v ρ t) ρ := by
  have hd := hasDerivWithinAt_characteristic hH v ρ.toNNReal ht
  rw [Real.coe_toNNReal _ hρ.le] at hd
  exact hd.hasDerivAt (Ici_mem_nhds hρ)

private lemma hasDerivAt_a (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : t ∈ Icc 0 (v : ℝ)) :
    HasDerivAt (fun z => a hH v z t) (b hH v ρ t * J hH v ρ t) ρ := by
  have hd := XCoef.hasDerivWithinAt_linearCoeff_comp hH t.toNNReal
    (hasDerivAt_chi hH v hρ ht).hasDerivWithinAt
    (s := Ici 0) (fun z hz => chi_nonneg hH v z ht) (chi_nonneg hH v ρ ht)
  exact hd.hasDerivAt (Ici_mem_nhds hρ)

private lemma hasDerivAt_f (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : t ∈ Icc 0 (v : ℝ)) :
    HasDerivAt (fun z => f hH v z t) (fp hH v ρ t * J hH v ρ t) ρ := by
  have hd := XCoef.hasDerivWithinAt_linearSource_comp hH t.toNNReal
    (hasDerivAt_chi hH v hρ ht).hasDerivWithinAt
    (s := Ici 0) (fun z hz => chi_nonneg hH v z ht) (chi_nonneg hH v ρ ht)
  exact hd.hasDerivAt (Ici_mem_nhds hρ)

end Auxiliary

namespace Auxiliary
variable {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}

private lemma x_nonneg (hH : MemXBall u₀ x H) : 0 ≤ x :=
  le_trans (by positivity) (hH.2.2 0 (by positivity) 0)

private lemma abs_b_le (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀) (ρ t : ℝ) :
    |b hH v ρ t| ≤ π * x ^ 2 / 2 := by
  let r := (chi hH v ρ t).toNNReal
  have hb := abs_deriv2GBarX_le hH t.toNNReal r
  have hr : 1 ≤ (1 + (r : ℝ)) ^ 3 := one_le_pow₀ (by linarith [r.coe_nonneg])
  have hdiv : π * x ^ 2 / (1 + (r : ℝ)) ^ 3 ≤ π * x ^ 2 := by
    exact (div_le_iff₀ (by positivity)).mpr (le_mul_of_one_le_right (by positivity) hr)
  simp only [b, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hh := mul_le_mul_of_nonneg_left (hb.trans hdiv) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  convert hh using 1
  ring

private lemma abs_f_le (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀) (ρ t : ℝ) :
    |f hH v ρ t| ≤ π * x ^ 3 / 6 := by
  let r := (chi hH v ρ t).toNNReal
  have hx := x_nonneg hH
  have hb := XCoef.abs_linearSource_le hH t.toNNReal r
  have hr : 1 ≤ (1 + (r : ℝ)) ^ 3 := one_le_pow₀ (by linarith [r.coe_nonneg])
  apply hb.trans
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := le_mul_of_one_le_right (show 0 ≤ π * x ^ 3 / 6 by positivity) hr
  nlinarith only [hh]

private lemma abs_fp_le (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀) (ρ t : ℝ) :
    |fp hH v ρ t| ≤ 7 * π * x ^ 3 / 12 := by
  let r := (chi hH v ρ t).toNNReal
  have hx := x_nonneg hH
  have hb := abs_deriv_linearSource_le hH t.toNNReal r
  have hr : 1 ≤ (1 + (r : ℝ)) ^ 4 := one_le_pow₀ (by linarith [r.coe_nonneg])
  apply hb.trans
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := le_mul_of_one_le_right (show 0 ≤ 7 * π * x ^ 3 / 12 by positivity) hr
  nlinarith only [hh]

private lemma J_le (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀) (ρ : ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 (v : ℝ)) :
    J hH v ρ t ≤ exp (π / 12 * x ^ 2 * (u₀ : ℝ)) := by
  have hc : Continuous (a hH v ρ) :=
    (continuous_a hH).comp ((continuous_const.prodMk continuous_const).prodMk continuous_id)
  have hi := intervalIntegral.integral_mono_on (μ := volume) ht.2 (hc.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable t (v : ℝ))
    (fun s hs => XCoef.linearCoeff_le_uniform hH s.toNNReal (chi hH v ρ s).toNNReal)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ((v : ℝ) - t) * (π / 12 * x ^ 2) := hi
    _ ≤ (u₀ : ℝ) * (π / 12 * x ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith [ht.1, v.2.2]) (by positivity)
    _ = _ := by ring

private lemma abs_J_le (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀) (ρ : ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 (v : ℝ)) :
    |J hH v ρ t| ≤ exp (π / 12 * x ^ 2 * (u₀ : ℝ)) := by
  rw [abs_of_pos (show 0 < J hH v ρ t from Real.exp_pos _)]
  exact J_le hH v ρ ht

private lemma abs_K_le (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀) (ρ : ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 (v : ℝ)) :
    |K hH v ρ t| ≤ (u₀ : ℝ) * (π * x ^ 2 / 2) * exp (π / 12 * x ^ 2 * (u₀ : ℝ)) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := (v : ℝ)) (f := fun s => b hH v ρ s * J hH v ρ s)
    (C := (π * x ^ 2 / 2) * exp (π / 12 * x ^ 2 * (u₀ : ℝ))) (fun s hs => by
      rw [uIoc_of_le ht.2] at hs
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_b_le hH v ρ s)
        (abs_J_le hH v ρ ⟨ht.1.trans hs.1.le, hs.2⟩) (abs_nonneg _) (by positivity))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)] at hi
  change |K hH v ρ t| ≤ _ at hi
  calc
    _ ≤ _ := hi
    _ ≤ ((π * x ^ 2 / 2) * exp (π / 12 * x ^ 2 * (u₀ : ℝ))) * (u₀ : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith [ht.1, v.2.2]) (by positivity)
    _ = _ := by ring

end Auxiliary

namespace Auxiliary

private lemma positive_parametric_integral {F Fp : ℝ → ℝ → ℝ} {C ρ l r : ℝ}
    (hρ : 0 < ρ) (hlr : l ≤ r) (hF : Continuous F.uncurry)
    (hFp : Continuous Fp.uncurry)
    (hbound : ∀ z, 0 < z → ∀ t ∈ Icc l r, |Fp z t| ≤ C)
    (hdiff : ∀ z, 0 < z → ∀ t ∈ Icc l r,
      HasDerivAt (fun w => F w t) (Fp z t) z) :
    HasDerivAt (fun z => ∫ t in l..r, F z t) (∫ t in l..r, Fp ρ t) ρ := by
  have hFc (z : ℝ) : Continuous (F z) := hF.comp (Continuous.prodMk_right z)
  have hFpc (z : ℝ) : Continuous (Fp z) := hFp.comp (Continuous.prodMk_right z)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Ioi 0) (bound := fun _ => C)
    (Ioi_mem_nhds hρ)
    (Eventually.of_forall (fun z => (hFc z).aestronglyMeasurable))
    ((hFc ρ).intervalIntegrable l r)
    ((hFpc ρ).aestronglyMeasurable)
    (Eventually.of_forall (fun t ht z hz => by
      rw [uIoc_of_le hlr] at ht
      rw [Real.norm_eq_abs]
      exact hbound z hz t ⟨ht.1.le, ht.2⟩))
    (continuous_const.intervalIntegrable l r)
    (Eventually.of_forall (fun t ht z hz => by
      rw [uIoc_of_le hlr] at ht
      exact hdiff z hz t ⟨ht.1.le, ht.2⟩))).2

variable {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}

private lemma hasDerivAt_A (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : t ∈ Icc 0 (v : ℝ)) :
    HasDerivAt (fun z => ∫ τ in t..(v : ℝ), a hH v z τ) (K hH v ρ t) ρ := by
  apply positive_parametric_integral (C := π * x ^ 2 / 2 * exp (π / 12 * x ^ 2 * (u₀ : ℝ)))
    hρ ht.2
  · exact (continuous_a hH).comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  · exact ((continuous_b hH).comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).mul
      ((continuous_J hH).comp
        ((continuous_const.prodMk continuous_fst).prodMk continuous_snd))
  · intro z hz s hs
    rw [abs_mul]
    exact mul_le_mul (abs_b_le hH v z s)
      (abs_J_le hH v z ⟨ht.1.trans hs.1, hs.2⟩) (abs_nonneg _) (by positivity)
  · intro z hz s hs
    exact hasDerivAt_a hH v hz ⟨ht.1.trans hs.1, hs.2⟩

private lemma hasDerivAt_J (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : t ∈ Icc 0 (v : ℝ)) :
    HasDerivAt (fun z => J hH v z t) (J hH v ρ t * K hH v ρ t) ρ :=
  (hasDerivAt_A hH v hρ ht).exp

private lemma abs_outer_derivative_le (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    (ρ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 (v : ℝ)) :
    |J hH v ρ t * K hH v ρ t * f hH v ρ t + J hH v ρ t ^ 2 * fp hH v ρ t| ≤
      exp (π / 12 * x ^ 2 * (u₀ : ℝ)) *
        ((u₀ : ℝ) * (π * x ^ 2 / 2) * exp (π / 12 * x ^ 2 * (u₀ : ℝ))) * (π * x ^ 3 / 6) +
      exp (π / 12 * x ^ 2 * (u₀ : ℝ)) ^ 2 * (7 * π * x ^ 3 / 12) := by
  have hx := x_nonneg hH
  calc
    _ ≤ |J hH v ρ t * K hH v ρ t * f hH v ρ t| + |J hH v ρ t ^ 2 * fp hH v ρ t| :=
      abs_add_le _ _
    _ ≤ _ := by
      simp only [abs_mul, abs_pow]
      gcongr
      · exact abs_J_le hH v ρ ht
      · exact abs_K_le hH v ρ ht
      · exact abs_f_le hH v ρ t
      · exact abs_J_le hH v ρ ht
      · exact abs_fp_le hH v ρ t

private lemma continuous_outer_derivative (hH : MemXBall u₀ x H)
    (v : Icc (0 : ℝ) u₀) :
    Continuous (fun p : ℝ × ℝ =>
      J hH v p.1 p.2 * K hH v p.1 p.2 * f hH v p.1 p.2 +
        J hH v p.1 p.2 ^ 2 * fp hH v p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × ℝ => ((v, p.1), p.2)) :=
    (continuous_const.prodMk continuous_fst).prodMk continuous_snd
  have hJ : Continuous (fun p : ℝ × ℝ => J hH v p.1 p.2) :=
    by simpa only [Function.comp_def] using (continuous_J hH).comp hc
  have hK : Continuous (fun p : ℝ × ℝ => K hH v p.1 p.2) :=
    by simpa only [Function.comp_def] using (continuous_K hH).comp hc
  have hf : Continuous (fun p : ℝ × ℝ => f hH v p.1 p.2) :=
    by simpa only [Function.comp_def] using (continuous_f hH).comp hc
  have hfp : Continuous (fun p : ℝ × ℝ => fp hH v p.1 p.2) :=
    by simpa only [Function.comp_def] using (continuous_fp hH).comp hc
  exact ((hJ.mul hK).mul hf).add ((hJ.pow 2).mul hfp)

private lemma hasDerivAt_outer_integral (hH : MemXBall u₀ x H) (v : Icc (0 : ℝ) u₀)
    {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun z => ∫ t in (0 : ℝ)..(v : ℝ), J hH v z t * f hH v z t)
      (∫ t in (0 : ℝ)..(v : ℝ),
        J hH v ρ t * K hH v ρ t * f hH v ρ t + J hH v ρ t ^ 2 * fp hH v ρ t) ρ := by
  apply positive_parametric_integral
    (F := fun z t => J hH v z t * f hH v z t)
    (Fp := fun z t => J hH v z t * K hH v z t * f hH v z t + J hH v z t ^ 2 * fp hH v z t)
    hρ v.2.1
  · exact ((continuous_J hH).comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).mul
      ((continuous_f hH).comp
        ((continuous_const.prodMk continuous_fst).prodMk continuous_snd))
  · exact continuous_outer_derivative hH v
  · intro z hz t ht
    exact abs_outer_derivative_le hH v z ht
  · intro z hz t ht
    convert (hasDerivAt_J hH v hz ht).mul (hasDerivAt_f hH v hz ht) using 1
    ring

end Auxiliary

open Auxiliary in
private lemma Auxiliary.hasDerivAt_linearStep_pos {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0))
    (u r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => linearStep hH data u (Real.toNNReal s))
      (derivLinearStep hH data hdata u r) (r : ℝ) := by
  let v : Icc (0 : ℝ) u₀ :=
    ⟨min u u₀, (min u u₀).coe_nonneg, by exact_mod_cast min_le_right u u₀⟩
  have hrp : 0 < (r : ℝ) := NNReal.coe_pos.mpr hr
  have ht0 : (0 : ℝ) ∈ Icc 0 (v : ℝ) := ⟨le_rfl, v.2.1⟩
  let dp := derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (chi hH v r 0)
  have hdData : HasDerivAt (fun z => data (chi hH v z 0).toNNReal)
      (dp * J hH v r 0) (r : ℝ) := by
    have hh := (hdata.differentiableOn (by norm_num) _ (chi_nonneg hH v r ht0)).hasDerivWithinAt
    have hd := hh.comp (r : ℝ)
      (hasDerivAt_chi hH v hrp ht0).hasDerivWithinAt
      (s := Ici 0) (fun z hz => chi_nonneg hH v z ht0)
    exact hd.hasDerivAt (Ici_mem_nhds hrp)
  have hdInitial := hdData.mul (hasDerivAt_J hH v hrp ht0)
  have hdOuter := hasDerivAt_outer_integral hH v hrp
  have hR14 : derivLinearStep hH data hdata u r =
    dp * J hH v r 0 ^ 2 + data (chi hH v r 0).toNNReal * J hH v r 0 * K hH v r 0 +
      ∫ s in (0 : ℝ)..(v : ℝ),
        J hH v r s ^ 2 * fp hH v r s + J hH v r s * f hH v r s * K hH v r s := by
    simpa only [v, dp, chi, J, K, a, b, f, fp, Real.toNNReal_coe] using
      XReg.derivLinearStep_eq_R14 hH data hdata u r
  have hInt : (∫ s in (0 : ℝ)..(v : ℝ),
      J hH v r s * K hH v r s * f hH v r s + J hH v r s ^ 2 * fp hH v r s) =
      ∫ s in (0 : ℝ)..(v : ℝ),
        J hH v r s ^ 2 * fp hH v r s + J hH v r s * f hH v r s * K hH v r s := by
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    ring
  have hd := hdInitial.add hdOuter
  convert hd using 1
  · ext z
    simp only [Pi.add_apply, Pi.mul_apply, linearStep, v, chi, J, a, f]
  · rw [hR14, hInt]
    ring

open Auxiliary in
/-- The linear step is jointly continuous for continuous initial data. -/
theorem XReg.continuous_linearStep {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ)) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => linearStep hH data p.1 p.2) := by
  let v : ℝ≥0 × ℝ≥0 → Icc (0 : ℝ) u₀ := fun p =>
    ⟨min p.1 u₀, (min p.1 u₀).coe_nonneg, by exact_mod_cast min_le_right p.1 u₀⟩
  have hv : Continuous v := by
    exact (NNReal.continuous_coe.comp (continuous_fst.min continuous_const)).subtype_mk _
  have hz : Continuous (fun p : ℝ≥0 × ℝ≥0 => (v p, (p.2 : ℝ))) :=
    hv.prodMk (NNReal.continuous_coe.comp continuous_snd)
  have hparam : Continuous (fun q : (ℝ≥0 × ℝ≥0) × ℝ => ((v q.1, (q.1.2 : ℝ)), q.2)) :=
    (hz.comp continuous_fst).prodMk continuous_snd
  have hχ0 : Continuous (fun p : ℝ≥0 × ℝ≥0 => chi hH (v p) p.2 0) :=
    (continuous_chi hH).comp (hz.prodMk continuous_const)
  have hJ0 : Continuous (fun p : ℝ≥0 × ℝ≥0 => J hH (v p) p.2 0) :=
    (continuous_J hH).comp (hz.prodMk continuous_const)
  have hInt : Continuous (fun p : ℝ≥0 × ℝ≥0 =>
      ∫ s in (0 : ℝ)..(v p : ℝ), J hH (v p) p.2 s * f hH (v p) p.2 s) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (((continuous_J hH).comp hparam).mul ((continuous_f hH).comp hparam))
      (continuous_subtype_val.comp hv)
  have heq : (fun p : ℝ≥0 × ℝ≥0 => linearStep hH data p.1 p.2) =
      fun p => data (chi hH (v p) p.2 0).toNNReal * J hH (v p) p.2 0 +
        ∫ s in (0 : ℝ)..(v p : ℝ), J hH (v p) p.2 s * f hH (v p) p.2 s := by
    funext p
    simp only [linearStep, v, chi, J, a, f, Real.toNNReal_coe]
  rw [heq]
  exact ((data.continuous.comp (continuous_real_toNNReal.comp hχ0)).mul hJ0).add hInt

/-- The radial derivative of the linear step is jointly continuous. -/
theorem XReg.continuous_derivLinearStep {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0)) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => derivLinearStep hH data hdata p.1 p.2) := by
  let v : ℝ≥0 × ℝ≥0 → Icc (0 : ℝ) u₀ := fun p =>
    ⟨min p.1 u₀, (min p.1 u₀).coe_nonneg, by exact_mod_cast min_le_right p.1 u₀⟩
  have hv : Continuous v := by
    exact (NNReal.continuous_coe.comp (continuous_fst.min continuous_const)).subtype_mk _
  have hz : Continuous (fun p : ℝ≥0 × ℝ≥0 => (v p, (p.2 : ℝ))) :=
    hv.prodMk (NNReal.continuous_coe.comp continuous_snd)
  have hparam : Continuous (fun q : (ℝ≥0 × ℝ≥0) × ℝ => ((v q.1, (q.1.2 : ℝ)), q.2)) :=
    (hz.comp continuous_fst).prodMk continuous_snd
  have hχ0 : Continuous (fun p : ℝ≥0 × ℝ≥0 => Auxiliary.chi hH (v p) p.2 0) :=
    (Auxiliary.continuous_chi hH).comp (hz.prodMk continuous_const)
  have hJ0 : Continuous (fun p : ℝ≥0 × ℝ≥0 => Auxiliary.J hH (v p) p.2 0) :=
    (Auxiliary.continuous_J hH).comp (hz.prodMk continuous_const)
  have hK0 : Continuous (fun p : ℝ≥0 × ℝ≥0 => Auxiliary.K hH (v p) p.2 0) :=
    (Auxiliary.continuous_K hH).comp (hz.prodMk continuous_const)
  have hd : Continuous (fun p : ℝ≥0 × ℝ≥0 =>
      derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (Auxiliary.chi hH (v p) p.2 0)) := by
    exact (hdata.continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by norm_num)).comp_continuous hχ0
      (fun p => Auxiliary.chi_nonneg hH (v p) p.2 ⟨le_rfl, (v p).2.1⟩)
  have hInt : Continuous (fun p : ℝ≥0 × ℝ≥0 => ∫ s in (0 : ℝ)..(v p : ℝ),
      Auxiliary.J hH (v p) p.2 s ^ 2 * Auxiliary.fp hH (v p) p.2 s +
        Auxiliary.J hH (v p) p.2 s * Auxiliary.f hH (v p) p.2 s * Auxiliary.K hH (v p) p.2 s) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      ((((Auxiliary.continuous_J hH).comp hparam).pow 2).mul
        ((Auxiliary.continuous_fp hH).comp hparam) |>.add
      ((((Auxiliary.continuous_J hH).comp hparam).mul
        ((Auxiliary.continuous_f hH).comp hparam)).mul
          ((Auxiliary.continuous_K hH).comp hparam)))
      (continuous_subtype_val.comp hv)
  have heq : (fun p : ℝ≥0 × ℝ≥0 => derivLinearStep hH data hdata p.1 p.2) = fun p =>
      derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (Auxiliary.chi hH (v p) p.2 0) *
        Auxiliary.J hH (v p) p.2 0 ^ 2 +
      data (Auxiliary.chi hH (v p) p.2 0).toNNReal * Auxiliary.J hH (v p) p.2 0 *
        Auxiliary.K hH (v p) p.2 0 +
      ∫ s in (0 : ℝ)..(v p : ℝ),
        Auxiliary.J hH (v p) p.2 s ^ 2 * Auxiliary.fp hH (v p) p.2 s +
          Auxiliary.J hH (v p) p.2 s * Auxiliary.f hH (v p) p.2 s * Auxiliary.K hH (v p) p.2 s := by
    funext p
    simpa only [v, Auxiliary.chi, Auxiliary.J, Auxiliary.K, Auxiliary.a,
      Auxiliary.b, Auxiliary.f, Auxiliary.fp, Real.toNNReal_coe] using
      XReg.derivLinearStep_eq_R14 hH data hdata p.1 p.2
  rw [heq]
  exact ((hd.mul (hJ0.pow 2)).add
    (((data.continuous.comp (continuous_real_toNNReal.comp hχ0)).mul hJ0).mul hK0)).add hInt


theorem XReg.hasDerivWithinAt_linearStep {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0))
    (u r : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => linearStep hH data u (Real.toNNReal s))
      (derivLinearStep hH data hdata u r) (Ici 0) (r : ℝ) := by
  rcases eq_or_ne r 0 with rfl | hr
  · have hd (s : ℝ) (hs : 0 < s) :
        HasDerivAt (fun t : ℝ => linearStep hH data u t.toNNReal)
          (derivLinearStep hH data hdata u s.toNNReal) s := by
      have hh := Auxiliary.hasDerivAt_linearStep_pos hH data hdata u s.toNNReal
        (Real.toNNReal_pos.mpr hs)
      rwa [Real.coe_toNNReal _ hs.le] at hh
    have hc : Continuous (fun s : ℝ => derivLinearStep hH data hdata u s.toNNReal) :=
      (XReg.continuous_derivLinearStep hH data hdata).comp
        ((continuous_const (y := u)).prodMk continuous_real_toNNReal)
    have ht : Tendsto (fun s : ℝ => derivLinearStep hH data hdata u s.toNNReal)
        (𝓝[>] 0) (𝓝 (derivLinearStep hH data hdata u 0)) := by
      simpa only [Real.toNNReal_zero] using
        (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := Ioi 0) (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    · exact ((XReg.continuous_linearStep hH data).comp
        ((continuous_const (y := u)).prodMk
          continuous_real_toNNReal)).continuousAt.continuousWithinAt
    · exact self_mem_nhdsWithin
    · apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hd s hs).deriv.symm
  · exact (Auxiliary.hasDerivAt_linearStep_pos hH data hdata u r
      (pos_iff_ne_zero.mpr hr)).hasDerivWithinAt

/-- Each radial slice is C¹, with a jointly continuous radial derivative on the strip. -/
theorem XReg.linearStep_radial_regular {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data (Real.toNNReal s)) (Ici 0)) :
    (∀ u : ℝ≥0, ContDiffOn ℝ 1
      (fun s : ℝ => linearStep hH data u (Real.toNNReal s)) (Ici 0)) ∧
    ContinuousOn
      (fun p : ℝ × ℝ => derivWithin
        (fun s : ℝ => linearStep hH data (Real.toNNReal p.1) (Real.toNNReal s))
        (Ici 0) p.2) (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) := by
  have hd (u : ℝ≥0) (s : ℝ) (hs : 0 ≤ s) :
      derivWithin (fun t : ℝ => linearStep hH data u t.toNNReal) (Ici 0) s =
        derivLinearStep hH data hdata u s.toNNReal := by
    have hh := XReg.hasDerivWithinAt_linearStep hH data hdata u s.toNNReal
    rw [Real.coe_toNNReal _ hs] at hh
    exact hh.derivWithin ((uniqueDiffOn_Ici 0).uniqueDiffWithinAt hs)
  have hc := XReg.continuous_derivLinearStep hH data hdata
  constructor
  · intro u
    apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ici 0)).mpr
    constructor
    · intro s hs
      have hh := XReg.hasDerivWithinAt_linearStep hH data hdata u s.toNNReal
      rw [Real.coe_toNNReal _ hs] at hh
      exact hh.differentiableWithinAt
    · apply (hc.comp
        ((continuous_const (y := u)).prodMk continuous_real_toNNReal)).continuousOn.congr
      intro s hs
      exact hd u s hs
  · apply (hc.comp
      ((continuous_real_toNNReal.comp continuous_fst).prodMk
        (continuous_real_toNNReal.comp continuous_snd))).continuousOn.congr
    intro p hp
    exact hd p.1.toNNReal p.2 hp.2

end Christodoulou.Bondi
