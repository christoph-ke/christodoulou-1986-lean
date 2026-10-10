module
public import Christodoulou.Bondi.RadialModulus
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.ConstantDataField
public import Mathlib.Topology.UniformSpace.Equicontinuity
import Christodoulou.Frozen.Bondi.HasDerivWithinAtLinearStep
import Christodoulou.Frozen.Bondi.IsCharacteristicHasDerivWithinAtDerivLinearStep
import Christodoulou.Frozen.Bondi.IsCharacteristicMemIcc
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic
import Christodoulou.Frozen.Bondi.LinearStepZero
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.ODE.Gronwall

/-!
# Characteristic estimates for radial derivative equicontinuity

The initial derivative is uniformly continuous by decay. The differentiated transport
equation is used only along characteristics, so no second derivative of the data is needed.
-/

public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi
namespace XEq
open Filter Topology

/-- A slice derivative is uniformly continuous because it is continuous and decays at infinity. -/
theorem uniformContinuous_slice_deriv {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u : ℝ≥0) (hu : u ≤ u₀) :
    UniformContinuous (fun r : ℝ≥0 =>
      derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r) := by
  let q := fun r : ℝ≥0 => derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r
  have hc : Continuous q :=
    ((hH.1 u hu).continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by norm_num)).comp_continuous
      NNReal.continuous_coe (fun r => r.coe_nonneg)
  have hb (r : ℝ≥0) : |q r| ≤ x / (1 + (r : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hw : 1 + (r : ℝ) ≤ (1 + (r : ℝ)) ^ 4 :=
      le_self_pow₀ (le_add_of_nonneg_right r.coe_nonneg) (by norm_num)
    calc
      _ = (1 + (r : ℝ)) * |q r| := mul_comm _ _
      _ ≤ (1 + (r : ℝ)) ^ 4 * |q r| :=
        mul_le_mul_of_nonneg_right hw (abs_nonneg _)
      _ ≤ x := (le_add_of_nonneg_left (by positivity)).trans (hH.2.2 u hu r)
  have ht : Tendsto (fun r : ℝ≥0 => x / (1 + (r : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_const_nhds.add_atTop (NNReal.tendsto_coe_atTop.mpr tendsto_id))
  have hq : Tendsto q atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero, Real.norm_eq_abs]
    exact squeeze_zero (fun r => abs_nonneg (q r)) hb ht
  exact hc.uniformContinuous_of_tendsto_cocompact (hq.mono_left cocompact_le_atTop)

private theorem step_deriv_eq {u₀ : ℝ≥0} {x : ℝ}
    {H S : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (hS : S = linearStepMap hH data) (u r : ℝ≥0) :
    derivLinearStep hH data hdata u r =
      derivWithin (fun s : ℝ => S (u, s.toNNReal)) (Ici 0) r := by
  rw [hS]
  exact ((hasDerivWithinAt_linearStep hH data hdata u r).derivWithin
    (uniqueDiffOn_Ici 0 _ r.coe_nonneg)).symm

/-- The derivative transport identity, expressed using the actual derivative of the step. -/
theorem hasDerivWithinAt_step_deriv {u₀ : ℝ≥0} {x : ℝ}
    {H S : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H}
    {t : Icc (0 : ℝ) u₀} {r : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH t r χ) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (hS : S = linearStepMap hH data) {s : ℝ} (hs : s ∈ Icc 0 (t : ℝ)) :
    let q := fun u r : ℝ≥0 =>
      derivWithin (fun z : ℝ => S (u, z.toNNReal)) (Ici 0) r
    HasDerivWithinAt (fun v : ℝ => q v.toNNReal (χ v).toNNReal)
      (2 * linearCoeff hH s.toNNReal (χ s).toNNReal * q s.toNNReal (χ s).toNNReal +
        (1 / 2 * deriv2GBarX hH s.toNNReal (χ s).toNNReal) *
          (S (s.toNNReal, (χ s).toNNReal) - hBarX u₀ H s.toNNReal (χ s).toNNReal) -
        linearCoeff hH s.toNNReal (χ s).toNNReal *
          derivHBarX hH s.toNNReal (χ s).toNNReal) (Icc 0 (t : ℝ)) s := by
  dsimp only
  have hd := hχ.hasDerivWithinAt_derivLinearStep data hdata hs
  simp_rw [step_deriv_eq hH data hdata hS] at hd
  have hv : linearStep hH data s.toNNReal (χ s).toNNReal =
      S (s.toNNReal, (χ s).toNNReal) := by rw [hS]; rfl
  rw [hv] at hd
  convert hd using 1
  ring

private lemma abs_hBarX_le_uniform {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (u r : ℝ≥0) :
    |hBarX u₀ H u r| ≤ x :=
  (XCoef.abs_hBarX_le hH u r).trans
    (div_le_self (x_nonneg hH) (le_add_of_nonneg_right r.coe_nonneg))

/-- The right side of the differentiated transport equation has uniform cubic size. -/
theorem abs_deriv_transport_le {u₀ : ℝ≥0} {x : ℝ}
    {H S : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hS : MemXBall u₀ x S)
    (u : ℝ≥0) (hu : u ≤ u₀) (r : ℝ≥0) :
    |2 * linearCoeff hH u r *
        derivWithin (fun z : ℝ => S (u, z.toNNReal)) (Ici 0) r +
      (1 / 2 * deriv2GBarX hH u r) * (S (u, r) - hBarX u₀ H u r) -
      linearCoeff hH u r * derivHBarX hH u r| ≤ 29 * π * x ^ 3 / 24 := by
  have hx := x_nonneg hH
  have hq := (value_deriv_le hS u hu r).2
  have hgap : |S (u, r) - hBarX u₀ H u r| ≤ 2 * x := by
    exact (abs_sub _ _).trans (by linarith [
      (value_deriv_le hS u hu r).1, abs_hBarX_le_uniform hH u r])
  have ha : |linearCoeff hH u r| ≤ π / 12 * x ^ 2 := by
    rw [abs_of_nonneg (XCoef.linearCoeff_nonneg hH u r)]
    exact XCoef.linearCoeff_le_uniform hH u r
  have har := abs_half_deriv2GBarX_le hH u r
  rw [abs_mul] at har
  have hβ := abs_derivHBarX_le_uniform hH u r
  calc
    _ ≤ |2 * linearCoeff hH u r *
          derivWithin (fun z : ℝ => S (u, z.toNNReal)) (Ici 0) r| +
        |(1 / 2 * deriv2GBarX hH u r) * (S (u, r) - hBarX u₀ H u r)| +
        |linearCoeff hH u r * derivHBarX hH u r| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * (π / 12 * x ^ 2) * x + (π * x ^ 2 / 2) * (2 * x) +
        (π / 12 * x ^ 2) * (x / 2) := by
      simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
    _ = _ := by ring

/-- The difference of the transport right sides obeys the centre-safe modulus estimate. -/
theorem abs_deriv_transport_sub_le {u₀ : ℝ≥0} {x : ℝ}
    {H S : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hS : MemXBall u₀ x S)
    (u : ℝ≥0) (hu : u ≤ u₀) {ρ ω : ℝ}
    (hq : ∀ r r' : ℝ≥0, |(r : ℝ) - r'| ≤ ρ →
      |derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r -
        derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r'| ≤ ω)
    (r r' : ℝ≥0) (hr : |(r : ℝ) - r'| ≤ ρ) :
    let q := fun z : ℝ≥0 => derivWithin (fun s : ℝ => S (u, s.toNNReal)) (Ici 0) z
    let F := fun z : ℝ≥0 => 2 * linearCoeff hH u z * q z +
      (1 / 2 * deriv2GBarX hH u z) * (S (u, z) - hBarX u₀ H u z) -
      linearCoeff hH u z * derivHBarX hH u z
    |F r - F r'| ≤ 2 * (π / 12 * x ^ 2) * |q r - q r'| +
      (5 * π ^ 2 * x ^ 5 / 3 + 2 * π * x ^ 3) * ρ +
      (27 * π * x ^ 2 / 8) * ω := by
  dsimp only
  let q := fun z : ℝ≥0 => derivWithin (fun s : ℝ => S (u, s.toNNReal)) (Ici 0) z
  let a := fun z => linearCoeff hH u z
  let b := fun z => 1 / 2 * deriv2GBarX hH u z
  let β := fun z => derivHBarX hH u z
  let V := fun z => S (u, z) - hBarX u₀ H u z
  have hx := x_nonneg hH
  have hρ := (abs_nonneg _).trans hr
  have hω := (abs_nonneg _).trans (hq r r' hr)
  have ha (z) : |a z| ≤ π / 12 * x ^ 2 := by
    rw [abs_of_nonneg (XCoef.linearCoeff_nonneg hH u z)]
    exact XCoef.linearCoeff_le_uniform hH u z
  have har := ha r
  have har' := ha r'
  have haΔ : |a r - a r'| ≤ π * x ^ 2 / 2 * ρ :=
    (abs_linearCoeff_sub_le hH u r r').trans
      (mul_le_mul_of_nonneg_left hr (by positivity))
  have hb := abs_half_deriv2GBarX_le hH u r'
  have hbΔ := abs_half_deriv2GBarX_sub_le hH u hu hq r r' hr
  have hβ := abs_derivHBarX_le_uniform hH u r
  have hβΔ := abs_derivHBarX_sub_le hH u hu hq r r' hr
  have hqr := (value_deriv_le hS u hu r').2
  have hV : |V r| ≤ 2 * x :=
    (abs_sub _ _).trans (by linarith [
      (value_deriv_le hS u hu r).1, abs_hBarX_le_uniform hH u r])
  have hVΔ : |V r - V r'| ≤ (3 * x / 2) * ρ := by
    calc
      _ = |(S (u, r) - S (u, r')) - (hBarX u₀ H u r - hBarX u₀ H u r')| := by
        dsimp only [V]; congr 1; ring
      _ ≤ |S (u, r) - S (u, r')| + |hBarX u₀ H u r - hBarX u₀ H u r'| := abs_sub _ _
      _ ≤ x * |(r : ℝ) - r'| + x / 2 * |(r : ℝ) - r'| :=
        add_le_add (abs_sub_le hS u hu r r') (abs_hBarX_sub_le hH u r r')
      _ = (3 * x / 2) * |(r : ℝ) - r'| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
  change |(2 * a r * q r + b r * V r - a r * β r) -
    (2 * a r' * q r' + b r' * V r' - a r' * β r')| ≤ _
  calc
    _ = |2 * a r * (q r - q r') + 2 * (a r - a r') * q r' +
        (b r - b r') * V r + b r' * (V r - V r') -
        (a r - a r') * β r - a r' * (β r - β r')| := by congr 1; ring
    _ ≤ |2 * a r * (q r - q r')| + |2 * (a r - a r') * q r'| +
        |(b r - b r') * V r| + |b r' * (V r - V r')| +
        |(a r - a r') * β r| + |a r' * (β r - β r')| := by
      repeat first | exact le_rfl | apply le_trans (abs_sub _ _)
                   | apply le_trans (abs_add_le _ _) | apply add_le_add
    _ ≤ 2 * (π / 12 * x ^ 2) * |q r - q r'| +
        2 * (π * x ^ 2 / 2 * ρ) * x +
        (5 * π ^ 2 * x ^ 4 / 6 * ρ + 5 * π * x / 3 * ω) * (2 * x) +
        (π * x ^ 2 / 2) * ((3 * x / 2) * ρ) +
        (π * x ^ 2 / 2 * ρ) * (x / 2) + (π / 12 * x ^ 2) * (ω / 2) := by
      simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
    _ = _ := by ring

private theorem iterate_radial_bound {u₀ : ℝ≥0} {x : ℝ}
    (data : C(ℝ≥0, ℝ)) (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ))
    (hb : ∀ n, MemXBall u₀ x (h n)) (hzero : h 0 = constantDataField data)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n) data)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hmod : ∀ r r' : ℝ≥0, |(r : ℝ) - r'| ≤ δ →
      |derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) r -
        derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) r'| ≤ ε) :
    let L := π / 12 * x ^ 2
    let J := 2 * L + (5 * π ^ 2 * x ^ 5 / 3 + 2 * π * x ^ 3) +
      27 * π * x ^ 2 / 8 + 1
    ∀ (n : ℕ) (t : Icc (0 : ℝ) u₀) (r r' : ℝ≥0),
      exp (L * t) * |(r : ℝ) - r'| ≤ δ →
      |derivWithin (fun z : ℝ => h n ((t : ℝ).toNNReal, z.toNNReal)) (Ici 0) r -
        derivWithin (fun z : ℝ => h n ((t : ℝ).toNNReal, z.toNNReal)) (Ici 0) r'| ≤
        exp (J * t) * (ε + δ) := by
  dsimp only
  let L := π / 12 * x ^ 2
  let C := 5 * π ^ 2 * x ^ 5 / 3 + 2 * π * x ^ 3
  let D := 27 * π * x ^ 2 / 8
  let J := 2 * L + C + D + 1
  let q := fun (n : ℕ) (u r : ℝ≥0) =>
    derivWithin (fun z : ℝ => h n (u, z.toNNReal)) (Ici 0) r
  have hx := x_nonneg (hb 0)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hm : 0 < ε + δ := add_pos hε hδ
  have hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0) := by
    simpa only [hzero, constantDataField, ContinuousMap.coe_mk] using (hb 0).1 0 bot_le
  have htrace (n : ℕ) (r : ℝ≥0) : h n (0, r) = data r := by
    cases n with
    | zero => rw [hzero]; rfl
    | succ n => rw [hstep]; exact linearStep_zero (hb n) data r
  have hqzero (n : ℕ) (r : ℝ≥0) : q n 0 r =
      derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) r := by
    simp only [q, htrace]
  have hqinit (u r : ℝ≥0) : q 0 u r =
      derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) r := by
    dsimp only [q]
    rw [hzero]
    rfl
  change ∀ (n : ℕ) (t : Icc (0 : ℝ) u₀) (r r' : ℝ≥0),
    exp (L * t) * |(r : ℝ) - r'| ≤ δ →
    |q n (t : ℝ).toNNReal r - q n (t : ℝ).toNNReal r'| ≤ exp (J * t) * (ε + δ)
  intro n
  induction n with
  | zero =>
    intro t r r' hr
    rw [hqinit, hqinit]
    have hd : |(r : ℝ) - r'| ≤ δ :=
      (le_mul_of_one_le_left (abs_nonneg _) (one_le_exp (mul_nonneg hL t.2.1))).trans hr
    exact (hmod r r' hd).trans ((le_add_of_nonneg_right hδ.le).trans
      (le_mul_of_one_le_left hm.le (one_le_exp (mul_nonneg hJ t.2.1))))
  | succ n ih =>
    intro t r r' hr
    let χ := characteristic (hb n) t r
    let χ' := characteristic (hb n) t r'
    have hc := isCharacteristic_characteristic (hb n) t r
    have hc' := isCharacteristic_characteristic (hb n) t r'
    let ψ := fun s : ℝ => q (n + 1) s.toNNReal (χ s).toNNReal -
      q (n + 1) s.toNNReal (χ' s).toNNReal
    let F := fun (s : ℝ) (z : ℝ≥0) =>
      2 * linearCoeff (hb n) s.toNNReal z * q (n + 1) s.toNNReal z +
        (1 / 2 * deriv2GBarX (hb n) s.toNNReal z) *
          (h (n + 1) (s.toNNReal, z) - hBarX u₀ (h n) s.toNNReal z) -
        linearCoeff (hb n) s.toNNReal z * derivHBarX (hb n) s.toNNReal z
    let ψ' := fun s : ℝ => F s (χ s).toNNReal - F s (χ' s).toNNReal
    have hd (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
        HasDerivWithinAt ψ (ψ' s) (Icc 0 (t : ℝ)) s :=
      (hasDerivWithinAt_step_deriv hc data hdata (hstep n) hs).sub
        (hasDerivWithinAt_step_deriv hc' data hdata (hstep n) hs)
    have hn (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
        0 ≤ χ s ∧ 0 ≤ χ' s :=
      ⟨r.coe_nonneg.trans (hc.mem_Icc hs).1, r'.coe_nonneg.trans (hc'.mem_Icc hs).1⟩
    have hsep (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
        |((χ s).toNNReal : ℝ) - (χ' s).toNNReal| ≤
          exp (L * ((t : ℝ) - s)) * |(r : ℝ) - r'| := by
      rw [Real.coe_toNNReal _ (hn s hs).1, Real.coe_toNNReal _ (hn s hs).2]
      exact characteristic_sub_le (hb n) t r r' hs
    have hscale (s : ℝ) : exp (L * s) *
        (exp (L * ((t : ℝ) - s)) * |(r : ℝ) - r'|) ≤ δ := by
      rw [← mul_assoc, ← exp_add]
      rw [show L * s + L * ((t : ℝ) - s) = L * t by ring]
      exact hr
    have hbψ (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
        |ψ' s| ≤ 2 * L * |ψ s| + (C + D) * (exp (J * s) * (ε + δ)) := by
      let ρ := exp (L * ((t : ℝ) - s)) * |(r : ℝ) - r'|
      have hρ : ρ ≤ δ :=
        (le_mul_of_one_le_left (by positivity : 0 ≤ ρ)
          (one_le_exp (mul_nonneg hL hs.1))).trans (hscale s)
      have ht0 : s ≤ (u₀ : ℝ) := hs.2.trans t.2.2
      have hprior (z z' : ℝ≥0) (hz : |(z : ℝ) - z'| ≤ ρ) :
          |q n s.toNNReal z - q n s.toNNReal z'| ≤ exp (J * s) * (ε + δ) := by
        exact ih ⟨s, hs.1, ht0⟩ z z'
          ((mul_le_mul_of_nonneg_left hz (exp_pos _).le).trans (hscale s))
      have hh := abs_deriv_transport_sub_le (hb n) (hb (n + 1)) s.toNNReal
        (Real.toNNReal_le_iff_le_coe.mpr ht0) hprior (χ s).toNNReal (χ' s).toNNReal
        (hsep s hs)
      change |ψ' s| ≤ 2 * L * |ψ s| + C * ρ + D * (exp (J * s) * (ε + δ)) at hh
      have hρB : ρ ≤ exp (J * s) * (ε + δ) := hρ.trans
        ((le_add_of_nonneg_left hε.le).trans
          (le_mul_of_one_le_left hm.le (one_le_exp (mul_nonneg hJ hs.1))))
      calc
        _ ≤ 2 * L * |ψ s| + C * ρ + D * (exp (J * s) * (ε + δ)) := hh
        _ ≤ 2 * L * |ψ s| + C * (exp (J * s) * (ε + δ)) +
            D * (exp (J * s) * (ε + δ)) := by gcongr
        _ = _ := by ring
    have hψ0 : ‖ψ 0‖ ≤ exp (J * 0) * (ε + δ) := by
      have hs : (0 : ℝ) ∈ Icc 0 (t : ℝ) := ⟨le_rfl, t.2.1⟩
      have hh := hmod (χ 0).toNNReal (χ' 0).toNNReal
        ((hsep 0 hs).trans (by simpa only [sub_zero] using hr))
      simpa only [ψ, Real.toNNReal_zero, hqzero, Real.norm_eq_abs, mul_zero,
        exp_zero, one_mul] using hh.trans (le_add_of_nonneg_right hδ.le)
    have hB (s : ℝ) : HasDerivAt (fun v : ℝ => exp (J * v) * (ε + δ))
        (J * (exp (J * s) * (ε + δ))) s := by
      convert (((hasDerivAt_id s).const_mul J).exp.mul_const (ε + δ)) using 1
      · rfl
      · dsimp only [id]; ring
    have hbound := image_norm_le_of_norm_deriv_right_lt_deriv_boundary
      (HasDerivWithinAt.continuousOn hd)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs)) hψ0 hB (fun s hs heq => by
          have hh := hbψ s (Ico_subset_Icc_self hs)
          rw [Real.norm_eq_abs] at heq ⊢
          rw [heq] at hh
          have hpos : 0 < exp (J * s) * (ε + δ) := mul_pos (exp_pos _) hm
          dsimp only [J] at *
          nlinarith only [hh, hpos]) (show (t : ℝ) ∈ Icc 0 (t : ℝ) from ⟨t.2.1, le_rfl⟩)
    simpa only [ψ, χ, χ', hc.1, hc'.1, Real.toNNReal_coe, Real.norm_eq_abs] using hbound

private theorem iterate_radial_equicontinuity {u₀ : ℝ≥0} {x : ℝ}
    (data : C(ℝ≥0, ℝ)) (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ))
    (hb : ∀ n, MemXBall u₀ x (h n)) (hzero : h 0 = constantDataField data)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n) data) :
    ∀ ε > 0, ∃ η > 0, ∀ (n : ℕ) (u : ℝ≥0), u ≤ u₀ → ∀ r r' : ℝ≥0,
      |(r : ℝ) - r'| < η →
      |derivWithin (fun z : ℝ => h n (u, z.toNNReal)) (Ici 0) r -
        derivWithin (fun z : ℝ => h n (u, z.toNNReal)) (Ici 0) r'| < ε := by
  intro ε hε
  let L := π / 12 * x ^ 2
  let J := 2 * L + (5 * π ^ 2 * x ^ 5 / 3 + 2 * π * x ^ 3) +
    27 * π * x ^ 2 / 8 + 1
  have hx := x_nonneg (hb 0)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hJ : 0 ≤ J := by dsimp only [J, L]; positivity
  let e := ε / (4 * exp (J * u₀))
  have he : 0 < e := by dsimp only [e]; positivity
  have huc := uniformContinuous_slice_deriv (hb 0) 0 bot_le
  rw [hzero] at huc
  change UniformContinuous (fun r : ℝ≥0 =>
    derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) r) at huc
  obtain ⟨d, hd, hmod⟩ := Metric.uniformContinuous_iff.mp huc e he
  let δ := min (d / 2) e
  have hδ : 0 < δ := lt_min (half_pos hd) he
  have hmod' (r r' : ℝ≥0) (hr : |(r : ℝ) - r'| ≤ δ) :
      |derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) r -
        derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) r'| ≤ e := by
    apply le_of_lt
    apply hmod
    change |(r : ℝ) - r'| < d
    exact hr.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hd))
  refine ⟨δ / exp (L * u₀), div_pos hδ (exp_pos _), ?_⟩
  intro n u hu r r' hr
  have hscaled : exp (L * (u : ℝ)) * |(r : ℝ) - r'| ≤ δ := by
    calc
      _ ≤ exp (L * u₀) * |(r : ℝ) - r'| := by gcongr
      _ ≤ δ := by simpa only [mul_comm] using (le_div_iff₀ (exp_pos _)).mp hr.le
  have hh := iterate_radial_bound data h hb hzero hstep e δ he hδ hmod'
    n ⟨u, u.coe_nonneg, by exact_mod_cast hu⟩ r r' hscaled
  simp only [Real.toNNReal_coe] at hh
  calc
    _ ≤ exp (J * (u : ℝ)) * (e + δ) := hh
    _ ≤ exp (J * u₀) * (e + e) := by
      gcongr
      exact min_le_right _ _
    _ = ε / 2 := by dsimp only [e]; field_simp; ring
    _ < ε := half_lt_self hε

/-- Along one characteristic, the radial derivative of a bounded step is Lipschitz in time. -/
theorem step_deriv_along_sub_le {u₀ : ℝ≥0} {x : ℝ}
    {H S : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H}
    (hS : MemXBall u₀ x S) {t : Icc (0 : ℝ) u₀} {r : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH t r χ) (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun z : ℝ => data z.toNNReal) (Ici 0))
    (hstep : S = linearStepMap hH data) {s s' : ℝ}
    (hs : s ∈ Icc 0 (t : ℝ)) (hs' : s' ∈ Icc 0 (t : ℝ)) :
    let q := fun u r : ℝ≥0 =>
      derivWithin (fun z : ℝ => S (u, z.toNNReal)) (Ici 0) r
    |q s.toNNReal (χ s).toNNReal - q s'.toNNReal (χ s').toNNReal| ≤
      (29 * π * x ^ 3 / 24) * |s - s'| := by
  have hd (v : ℝ) (hv : v ∈ Icc 0 (t : ℝ)) :=
    hasDerivWithinAt_step_deriv hχ data hdata hstep hv
  have hbound (v : ℝ) (hv : v ∈ Icc 0 (t : ℝ)) :=
    abs_deriv_transport_le hH hS v.toNNReal
      (Real.toNNReal_le_iff_le_coe.mpr (hv.2.trans t.2.2)) (χ v).toNNReal
  have hh := (convex_Icc (0 : ℝ) (t : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd (fun v hv => by simpa only [Real.norm_eq_abs] using hbound v hv) hs' hs
  simpa only [Real.norm_eq_abs] using hh

/-- The derivatives of any bounded linear iteration are uniformly equicontinuous on the strip. -/
theorem iterate_deriv_uniformEquicontinuousOn {u₀ : ℝ≥0} {x : ℝ}
    (data : C(ℝ≥0, ℝ))
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ)) (hb : ∀ n, MemXBall u₀ x (h n))
    (hzero : h 0 = constantDataField data)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n) data) :
    UniformEquicontinuousOn
      (fun n (p : ℝ × ℝ) => derivWithin
        (fun s : ℝ => h n (p.1.toNNReal, s.toNNReal)) (Ici 0) p.2)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) := by
  rw [← uniformEquicontinuous_restrict_iff]
  apply Metric.uniformEquicontinuous_iff.mpr
  intro ε hε
  obtain ⟨η, hη, hrad⟩ := iterate_radial_equicontinuity data h hb hzero hstep
    (ε / 2) (half_pos hε)
  let M := 29 * π * x ^ 3 / 24
  have hx := x_nonneg (hb 0)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  let δ := min (η / 2) (ε / (2 * (M + 1)))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let q := fun (n : ℕ) (u r : ℝ≥0) =>
    derivWithin (fun z : ℝ => h n (u, z.toNNReal)) (Ici 0) r
  have hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0) := by
    simpa only [hzero, constantDataField, ContinuousMap.coe_mk] using (hb 0).1 0 bot_le
  have ordered (n : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : v ≤ u₀) (huv : u ≤ v)
      (r r' : ℝ≥0) (ht : |v - u| < δ) (hr : |(r' : ℝ) - r| < δ) :
      |q n v.toNNReal r' - q n u.toNNReal r| < ε := by
    have hut : u.toNNReal ≤ u₀ := Real.toNNReal_le_iff_le_coe.mpr (huv.trans hv)
    have hδr : δ ≤ η / 2 := min_le_left _ _
    have hδε : δ ≤ ε / (2 * (M + 1)) := min_le_right _ _
    have hvu : 0 ≤ v - u := sub_nonneg.mpr huv
    have hrη : |(r' : ℝ) - r| < η := hr.trans_le (hδr.trans (half_le_self hη.le))
    cases n with
    | zero =>
      have hh := hrad 0 u.toNNReal hut r' r hrη
      have heq : q 0 v.toNNReal r' = q 0 u.toNNReal r' := by
        dsimp only [q]
        rw [hzero]
        rfl
      rw [heq]
      exact hh.trans (half_lt_self hε)
    | succ n =>
      let t : Icc (0 : ℝ) u₀ := ⟨v, hu.trans huv, hv⟩
      let χ := characteristic (hb n) t r'
      have hc := isCharacteristic_characteristic (hb n) t r'
      have hu' : u ∈ Icc 0 (t : ℝ) := ⟨hu, huv⟩
      have hv' : v ∈ Icc 0 (t : ℝ) := ⟨hu.trans huv, le_rfl⟩
      have hχ := hc.mem_Icc hu'
      have hχ0 : 0 ≤ χ u := r'.coe_nonneg.trans hχ.1
      have hχr : |((χ u).toNNReal : ℝ) - r| < η := by
        rw [Real.coe_toNNReal _ hχ0]
        calc
          _ ≤ |χ u - (r' : ℝ)| + |(r' : ℝ) - r| := _root_.abs_sub_le _ _ _
          _ ≤ (v - u) / 2 + |(r' : ℝ) - r| := by
            apply add_le_add _ le_rfl
            rw [abs_of_nonneg (sub_nonneg.mpr hχ.1)]
            linarith only [hχ.2]
          _ < η := by
            rw [abs_of_nonneg hvu] at ht
            linarith only [ht, hr, hδr, hη]
      have hf := step_deriv_along_sub_le (hb (n + 1)) hc data hdata (hstep n) hv' hu'
      dsimp only at hf
      rw [show characteristic (hb n) t r' v = r' from hc.1,
        Real.toNNReal_coe] at hf
      change |q (n + 1) v.toNNReal r' - q (n + 1) u.toNNReal (χ u).toNNReal| ≤
        M * |v - u| at hf
      have htime : M * |v - u| < ε / 2 := by
        have hlt := (mul_lt_mul_of_pos_left (ht.trans_le hδε)
          (show 0 < M + 1 by positivity))
        have heq : (M + 1) * (ε / (2 * (M + 1))) = ε / 2 := by field_simp
        rw [heq] at hlt
        exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
          (abs_nonneg _)).trans_lt hlt
      have hrq := hrad (n + 1) u.toNNReal hut (χ u).toNNReal r hχr
      calc
        _ ≤ |q (n + 1) v.toNNReal r' - q (n + 1) u.toNNReal (χ u).toNNReal| +
            |q (n + 1) u.toNNReal (χ u).toNNReal - q (n + 1) u.toNNReal r| :=
          _root_.abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add (hf.trans_lt htime) hrq
        _ = ε := add_halves ε
  refine ⟨δ, hδ, ?_⟩
  intro p p' hpp n
  have hp := p.property
  have hp' := p'.property
  change max |p.val.1 - p'.val.1| |p.val.2 - p'.val.2| < δ at hpp
  have ht : |p'.val.1 - p.val.1| < δ := by
    rw [abs_sub_comm]
    exact (le_max_left _ _).trans_lt hpp
  have hr : |p'.val.2 - p.val.2| < δ := by
    rw [abs_sub_comm]
    exact (le_max_right _ _).trans_lt hpp
  have hq : |q n p'.val.1.toNNReal p'.val.2.toNNReal -
      q n p.val.1.toNNReal p.val.2.toNNReal| < ε := by
    rcases le_total p.val.1 p'.val.1 with huv | hvu
    · apply ordered n _ _ hp.1.1 hp'.1.2 huv _ _ ht
      simpa only [Real.coe_toNNReal _ hp.2, Real.coe_toNNReal _ hp'.2] using hr
    · rw [abs_sub_comm]
      apply ordered n _ _ hp'.1.1 hp.1.2 hvu
      · simpa only [abs_sub_comm] using ht
      · simpa only [Real.coe_toNNReal _ hp.2, Real.coe_toNNReal _ hp'.2,
          abs_sub_comm] using hr
  simpa only [Function.comp_apply, Set.domRestrict_apply, q, Real.coe_toNNReal _ hp.2,
    Real.coe_toNNReal _ hp'.2, Real.dist_eq, abs_sub_comm] using hq

end XEq
end Christodoulou.Bondi
