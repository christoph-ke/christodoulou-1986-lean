module
public import Christodoulou.Frozen.Bondi.TranslatedDataField
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Mathlib.Topology.UniformSpace.Equicontinuity
import Christodoulou.Bondi.DerivEquicontinuity
import Christodoulou.Frozen.Bondi.TranslatedDataFieldApply
import Christodoulou.Frozen.Bondi.IsCharacteristicMemIcc
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic
import Christodoulou.Frozen.Bondi.LinearStepZero
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.ODE.Gronwall

/-!
# Equicontinuity for the translated seed

The seed derivative is the initial derivative evaluated at `r + u / 2`. Its radial modulus
is preserved by translation, and its joint modulus follows from the distance between the
translated arguments. The characteristic comparison and exponential majorant then propagate
the radial modulus to every bounded iterate on any finite strip.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XTE

open XEq

private lemma translatedDataField_real_apply (T : ℝ≥0) (data : C(ℝ≥0, ℝ))
    (u : ℝ≥0) (hu : u ≤ T) (z : ℝ) (hz : 0 ≤ z) :
    translatedDataField T data (u, z.toNNReal) = data (z + (u : ℝ) / 2).toNNReal := by
  rw [translatedDataField_apply T data u z.toNNReal hu]
  congr 1
  apply NNReal.coe_injective
  have hzshift : 0 ≤ z + (u : ℝ) / 2 :=
    add_nonneg hz (div_nonneg u.coe_nonneg (by norm_num))
  simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat,
    Real.coe_toNNReal z hz, Real.coe_toNNReal (z + (u : ℝ) / 2) hzshift]

private lemma translatedDataField_derivWithin (T : ℝ≥0) (data : C(ℝ≥0, ℝ))
    (hdata : IsDecaySlice data) (u : ℝ≥0) (hu : u ≤ T) (z : ℝ) (hz : 0 ≤ z) :
    derivWithin (fun s : ℝ => translatedDataField T data (u, s.toNNReal)) (Ici 0) z =
      derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (z + (u : ℝ) / 2) := by
  have hshift : MapsTo (fun s : ℝ => s + (u : ℝ) / 2) (Ici 0) (Ici 0) :=
    fun s hs => add_nonneg hs (div_nonneg u.coe_nonneg (by norm_num))
  have hd := (hdata.1.1.differentiableOn one_ne_zero _ (hshift hz)).hasDerivWithinAt
  have hcomp := hd.comp z ((hasDerivAt_id z).add_const ((u : ℝ) / 2)).hasDerivWithinAt
    hshift
  have hseed : HasDerivWithinAt
      (fun s : ℝ => translatedDataField T data (u, s.toNNReal))
      (derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (z + (u : ℝ) / 2))
      (Ici 0) z := by
    simpa only [Function.comp_def, mul_one] using hcomp.congr_of_mem
      (fun s hs => translatedDataField_real_apply T data u hu s hs) hz
  exact hseed.derivWithin (uniqueDiffOn_Ici 0 z hz)

private lemma seed_deriv (T : ℝ≥0) (data : C(ℝ≥0, ℝ))
    (hdata : IsDecaySlice data) (u r : ℝ≥0) (hu : u ≤ T) :
    derivWithin (fun z : ℝ => translatedDataField T data (u, z.toNNReal)) (Ici 0) r =
      derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) (r + u / 2 : ℝ≥0) := by
  simpa only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat] using
    translatedDataField_derivWithin T data hdata u hu r r.coe_nonneg

private lemma seed_zero (T : ℝ≥0) (data : C(ℝ≥0, ℝ)) (r : ℝ≥0) :
    translatedDataField T data (0, r) = data r := by
  rw [translatedDataField_apply T data 0 r bot_le, zero_div, add_zero]

private theorem iterate_radial_bound {u₀ : ℝ≥0} {x : ℝ}
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ))
    (hb : ∀ n, MemXBall u₀ x (h n)) (hzero : h 0 = translatedDataField u₀ data)
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
  have htrace (n : ℕ) (r : ℝ≥0) : h n (0, r) = data r := by
    cases n with
    | zero => rw [hzero]; exact seed_zero u₀ data r
    | succ n => rw [hstep]; exact linearStep_zero (hb n) data r
  have hqzero (n : ℕ) (r : ℝ≥0) : q n 0 r =
      derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) r := by
    simp only [q, htrace]
  have hqinit (u r : ℝ≥0) (hu : u ≤ u₀) : q 0 u r =
      derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) (r + u / 2 : ℝ≥0) := by
    dsimp only [q]
    rw [hzero]
    exact seed_deriv u₀ data hdata u r hu
  change ∀ (n : ℕ) (t : Icc (0 : ℝ) u₀) (r r' : ℝ≥0),
    exp (L * t) * |(r : ℝ) - r'| ≤ δ →
    |q n (t : ℝ).toNNReal r - q n (t : ℝ).toNNReal r'| ≤ exp (J * t) * (ε + δ)
  intro n
  induction n with
  | zero =>
    intro t r r' hr
    have htu : (t : ℝ).toNNReal ≤ u₀ := Real.toNNReal_le_iff_le_coe.mpr t.2.2
    rw [hqinit _ _ htu, hqinit _ _ htu]
    have hd : |(r : ℝ) - r'| ≤ δ :=
      (le_mul_of_one_le_left (abs_nonneg _) (one_le_exp (mul_nonneg hL t.2.1))).trans hr
    have hshift : |((r + (t : ℝ).toNNReal / 2 : ℝ≥0) : ℝ) -
        (r' + (t : ℝ).toNNReal / 2 : ℝ≥0)| ≤ δ := by
      simpa only [NNReal.coe_add, add_sub_add_right_eq_sub] using hd
    exact (hmod _ _ hshift).trans ((le_add_of_nonneg_right hδ.le).trans
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
      (hasDerivWithinAt_step_deriv hc data hdata.1.1 (hstep n) hs).sub
        (hasDerivWithinAt_step_deriv hc' data hdata.1.1 (hstep n) hs)
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
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ))
    (hb : ∀ n, MemXBall u₀ x (h n)) (hzero : h 0 = translatedDataField u₀ data)
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
  simp only [seed_zero] at huc
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
  have hh := iterate_radial_bound data hdata h hb hzero hstep e δ he hδ hmod'
    n ⟨u, u.coe_nonneg, by exact_mod_cast hu⟩ r r' hscaled
  simp only [Real.toNNReal_coe] at hh
  calc
    _ ≤ exp (J * (u : ℝ)) * (e + δ) := hh
    _ ≤ exp (J * u₀) * (e + e) := by
      gcongr
      exact min_le_right _ _
    _ = ε / 2 := by dsimp only [e]; field_simp; ring
    _ < ε := half_lt_self hε

/-- The argument of Lemma 3 for the translated seed (9.2): uniform equicontinuity of the radial
derivatives on the strip. -/
theorem translated_iterate_deriv_uniformEquicontinuousOn {T : ℝ≥0} {x : ℝ}
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ)) (hb : ∀ n, MemXBall T x (h n))
    (hzero : h 0 = translatedDataField T data)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n) data) :
    UniformEquicontinuousOn (fun n (p : ℝ × ℝ) => derivWithin
      (fun z : ℝ => h n (p.1.toNNReal, z.toNNReal)) (Ici 0) p.2)
      (Icc 0 (T : ℝ) ×ˢ Ici 0) := by
  rw [← uniformEquicontinuous_restrict_iff]
  apply Metric.uniformEquicontinuous_iff.mpr
  intro ε hε
  obtain ⟨η, hη, hrad⟩ := iterate_radial_equicontinuity data hdata h hb hzero hstep
    (ε / 2) (half_pos hε)
  let M := 29 * π * x ^ 3 / 24
  have hx := x_nonneg (hb 0)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  let δ := min (η / 2) (ε / (2 * (M + 1)))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let q := fun (n : ℕ) (u r : ℝ≥0) =>
    derivWithin (fun z : ℝ => h n (u, z.toNNReal)) (Ici 0) r
  have ordered (n : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : v ≤ T) (huv : u ≤ v)
      (r r' : ℝ≥0) (ht : |v - u| < δ) (hr : |(r' : ℝ) - r| < δ) :
      |q n v.toNNReal r' - q n u.toNNReal r| < ε := by
    have hut : u.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr (huv.trans hv)
    have hδr : δ ≤ η / 2 := min_le_left _ _
    have hδε : δ ≤ ε / (2 * (M + 1)) := min_le_right _ _
    have hvu : 0 ≤ v - u := sub_nonneg.mpr huv
    cases n with
    | zero =>
      have hvt : v.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hv
      have hshift : |((r' + v.toNNReal / 2 : ℝ≥0) : ℝ) -
          (r + u.toNNReal / 2 : ℝ≥0)| < η := by
        simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat,
          Real.coe_toNNReal _ hu, Real.coe_toNNReal _ (hu.trans huv)]
        calc
          _ = |((r' : ℝ) - r) + (v - u) / 2| := by congr 1; ring
          _ ≤ |(r' : ℝ) - r| + |v - u| / 2 := by
            simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
              abs_add_le ((r' : ℝ) - r) ((v - u) / 2)
          _ < η := by linarith only [hr, ht, hδr, hη]
      have hh := hrad 0 0 bot_le (r' + v.toNNReal / 2) (r + u.toNNReal / 2) hshift
      dsimp only [q]
      rw [hzero, seed_deriv T data hdata _ _ hvt, seed_deriv T data hdata _ _ hut]
      simpa only [hzero, seed_zero] using hh.trans (half_lt_self hε)
    | succ n =>
      let t : Icc (0 : ℝ) T := ⟨v, hu.trans huv, hv⟩
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
      have hf := step_deriv_along_sub_le (hb (n + 1)) hc data hdata.1.1 (hstep n) hv' hu'
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

end XTE
end Christodoulou.Bondi
