module
public import Christodoulou.Frozen.Bondi.HasDerivAtMassCurry
public import Christodoulou.Frozen.Bondi.HasDerivAtMass
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.G
public import Christodoulou.Frozen.Bondi.GPos
public import Christodoulou.Frozen.Bondi.GBar
public import Christodoulou.Frozen.Bondi.Xi
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.IsCharacteristicStrictAntiOn
public import Christodoulou.Frozen.Bondi.CharField
public import Christodoulou.Frozen.Bondi.CharFieldOfLe
public import Christodoulou.Frozen.Bondi.GBarX
public import Christodoulou.Frozen.Bondi.GBarXOfLe
public import Christodoulou.Frozen.Bondi.GX
public import Christodoulou.Frozen.Bondi.GXOfLe
public import Christodoulou.Frozen.Bondi.ContinuousGBarX
public import Christodoulou.Frozen.Radial.Mean
public import Christodoulou.Bondi.XBallContinuity
public import Christodoulou.Radial.MeanBasic
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Mass evolution along incoming characteristics

A mean-value chain rule combines the frozen time and radial mass derivatives to prove
(4.6) along an incoming light ray. Joint continuity of the radial coefficient follows
from the X-ball metric coefficients and the unit-interval formula for the radial mean.
-/

public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi

open Christodoulou.Radial

namespace XMC

/-- A chain rule using a time partial at the base point and a jointly continuous
radial partial nearby. The uniform radial remainder is the parametric mean value theorem. -/
theorem hasDerivAt_diagonal_of_partial
    {f d : ℝ → ℝ → ℝ} {χ : ℝ → ℝ} {t a b : ℝ}
    (ht : HasDerivAt (fun s => f s (χ t)) a t)
    (hχ : HasDerivAt χ b t)
    (hd : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, χ t), HasDerivAt (f p.1) (d p.1 p.2) p.2)
    (hc : ContinuousAt (fun p : ℝ × ℝ => d p.1 p.2) (t, χ t)) :
    HasDerivAt (fun s => f s (χ s)) (a + d t (χ t) * b) t := by
  have hr : (fun s => f s (χ s) - f s (χ t) - (χ s - χ t) * d t (χ t))
      =o[𝓝 t] (fun s => χ s - χ t) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have hd' : ∀ᶠ p : ℝ × ℝ in 𝓝 t ×ˢ 𝓝 (χ t),
        HasDerivAt (f p.1) (d p.1 p.2) p.2 := by
      simpa only [← nhds_prod_eq] using hd
    have hds := Filter.Eventually.segment_of_prod_nhds
      (r := fun s r => HasDerivAt (f s) (d s r) r)
      tendsto_const_nhds hχ.continuousAt hd'
    have he : ∀ᶠ p : ℝ × ℝ in 𝓝 t ×ˢ 𝓝 (χ t),
        ‖d p.1 p.2 - d t (χ t)‖ < ε := by
      rw [← nhds_prod_eq]
      exact hc.eventually (Metric.ball_mem_nhds _ hε)
    have hes := Filter.Eventually.segment_of_prod_nhds
      (r := fun s r => ‖d s r - d t (χ t)‖ < ε)
      tendsto_const_nhds hχ.continuousAt he
    filter_upwards [hds, hes] with s hds hes
    have hm := (convex_segment (χ t) (χ s)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z => f s z - z * d t (χ t))
      (f' := fun z => d s z - d t (χ t))
      (fun z hz => by
        simpa only [one_mul, Pi.sub_apply, id_eq] using!
          ((hds z hz).sub ((hasDerivAt_id z).mul_const (d t (χ t)))).hasDerivWithinAt
            (s := segment ℝ (χ t) (χ s)))
      (fun z hz => (hes z hz).le) (left_mem_segment ..) (right_mem_segment ..)
    convert hm using 1
    congr 1
    ring
  have hrem := (hr.trans_isBigO hχ.isBigO_sub).add
    (ht.isLittleO.add (hχ.isLittleO.const_mul_left (d t (χ t))))
  apply HasDerivAt.of_isLittleO
  convert hrem using 1
  ext s
  simp only [smul_eq_mul]
  ring

/-- The radial mean is jointly continuous, including the centre, for any continuous field. -/
theorem continuous_mean_joint (H : C(ℝ≥0 × ℝ≥0, ℝ)) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => mean (H.curry p.1) p.2) := by
  simp_rw [mean_eq_integral_unitInterval]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact H.continuous.comp
    ((continuous_fst.comp continuous_fst).prodMk
      (continuous_real_toNNReal.comp
        ((NNReal.continuous_coe.comp (continuous_snd.comp continuous_fst)).mul continuous_snd)))

/-- A continuous extension of the radial mass derivative from the closed strip.
Only the metric coefficients are clamped; on the strip this is exactly (4.4). -/
theorem continuous_mass_radial_coefficient {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hX : MemXBall u₀ x H) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 =>
      2 * π * (gBarX hX p.1 p.2 / gX hX p.1 p.2)
        * (H p - mean (H.curry p.1) p.2) ^ 2) := by
  have hn (p : ℝ≥0 × ℝ≥0) : gX hX p.1 p.2 ≠ 0 :=
    (g_pos _ _ _).ne'
  exact (continuous_const.mul ((continuous_gBarX hX).div (continuous_gX hX) hn)).mul
    ((H.continuous.sub (continuous_mean_joint H)).pow 2)


theorem radialDerivative_bound_of_memXBall {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hX : MemXBall u₀ x H) :
    ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |radialDerivative H u r| ≤ x * (1 + (r : ℝ)) ^ (-4 : ℤ) := by
  intro u hu r
  have hb := hX.2.2 u hu r
  have hd : (1 + (r : ℝ)) ^ 4 * |radialDerivative H u r| ≤ x :=
    (le_add_of_nonneg_left (by positivity)).trans hb
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hd)

/-- Equation (4.6) along an incoming characteristic at interior times. -/
theorem hasDerivAt_mass_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (hX : MemXBall u₀ x H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hX u₁ r₁ χ) {t : ℝ} (ht : 0 < t) (htu : t < u₁) :
    HasDerivAt (fun s : ℝ => mass (H.curry (Real.toNNReal s)) (hs (Real.toNNReal s))
        (Real.toNNReal (χ s)))
      (-(π / g (H.curry (Real.toNNReal t)) (hs (Real.toNNReal t)) (Real.toNNReal (χ t)))
        * xi (H.curry (Real.toNNReal t)) (hs (Real.toNNReal t)) (Real.toNNReal (χ t)) ^ 2) t := by
  have htT : t < (u₀ : ℝ) := htu.trans_le u₁.property.2
  have hrt : 0 < χ t := by
    have ha := hχ.strictAntiOn ⟨ht.le, htu.le⟩ ⟨u₁.property.1, le_rfl⟩ htu
    rw [hχ.1] at ha
    exact r₁.coe_nonneg.trans_lt ha
  have hχ' := (hχ.2 t ⟨ht.le, htu.le⟩).hasDerivAt (Icc_mem_nhds ht htu)
  rw [charField_of_le hX htT.le (hs _) (χ t)] at hχ'
  let f : ℝ → ℝ → ℝ := fun s r =>
    mass (H.curry s.toNNReal) (hs s.toNNReal) r.toNNReal
  let d : ℝ → ℝ → ℝ := fun s r =>
    2 * π * (gBarX hX s.toNNReal r.toNNReal / gX hX s.toNNReal r.toNNReal)
      * (H (s.toNNReal, r.toNNReal)
        - mean (H.curry s.toNNReal) r.toNNReal) ^ 2
  have hd : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, χ t),
      HasDerivAt (f p.1) (d p.1 p.2) p.2 := by
    have he : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, χ t), p.1 < (u₀ : ℝ) ∧ 0 < p.2 :=
      ((continuous_fst.tendsto (t, χ t)).eventually (gt_mem_nhds htT)).and
        ((continuous_snd.tendsto (t, χ t)).eventually (lt_mem_nhds hrt))
    filter_upwards [he] with p hp
    have hu : p.1.toNNReal ≤ u₀ := Real.toNNReal_le_iff_le_coe.mpr hp.1.le
    have hr := hasDerivAt_mass (H.curry p.1.toNNReal) (hs _) p.2.toNNReal
      (Real.toNNReal_pos.mpr hp.2)
    simpa only [f, d, gBarX_of_le hX hu (hs _), gX_of_le hX hu (hs _),
      Real.coe_toNNReal _ hp.2.le, ContinuousMap.curry_apply] using hr
  have hc : ContinuousAt (fun p : ℝ × ℝ => d p.1 p.2) (t, χ t) :=
    ((continuous_mass_radial_coefficient hX).comp
      ((continuous_real_toNNReal.comp continuous_fst).prodMk
        (continuous_real_toNNReal.comp continuous_snd))).continuousAt
  have htime := hasDerivAt_mass_curry hH hs (radialDerivative_bound_of_memXBall hX)
    t.toNNReal (Real.toNNReal_pos.mpr ht)
    (by exact_mod_cast (show (t.toNNReal : ℝ) < u₀ by
      simpa only [Real.coe_toNNReal _ ht.le] using htT))
    (χ t).toNNReal (Real.toNNReal_pos.mpr hrt)
  rw [Real.coe_toNNReal _ ht.le] at htime
  have hres := hasDerivAt_diagonal_of_partial (f := f) htime hχ' hd hc
  have hu : t.toNNReal ≤ u₀ := Real.toNNReal_le_iff_le_coe.mpr htT.le
  dsimp only [d] at hres
  rw [gBarX_of_le hX hu (hs _), gX_of_le hX hu (hs _)] at hres
  convert hres using 1
  ring

end XMC

end Christodoulou.Bondi
