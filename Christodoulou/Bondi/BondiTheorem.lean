module
public import Christodoulou.Frozen.Bondi.HasDerivAtMassCurry
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.BondiMassSpec
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.GX
public import Christodoulou.Frozen.Bondi.GBarX
public import Christodoulou.Frozen.Bondi.ContinuousGBarX
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.ExistsMemXBallOfIsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsClassicalSolutionIsSlice
public import Christodoulou.Frozen.Bondi.GLeOne
public import Christodoulou.Frozen.Bondi.GBarLeG
public import Christodoulou.Bondi.XBallContinuity
public import Christodoulou.Bondi.CoefficientRegularity
public import Christodoulou.Bondi.GBarBasic
public import Christodoulou.Bondi.RadialModulus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.MonotoneConvergence



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi

open Christodoulou.Radial

namespace XBT

/-- Continuity on the closed time strip, including both endpoints. -/
private theorem continuousOn_mass_curry {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hX : MemXBall u₀ x H) (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) (r : ℝ≥0) :
    ContinuousOn (fun v : ℝ => mass (H.curry v.toNNReal) (hs v.toNNReal) r)
      (Icc 0 (u₀ : ℝ)) := by
  have hp : Continuous (fun v : ℝ => (v.toNNReal, r)) :=
    continuous_real_toNNReal.prodMk continuous_const
  have hg := (continuous_gX hX).comp hp
  have hb := (continuous_gBarX hX).comp hp
  have hn (v : ℝ) : gX hX v.toNNReal r ≠ 0 :=
    (g_pos (H.curry (min v.toNNReal u₀))
      (hX.isSlice (min v.toNNReal u₀) (min_le_right _ _)) r).ne'
  have hc := (continuous_const (y := (r : ℝ) / 2)).mul
    ((continuous_const (y := (1 : ℝ))).sub (hb.div hg hn))
  apply hc.continuousOn.congr
  intro v hv
  have hv' : v.toNNReal ≤ u₀ := (Real.toNNReal_le_iff_le_coe).2 hv.2
  change mass (H.curry v.toNNReal) (hs v.toNNReal) r =
    (r : ℝ) / 2 * (1 - gBarX hX v.toNNReal r / gX hX v.toNNReal r)
  simp only [mass, gX, gBarX, min_eq_left hv']

/-- A uniform radial envelope supplied by the existing X-ball estimate. -/
private theorem gap_bound {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hX : MemXBall u₀ x H) {u : ℝ≥0} (hu : u ≤ u₀) (r : ℝ≥0) :
    |H (u, r) - mean (H.curry u) r| ≤ x / (1 + (r : ℝ)) := by
  have hx : 0 ≤ x := XEq.x_nonneg hX
  have hb := XCoef.abs_sub_hBarX_le hX u r
  simp only [hBarX, min_eq_left hu] at hb
  apply hb.trans
  have hr : 0 < 1 + (r : ℝ) := by positivity
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (1 + (r : ℝ)) ^ 2) hr).2
  nlinarith [mul_nonneg hx r.coe_nonneg, mul_nonneg hx (sq_nonneg (r : ℝ))]

/-- The evolution expression is bounded above by a vanishing radial envelope. -/
private theorem evolution_le_envelope {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hX : MemXBall u₀ x H) (hs : ∀ v : ℝ≥0, IsSlice (H.curry v))
    {u : ℝ≥0} (hu : u ≤ u₀) (r : ℝ≥0) :
    1 / 2 * gBar (H.curry u) (hs u) r
          * (2 * π * (gBar (H.curry u) (hs u) r / g (H.curry u) (hs u) r)
            * (H (u, r) - mean (H.curry u) r) ^ 2)
        - π / g (H.curry u) (hs u) r * xi (H.curry u) (hs u) r ^ 2
      ≤ π * (x / (1 + (r : ℝ))) ^ 2 := by
  have hg := g_pos (H.curry u) (hs u) r
  have hb := gBar_pos (H.curry u) (hs u) r
  have hb1 := (gBar_le_g (H.curry u) (hs u) r).trans (g_le_one _ _ _)
  have hratio : gBar (H.curry u) (hs u) r / g (H.curry u) (hs u) r ≤ 1 :=
    (div_le_one hg).2 (gBar_le_g _ _ _)
  have hratio0 := div_nonneg hb.le hg.le
  have hsq := pow_le_pow_left₀ (abs_nonneg _) (gap_bound hX hu r) 2
  rw [sq_abs] at hsq
  have hprod : gBar (H.curry u) (hs u) r *
      (gBar (H.curry u) (hs u) r / g (H.curry u) (hs u) r) ≤ 1 := by
    nlinarith
  have hpos : 0 ≤ π / g (H.curry u) (hs u) r * xi (H.curry u) (hs u) r ^ 2 :=
    mul_nonneg (div_nonneg pi_pos.le hg.le) (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hprod
    (mul_nonneg pi_pos.le (sq_nonneg (H (u, r) - mean (H.curry u) r))),
    mul_le_mul_of_nonneg_left hsq pi_pos.le]

/-- Derivative comparison followed by the radial limit of the mass. -/
private theorem antitoneOn_bondiMass_of_bound {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ}
    (hX : MemXBall u₀ x H) (hs : ∀ v : ℝ≥0, IsSlice (H.curry v))
    (hd : ∀ (r : ℝ≥0), 0 < r → ∀ v ∈ Ioo (0 : ℝ) (u₀ : ℝ),
      ∃ d : ℝ, HasDerivAt (fun v : ℝ => mass (H.curry v.toNNReal) (hs v.toNNReal) r) d v ∧
        d ≤ π * (x / (1 + (r : ℝ))) ^ 2) :
    AntitoneOn (fun u : ℝ≥0 => bondiMass (H.curry u) (hs u)) (Icc 0 u₀) := by
  intro a ha b hb hab
  have hm (r : ℝ≥0) (hr : 0 < r) :
      mass (H.curry b) (hs b) r - mass (H.curry a) (hs a) r ≤
        (π * (x / (1 + (r : ℝ))) ^ 2) * ((b : ℝ) - (a : ℝ)) := by
    have hc := continuousOn_mass_curry hX hs r
    have hh := (convex_Icc (0 : ℝ) (u₀ : ℝ)).image_sub_le_mul_sub_of_deriv_le hc
      (fun v hv => by
        rw [interior_Icc] at hv
        obtain ⟨d, hd, _⟩ := hd r hr v hv
        exact hd.differentiableAt.differentiableWithinAt)
      (fun v hv => by
        rw [interior_Icc] at hv
        obtain ⟨d, hd, hb⟩ := hd r hr v hv
        simpa [hd.deriv] using hb)
      (a : ℝ) ⟨a.coe_nonneg, ha.2⟩ (b : ℝ) ⟨b.coe_nonneg, hb.2⟩ hab
    simpa only [Real.toNNReal_coe] using hh
  have hi : Tendsto (fun r : ℝ≥0 => (1 + (r : ℝ))⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_add_const_left _ _ (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have he : Tendsto (fun r : ℝ≥0 => π * (x / (1 + (r : ℝ))) ^ 2 *
      ((b : ℝ) - (a : ℝ))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true] using (((hi.const_mul x).pow 2).const_mul π).mul_const
        ((b : ℝ) - (a : ℝ))
  have hlim := ((bondiMass_spec (H.curry b) (hs b)).2.1.sub
    (bondiMass_spec (H.curry a) (hs a)).2.1).sub he
  have hle : bondiMass (H.curry b) (hs b) - bondiMass (H.curry a) (hs a) - 0 ≤ 0 :=
    le_of_tendsto hlim (by
      filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with r hr
      exact sub_nonpos.2 (hm r hr))
  linarith

/-- Bondi mass is nonincreasing on the closed time strip (Bondi's theorem). -/
theorem antitoneOn_bondiMass {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) {C : ℝ}
    (hd : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ)) :
    AntitoneOn (fun u : ℝ≥0 => bondiMass (H.curry u) (hs u)) (Icc 0 u₀) := by
  obtain ⟨x, hX⟩ := exists_memXBall_of_isClassicalSolution hH ⟨C, hd⟩
  apply antitoneOn_bondiMass_of_bound hX hs
  intro r hr v hv
  have hv0 : 0 < v.toNNReal := Real.toNNReal_pos.2 hv.1
  have hvT : v.toNNReal < u₀ := by
    exact_mod_cast (show (v.toNNReal : ℝ) < (u₀ : ℝ) by
      simpa only [Real.coe_toNNReal v hv.1.le] using hv.2)
  refine ⟨_, ?_, evolution_le_envelope hX hs hvT.le r⟩
  simpa only [Real.coe_toNNReal v hv.1.le] using
    Christodoulou.Bondi.hasDerivAt_mass_curry hH hs hd v.toNNReal hv0 hvT r hr

/-- The time-clamped extension of a strip field. -/
@[expose] noncomputable def clampExt (u₀ : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) : C(ℝ≥0 × ℝ≥0, ℝ) :=
  H.comp ⟨fun p => (min p.1 u₀, p.2), by fun_prop⟩

/-- The clamped field evaluates the original field at the clamped time. -/
theorem clampExt_apply (u₀ : ℝ≥0) (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u r : ℝ≥0) :
    clampExt u₀ H (u, r) = H (min u u₀, r) := rfl

/-- Every slice on the closed strip agrees with the original slice. -/
theorem clampExt_curry_of_le {u₀ : ℝ≥0} (H : C(ℝ≥0 × ℝ≥0, ℝ))
    {u : ℝ≥0} (hu : u ≤ u₀) :
    (clampExt u₀ H).curry u = H.curry u := by
  ext r; simp [clampExt_apply, min_eq_left hu]

/-- Every slice of the time-clamped field belongs to the decaying slice class. -/
theorem isSlice_clampExt {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution u₀ H)
    (v : ℝ≥0) : IsSlice ((clampExt u₀ H).curry v) := by
  have : (clampExt u₀ H).curry v = H.curry (min v u₀) := by ext r; rfl
  rw [this]; exact hH.isSlice _ (min_le_right _ _)

/-- Time clamping preserves the classical solution on its closed strip. -/
theorem isClassicalSolution_clampExt {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) : IsClassicalSolution u₀ (clampExt u₀ H) := by
  obtain ⟨h1, ⟨C, hC⟩, h3⟩ := hH
  refine ⟨?_, ⟨C, fun u hu r => ?_⟩, ?_⟩
  · apply h1.congr
    intro p hp
    have : (Real.toNNReal p.1) ≤ u₀ := Real.toNNReal_le_iff_le_coe.2 hp.1.2
    simp [clampExt_apply, min_eq_left this]
  · rw [clampExt_apply, min_eq_left hu]; exact hC u hu r
  · intro u hu huT hs r hr
    have hcur := clampExt_curry_of_le H huT.le
    have hs' : IsSlice (H.curry u) := hcur ▸ hs
    have hev : (fun v : ℝ => clampExt u₀ H (Real.toNNReal v, r)) =ᶠ[𝓝 (u : ℝ)]
        (fun v : ℝ => H (Real.toNNReal v, r)) := by
      filter_upwards [Iio_mem_nhds (show (u : ℝ) < u₀ from huT)] with v hv
      have : Real.toNNReal v ≤ u₀ := Real.toNNReal_le_iff_le_coe.2 hv.le
      simp [clampExt_apply, min_eq_left this]
    have hsl : (fun s : ℝ => clampExt u₀ H (u, Real.toNNReal s)) =
        (fun s : ℝ => H (u, Real.toNNReal s)) := by
      funext s; simp [clampExt_apply, min_eq_left huT.le]
    rw [hev.deriv_eq, hsl]
    have key := h3 u hu huT hs' r hr
    have e1 : gBar ((clampExt u₀ H).curry u) hs r = gBar (H.curry u) hs' r := by
      simp only [hcur]
    have e2 : g ((clampExt u₀ H).curry u) hs r = g (H.curry u) hs' r := by
      simp only [hcur]
    rw [e1, e2, key, hcur, clampExt_apply, min_eq_left huT.le]

/-- Bondi's theorem for a strip solution, using time clamping to supply every slice. -/
theorem antitoneOn_bondiMass_clamped {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) {C : ℝ}
    (hd : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ)) :
    AntitoneOn (fun u : ℝ≥0 => bondiMass (H.curry (min u u₀))
      (hH.isSlice (min u u₀) (min_le_right _ _))) (Icc 0 u₀) := by
  have hd' : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |radialDerivative (clampExt u₀ H) u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ) := by
    intro u hu r
    have : radialDerivative (clampExt u₀ H) u r = radialDerivative H u r := by
      unfold radialDerivative
      congr 1; funext z; simp [clampExt_apply, min_eq_left hu]
    rw [this]; exact hd u hu r
  have hA := antitoneOn_bondiMass (isClassicalSolution_clampExt hH)
    (isSlice_clampExt hH) hd'
  intro a ha b hb hab
  have e : ∀ u ∈ Icc 0 u₀, bondiMass ((clampExt u₀ H).curry u) (isSlice_clampExt hH u) =
      bondiMass (H.curry (min u u₀)) (hH.isSlice (min u u₀) (min_le_right _ _)) := by
    intro u hu
    have h1 := clampExt_curry_of_le H hu.2
    simp only [min_eq_left hu.2, h1]
  have := hA ha hb hab
  dsimp only at this ⊢
  rw [← e a ha, ← e b hb]; exact this

end XBT

end Christodoulou.Bondi
