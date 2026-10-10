module
public import Christodoulou.Frozen.Bondi.Characteristic
public import Christodoulou.Frozen.Bondi.LinearCoeff
import Christodoulou.Frozen.Bondi.GBarXPos
import Christodoulou.Frozen.Bondi.GBarXLeOne
import Christodoulou.Frozen.Bondi.LipschitzWithGBarX
import Christodoulou.Frozen.Bondi.HasDerivWithinAtGBarX
import Christodoulou.Frozen.Bondi.DerivGBarXNonneg
import Christodoulou.Frozen.Bondi.ContinuousDerivGBarX
import Christodoulou.Frozen.Bondi.IsCharacteristicEqOn
import Christodoulou.Frozen.Bondi.IsCharacteristicMemIcc
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic
import Christodoulou.Frozen.Bondi.IsCharacteristicRestrict
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.HeineCantor



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi
namespace XDep

open Filter Topology

private theorem sharp_lipschitz {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (t : ℝ) :
    LipschitzWith (Real.toNNReal (π / 12 * x ^ 2)) (charField hH t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hK : 0 ≤ π / 6 * x ^ 2 := by positivity
  have hK' : 0 ≤ π / 12 * x ^ 2 := by positivity
  calc
    dist (charField hH t z) (charField hH t w) =
        (1 / 2 : ℝ) * dist (gBarX hH t.toNNReal z.toNNReal)
          (gBarX hH t.toNNReal w.toNNReal) := by
      simp only [charField, Real.dist_eq, ← mul_sub, abs_mul]
      norm_num
    _ ≤ 1 / 2 * ((Real.toNNReal (π / 6 * x ^ 2) : ℝ) * dist z w) :=
      mul_le_mul_of_nonneg_left ((lipschitzWith_gBarX hH t.toNNReal).dist_le_mul z w)
        (by norm_num)
    _ = _ := by rw [Real.coe_toNNReal _ hK, Real.coe_toNNReal _ hK']; ring

private theorem backward_dist {T K : ℝ} {f g : ℝ → ℝ} {v : ℝ → ℝ → ℝ}
    (hK : 0 ≤ K) (hv : ∀ s, LipschitzWith (Real.toNNReal K) (v s))
    (hf : ∀ s ∈ Icc 0 T, HasDerivWithinAt f (v s (f s)) (Icc 0 T) s)
    (hg : ∀ s ∈ Icc 0 T, HasDerivWithinAt g (v s (g s)) (Icc 0 T) s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (f t) (g t) ≤ exp (K * (T - t)) * dist (f T) (g T) := by
  have hm : MapsTo Neg.neg (Icc (-T) 0) (Icc 0 T) := by
    intro s hs; constructor <;> linarith [hs.1, hs.2]
  have hd {f : ℝ → ℝ}
      (hf : ∀ s ∈ Icc 0 T, HasDerivWithinAt f (v s (f s)) (Icc 0 T) s)
      (s : ℝ) (hs : s ∈ Ico (-T) 0) :
      HasDerivWithinAt (fun q => f (-q)) (-v (-s) (f (-s))) (Ici s) s := by
    have h := (hf (-s) (hm ⟨hs.1, hs.2.le⟩)).comp s
      (hasDerivAt_neg s).hasDerivWithinAt hm
    have h' : HasDerivWithinAt (fun q => f (-q)) (-v (-s) (f (-s)))
        (Icc (-T) 0) s := by convert! h using 1; simp
    exact h'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
  have hh := dist_le_of_trajectories_ODE
    (v := fun s z => -v (-s) z) (a := -T) (b := 0)
    (fun s => (hv (-s)).neg)
    ((HasDerivWithinAt.continuousOn hf).comp continuous_neg.continuousOn hm) (hd hf)
    ((HasDerivWithinAt.continuousOn hg).comp continuous_neg.continuousOn hm) (hd hg)
    (δ := dist (f T) (g T)) (by simp) (-t) (by constructor <;> linarith [ht.1, ht.2])
  simpa only [Function.comp_apply, neg_neg, Real.coe_toNNReal _ hK, neg_sub_neg, mul_comm] using hh

private theorem monotone_gBar {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : ℝ≥0) :
    MonotoneOn (fun z : ℝ => gBarX hH u z.toNNReal) (Ici 0) := by
  have hd : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt
      (fun z : ℝ => gBarX hH u z.toNNReal) (derivGBarX hH u z.toNNReal) (Ici 0) z := by
    intro z hz
    simpa only [Real.coe_toNNReal _ hz] using hasDerivWithinAt_gBarX hH u z.toNNReal
  exact monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (HasDerivWithinAt.continuousOn hd)
    (fun z hz => (hd z (interior_subset hz)).mono interior_subset)
    (fun z _ => derivGBarX_nonneg hH u z.toNNReal)

private theorem char_order {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r r' : ℝ≥0} {f g : ℝ → ℝ}
    (hf : IsCharacteristic hH u₁ r f) (hg : IsCharacteristic hH u₁ r' g)
    (hr : r ≤ r') : ∀ t ∈ Icc 0 (u₁ : ℝ), f t ≤ g t := by
  rcases eq_or_lt_of_le hr with he | he
  · subst r'; intro t ht; exact (hf.eqOn hg ht).le
  intro t ht
  by_contra hn
  have hn' : g t - f t < 0 := by linarith
  have hend : 0 < g u₁ - f u₁ := by rw [hf.1, hg.1]; exact sub_pos.mpr he
  have hc := (HasDerivWithinAt.continuousOn hg.2).sub
    (HasDerivWithinAt.continuousOn hf.2)
  obtain ⟨s, hs, hzero⟩ := intermediate_value_Icc ht.2
    (hc.mono (Icc_subset_Icc_left ht.1)) ⟨hn'.le, hend.le⟩
  have hs0 : 0 ≤ s := ht.1.trans hs.1
  have heq : f s = g s := by dsimp at hzero; linarith
  have hu := ODE_solution_unique_of_mem_Icc_right (v := charField hH)
    (s := fun _ => univ) (a := s) (b := (u₁ : ℝ))
    (fun q _ => (sharp_lipschitz hH q).lipschitzOnWith)
    ((HasDerivWithinAt.continuousOn hf.2).mono (Icc_subset_Icc_left hs0))
    (fun q hq => (hf.2 q ⟨hs0.trans hq.1, hq.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨hs0.trans hq.1, hq.2⟩))
    (fun _ _ => mem_univ _)
    ((HasDerivWithinAt.continuousOn hg.2).mono (Icc_subset_Icc_left hs0))
    (fun q hq => (hg.2 q ⟨hs0.trans hq.1, hq.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨hs0.trans hq.1, hq.2⟩))
    (fun _ _ => mem_univ _) heq
  have hh := hu ⟨hs.2, le_rfl⟩
  rw [hf.1, hg.1] at hh
  exact (ne_of_lt he) (NNReal.coe_injective hh)

private theorem char_difference {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r r' : ℝ≥0} {f g : ℝ → ℝ}
    (hf : IsCharacteristic hH u₁ r f) (hg : IsCharacteristic hH u₁ r' g)
    (hr : r ≤ r') {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    g t - f t ∈ Icc ((r' : ℝ) - r)
      (exp (π / 12 * x ^ 2 * ((u₁ : ℝ) - t)) * ((r' : ℝ) - r)) := by
  have ho := char_order hf hg hr
  have ha : AntitoneOn (fun s => g s - f s) (Icc 0 (u₁ : ℝ)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      ((HasDerivWithinAt.continuousOn hg.2).sub (HasDerivWithinAt.continuousOn hf.2))
      (fun s hs => ((hg.2 s (interior_subset hs)).sub
        (hf.2 s (interior_subset hs))).mono interior_subset) ?_
    intro s hs
    have hss := interior_subset hs
    have hfn : 0 ≤ f s := r.coe_nonneg.trans (hf.mem_Icc hss).1
    have hgn : 0 ≤ g s := r'.coe_nonneg.trans (hg.mem_Icc hss).1
    have hh := monotone_gBar hH s.toNNReal hfn hgn (ho s hss)
    dsimp only [charField]
    linarith only [hh]
  constructor
  · have hh := ha ht ⟨u₁.2.1, le_rfl⟩ ht.2
    simpa only [hf.1, hg.1] using hh
  · have hh := backward_dist (by positivity) (sharp_lipschitz hH) hf.2 hg.2 ht
    rw [hf.1, hg.1] at hh
    have hr' : (r : ℝ) ≤ r' := hr
    simpa only [Real.dist_eq, abs_sub_comm (f t) (g t), abs_of_nonneg (sub_nonneg.mpr (ho t ht)),
      abs_sub_comm (r : ℝ) (r' : ℝ), abs_of_nonneg (sub_nonneg.mpr hr')] using hh

/-- Order and exponential expansion in the terminal radius on `[0, u₁]`. -/
theorem characteristic_sub_mem_Icc {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) {r₁ r₁' : ℝ≥0} (hr : r₁ ≤ r₁')
    {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    characteristic hH u₁ r₁' t - characteristic hH u₁ r₁ t ∈
      Icc ((r₁' : ℝ) - r₁) (exp (π / 12 * x ^ 2 * ((u₁ : ℝ) - t)) * ((r₁' : ℝ) - r₁)) := by
  exact char_difference (isCharacteristic_characteristic hH u₁ r₁)
    (isCharacteristic_characteristic hH u₁ r₁') hr ht

/-- Dependence on the terminal time, via restriction to the earlier terminal point. -/
theorem characteristic_sub_mem_Icc_of_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) {u₁ u₁' : Icc (0 : ℝ) u₀} (hu : (u₁ : ℝ) ≤ u₁') (r₁ : ℝ≥0)
    {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    characteristic hH u₁' r₁ t - characteristic hH u₁ r₁ t ∈
      Icc 0 (exp (π / 12 * x ^ 2 * ((u₁ : ℝ) - t)) * (((u₁' : ℝ) - u₁) / 2)) := by
  let χ' := characteristic hH u₁' r₁
  have hχ' := isCharacteristic_characteristic hH u₁' r₁
  have huu : (u₁ : ℝ) ∈ Icc 0 (u₁' : ℝ) := ⟨u₁.2.1, hu⟩
  have hb := hχ'.mem_Icc huu
  have hn : 0 ≤ χ' u₁ := r₁.coe_nonneg.trans hb.1
  have hrr : r₁ ≤ (χ' u₁).toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hn]; exact hb.1
  have hh := char_difference (isCharacteristic_characteristic hH u₁ r₁)
    (hχ'.restrict huu) hrr ht
  rw [Real.coe_toNNReal _ hn] at hh
  exact ⟨(sub_nonneg.mpr hb.1).trans hh.1,
    hh.2.trans (mul_le_mul_of_nonneg_left (by linarith only [hb.2]) (exp_pos _).le)⟩

private theorem char_clamp {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : Icc (0 : ℝ) u₀) (r : ℝ≥0) (t : ℝ) :
    characteristic hH u r t = characteristic hH u r (max 0 (min (u : ℝ) t)) := by
  change characteristicOn hH u r (projIcc 0 (u : ℝ) u.2.1 t) =
    characteristicOn hH u r (projIcc 0 (u : ℝ) u.2.1 ((projIcc 0 (u : ℝ) u.2.1 t : ℝ)))
  rw [projIcc_val]

private theorem lipschitz_time {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : Icc (0 : ℝ) u₀) (r : ℝ≥0) :
    LipschitzWith (1 / 2) (characteristic hH u r) := by
  have hχ := isCharacteristic_characteristic hH u r
  have hl : LipschitzOnWith (1 / 2) (characteristic hH u r) (Icc 0 (u : ℝ)) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc _ _) hχ.2
    intro t _
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, Real.norm_eq_abs,
      charField, abs_mul]
    have hp := (gBarX_pos hH t.toNNReal (characteristic hH u r t).toNNReal).le
    rw [abs_of_nonneg hp]
    norm_num
    linarith only [gBarX_le_one hH t.toNNReal (characteristic hH u r t).toNNReal]
  have hh : LipschitzWith (1 / 2) (fun s : Icc 0 (u : ℝ) => characteristic hH u r s) := by
    apply LipschitzWith.of_dist_le_mul
    intro s q; exact hl.dist_le_mul s s.2 q q.2
  have h := hh.comp (LipschitzWith.projIcc u.2.1)
  simp only [mul_one] at h
  convert h using 1
  ext t
  exact char_clamp hH u r t

private theorem exp_le_global {u₀ : ℝ≥0} {x : ℝ} {u : Icc (0 : ℝ) u₀} {t : ℝ}
    (ht : t ∈ Icc 0 (u : ℝ)) :
    exp (π / 12 * x ^ 2 * ((u : ℝ) - t)) ≤ exp (π / 12 * x ^ 2 * (u₀ : ℝ)) := by
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by linarith [u.2.2, ht.1]) (by positivity)

/-- Unordered Lipschitz bound of the characteristics in the terminal radius, for every real
time `t` (including the constant extension). -/
theorem lipschitzWith_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) (t : ℝ) :
    LipschitzWith (Real.toNNReal (exp (π / 12 * x ^ 2 * (u₀ : ℝ))))
      (fun r₁ : ℝ≥0 => characteristic hH u₁ r₁ t) := by
  apply LipschitzWith.of_dist_le_mul
  intro r r'
  let s := max 0 (min (u₁ : ℝ) t)
  have hs : s ∈ Icc 0 (u₁ : ℝ) := (projIcc 0 (u₁ : ℝ) u₁.2.1 t).2
  rw [char_clamp hH u₁ r t, char_clamp hH u₁ r' t]
  have hh := backward_dist (by positivity) (sharp_lipschitz hH)
    (isCharacteristic_characteristic hH u₁ r).2 (isCharacteristic_characteristic hH u₁ r').2 hs
  rw [(isCharacteristic_characteristic hH u₁ r).1,
    (isCharacteristic_characteristic hH u₁ r').1] at hh
  calc
    _ ≤ exp (π / 12 * x ^ 2 * ((u₁ : ℝ) - s)) * dist (r : ℝ) (r' : ℝ) := hh
    _ ≤ _ := by
      rw [Real.coe_toNNReal _ (exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (exp_le_global hs) dist_nonneg

private theorem terminal_dist_of_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) {u u' : Icc (0 : ℝ) u₀} (hu : (u : ℝ) ≤ u') (r : ℝ≥0)
    (t : ℝ) : dist (characteristic hH u' r t) (characteristic hH u r t) ≤
      exp (π / 12 * x ^ 2 * (u₀ : ℝ)) * dist u' u := by
  let s := max 0 (min (u : ℝ) t)
  let s' := max 0 (min (u' : ℝ) t)
  let E := exp (π / 12 * x ^ 2 * (u₀ : ℝ))
  have hE : 1 ≤ E := one_le_exp_iff.mpr (by positivity)
  have hs : s ∈ Icc 0 (u : ℝ) := (projIcc 0 (u : ℝ) u.2.1 t).2
  have hh := characteristic_sub_mem_Icc_of_le hH hu r hs
  have hh' : dist (characteristic hH u' r s) (characteristic hH u r s) ≤
      E * ((u' : ℝ) - u) / 2 := by
    rw [Real.dist_eq, abs_of_nonneg hh.1]
    exact hh.2.trans (by
      have := mul_le_mul_of_nonneg_right (exp_le_global (x := x) hs)
        (by linarith : 0 ≤ ((u' : ℝ) - u) / 2)
      simpa only [mul_div_assoc] using this)
  have hp : dist s' s ≤ dist (u' : ℝ) (u : ℝ) := by
    have := ((LipschitzWith.id.min_const t).const_max 0).dist_le_mul (u' : ℝ) (u : ℝ)
    simpa only [id_eq, NNReal.coe_one, one_mul] using this
  rw [char_clamp hH u' r t, char_clamp hH u r t]
  calc
    _ ≤ dist (characteristic hH u' r s') (characteristic hH u' r s) +
        dist (characteristic hH u' r s) (characteristic hH u r s) := dist_triangle _ _ _
    _ ≤ 1 / 2 * dist (u' : ℝ) (u : ℝ) + E * ((u' : ℝ) - u) / 2 := by
      apply add_le_add _ hh'
      exact ((lipschitz_time hH u' r).dist_le_mul s' s).trans
        (mul_le_mul_of_nonneg_left hp (by norm_num))
    _ ≤ _ := by
      simp only [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu)]
      nlinarith only [hE, sub_nonneg.mpr hu]

private theorem lipschitz_terminal {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (r : ℝ≥0) (t : ℝ) :
    LipschitzWith (Real.toNNReal (exp (π / 12 * x ^ 2 * (u₀ : ℝ))))
      (fun u : Icc (0 : ℝ) u₀ => characteristic hH u r t) := by
  apply LipschitzWith.of_dist_le_mul
  intro u u'
  rw [Real.coe_toNNReal _ (exp_pos _).le]
  rcases le_total (u : ℝ) (u' : ℝ) with hu | hu
  · simpa only [dist_comm] using terminal_dist_of_le hH hu r t
  · exact terminal_dist_of_le hH hu r t

/-- Joint continuity in time, terminal time, and terminal radius,
including the constant extension. -/
theorem continuous_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ × Icc (0 : ℝ) u₀ × ℝ≥0 => characteristic hH p.2.1 p.2.2 p.1) := by
  have hp (t : ℝ) : Continuous
      (fun p : Icc (0 : ℝ) u₀ × ℝ≥0 => characteristic hH p.1 p.2 t) := by
    apply continuous_prod_of_continuous_lipschitzWith _
      (Real.toNNReal (exp (π / 12 * x ^ 2 * (u₀ : ℝ))))
    · intro u; exact (lipschitzWith_characteristic hH u t).continuous
    · intro r; exact lipschitz_terminal hH r t
  exact continuous_prod_of_continuous_lipschitzWith _ (1 / 2)
    (fun t => hp t) (fun p => lipschitz_time hH p.1 p.2)

private theorem gbar_sub_average {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : ℝ≥0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    gBarX hH u b.toNNReal - gBarX hH u a.toNNReal =
      (b - a) * ∫ θ in (0 : ℝ)..1,
        derivGBarX hH u (Real.toNNReal (a + θ * (b - a))) := by
  let z := fun θ : ℝ => a + θ * (b - a)
  have hm : MapsTo z (Icc 0 1) (Ici 0) := by
    intro θ hθ
    change 0 ≤ a + θ * (b - a)
    nlinarith only [mul_nonneg ha (sub_nonneg.mpr hθ.2), mul_nonneg hb hθ.1]
  have hc : Continuous (fun θ : ℝ => derivGBarX hH u (z θ).toNNReal) := by
    exact (continuous_derivGBarX hH).comp (continuous_const.prodMk
      (continuous_real_toNNReal.comp (by dsimp [z]; fun_prop)))
  have hd : ∀ θ ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun θ : ℝ => gBarX hH u (z θ).toNNReal)
        (derivGBarX hH u (z θ).toNNReal * (b - a)) (Icc 0 1) θ := by
    intro θ hθ
    have ho : HasDerivWithinAt (fun q : ℝ => gBarX hH u q.toNNReal)
        (derivGBarX hH u (z θ).toNNReal) (Ici 0) (z θ) := by
      simpa only [Real.coe_toNNReal _ (hm hθ)] using
        hasDerivWithinAt_gBarX hH u (z θ).toNNReal
    have hz : HasDerivAt z (b - a) θ := by
      convert ((hasDerivAt_id θ).mul_const (b - a)).const_add a using 1 <;> simp [z]
    convert ho.comp θ hz.hasDerivWithinAt hm using 1; rfl
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1)
    (HasDerivWithinAt.continuousOn hd)
    (fun θ hθ => (hd θ ⟨hθ.1.le, hθ.2.le⟩).hasDerivAt (Icc_mem_nhds hθ.1 hθ.2))
    ((hc.mul continuous_const).intervalIntegrable 0 1)
  simp only [z, one_mul, add_sub_cancel, zero_mul, add_zero,
    intervalIntegral.integral_mul_const] at hi
  exact hi.symm.trans (mul_comm _ _)

/-- The averaged coefficient `α(s) = ½ ∫₀¹ ∂_r ḡ(s, χ_r(s) + θ (χ_q(s) − χ_r(s))) dθ` between the
characteristics through `(u₁, r)` and `(u₁, q)`. -/
@[expose] noncomputable def avgCoeff {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) (r q : ℝ≥0) (s : ℝ) : ℝ :=
  1 / 2 * ∫ θ in (0 : ℝ)..1,
    derivGBarX hH s.toNNReal (Real.toNNReal (characteristic hH u₁ r s +
      θ * (characteristic hH u₁ q s - characteristic hH u₁ r s)))

/-- Joint continuity of the averaged coefficient in the second terminal radius and the time;
with `XDep.avgCoeff_self` this gives `α_δ → a` uniformly on compacts. -/
theorem continuous_avgCoeff {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) (r : ℝ≥0) :
    Continuous (fun p : ℝ≥0 × ℝ => XDep.avgCoeff hH u₁ r p.1 p.2) := by
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hf : Continuous (fun p : (ℝ≥0 × ℝ) × ℝ => characteristic hH u₁ r p.1.2) :=
    (lipschitz_time hH u₁ r).continuous.comp (continuous_snd.comp continuous_fst)
  have hg : Continuous (fun p : (ℝ≥0 × ℝ) × ℝ => characteristic hH u₁ p.1.1 p.1.2) :=
    (continuous_characteristic hH).comp
      ((continuous_snd.comp continuous_fst).prodMk
        (continuous_const.prodMk (continuous_fst.comp continuous_fst)))
  exact (continuous_derivGBarX hH).comp
    ((continuous_real_toNNReal.comp (continuous_snd.comp continuous_fst)).prodMk
      (continuous_real_toNNReal.comp (hf.add (continuous_snd.mul (hg.sub hf)))))

private theorem difference_ode {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : Icc (0 : ℝ) u₀) (r q : ℝ≥0) :
    ∀ s ∈ Icc 0 (u : ℝ), HasDerivWithinAt
      (fun s => characteristic hH u q s - characteristic hH u r s)
      (-avgCoeff hH u r q s * (characteristic hH u q s - characteristic hH u r s))
      (Icc 0 (u : ℝ)) s := by
  intro s hs
  have hf := isCharacteristic_characteristic hH u r
  have hg := isCharacteristic_characteristic hH u q
  have hh := gbar_sub_average hH s.toNNReal
    (r.coe_nonneg.trans (hf.mem_Icc hs).1) (q.coe_nonneg.trans (hg.mem_Icc hs).1)
  convert (hg.2 s hs).sub (hf.2 s hs) using 1
  dsimp only [charField, avgCoeff]
  linear_combination 1 / 2 * hh

private theorem terminal_linear_formula {T : ℝ} {c Y : ℝ → ℝ}
    (hc : Continuous c)
    (hd : ∀ s ∈ Icc 0 T, HasDerivWithinAt Y (-c s * Y s) (Icc 0 T) s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Y t = Y T * exp (∫ s in t..T, c s) := by
  let A := fun t => ∫ s in t..T, c s
  have hA (s : ℝ) : HasDerivAt A (-c s) s :=
    intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable s T)
      (hc.stronglyMeasurableAtFilter volume (𝓝 s)) hc.continuousAt
  have hh : ∀ s ∈ Icc 0 T,
      HasDerivWithinAt (fun s => Y s * exp (-A s)) 0 (Icc 0 T) s := by
    intro s hs
    convert (hd s hs).mul ((hA s).neg.exp.hasDerivWithinAt) using 1; ring
  have hconst := constant_of_has_deriv_right_zero (HasDerivWithinAt.continuousOn hh)
    (fun s hs => (hh s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs))
  have he := (hconst t ht).trans (hconst T ⟨ht.1.trans ht.2, le_rfl⟩).symm
  have he' : Y t * exp (-A t) = Y T := by simpa [A] using he
  calc
    Y t = (Y t * exp (-A t)) * exp (A t) := by
      rw [mul_assoc, ← exp_add]; simp only [neg_add_cancel, exp_zero, mul_one]
    _ = Y T * exp (A t) := by rw [he']

/-- The exact difference formula: `χ_q(t) − χ_r(t) = (q − r) e^{∫_t^{u₁} α}` on `[0, u₁]`. -/
theorem characteristic_sub_eq {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) (r q : ℝ≥0)
    {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    characteristic hH u₁ q t - characteristic hH u₁ r t =
      ((q : ℝ) - r) * exp (∫ s in t..(u₁ : ℝ), XDep.avgCoeff hH u₁ r q s) := by
  have hc : Continuous (avgCoeff hH u₁ r q) :=
    (continuous_avgCoeff hH u₁ r).comp (continuous_const.prodMk continuous_id)
  have hh := terminal_linear_formula hc (difference_ode hH u₁ r q) ht
  simpa only [(isCharacteristic_characteristic hH u₁ q).1,
    (isCharacteristic_characteristic hH u₁ r).1] using hh

/-- At equal terminal radii, the averaged coefficient is the linear coefficient. -/
theorem avgCoeff_self {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) (r : ℝ≥0) (s : ℝ) :
    XDep.avgCoeff hH u₁ r r s =
      linearCoeff hH (Real.toNNReal s) (Real.toNNReal (characteristic hH u₁ r s)) := by
  simp [avgCoeff, linearCoeff]

/-- The terminal radial derivative on `[0, u₁]`, taken within `[0, ∞)` at the centre. -/
theorem hasDerivWithinAt_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) (r₁ : ℝ≥0) {t : ℝ}
    (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    HasDerivWithinAt (fun ρ : ℝ => characteristic hH u₁ (Real.toNNReal ρ) t)
      (exp (∫ s in t..(u₁ : ℝ),
        linearCoeff hH (Real.toNNReal s) (Real.toNNReal (characteristic hH u₁ r₁ s))))
      (Ici 0) (r₁ : ℝ) := by
  let A := fun ρ : ℝ => ∫ s in t..(u₁ : ℝ), avgCoeff hH u₁ r₁ ρ.toNNReal s
  have hAc : Continuous A := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (continuous_avgCoeff hH u₁ r₁).comp
      ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
  have hAself : A (r₁ : ℝ) = ∫ s in t..(u₁ : ℝ),
      linearCoeff hH s.toNNReal (characteristic hH u₁ r₁ s).toNNReal := by
    simp only [A, Real.toNNReal_coe, avgCoeff_self]
  rw [← hAself]
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have hlim : Tendsto (fun ρ => exp (A ρ)) (𝓝[Ici (0 : ℝ) \ {(r₁ : ℝ)}] (r₁ : ℝ))
      (𝓝 (exp (A (r₁ : ℝ)))) :=
    (Real.continuous_exp.comp hAc).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ici (0 : ℝ) \ {(r₁ : ℝ)}))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  have hρ0 : 0 ≤ ρ := hρ.1
  have hρne : ρ ≠ (r₁ : ℝ) := hρ.2
  rw [slope_def_field]
  have hh := characteristic_sub_eq hH u₁ r₁ ρ.toNNReal ht
  rw [Real.coe_toNNReal _ hρ0] at hh
  rw [Real.toNNReal_coe, hh]
  dsimp only [A]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr hρne)).symm

/-- Joint continuity of the explicit variational factor on the whole product.
It equals the terminal radial derivative only for `0 ≤ t ≤ u₁`. -/
theorem continuous_exp_integral_linearCoeff {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) :
    Continuous (fun p : ℝ × Icc (0 : ℝ) u₀ × ℝ≥0 =>
      exp (∫ s in p.1..(p.2.1 : ℝ),
        linearCoeff hH (Real.toNNReal s) (Real.toNNReal (characteristic hH p.2.1 p.2.2 s)))) := by
  set F : (ℝ × Icc (0 : ℝ) u₀ × ℝ≥0) → ℝ → ℝ := fun p s =>
    linearCoeff hH (Real.toNNReal s) (Real.toNNReal (characteristic hH p.2.1 p.2.2 s)) with hFdef
  have hc := continuous_characteristic hH
  have hF : Continuous F.uncurry := by
    have hχ : Continuous (fun q : (ℝ × Icc (0 : ℝ) u₀ × ℝ≥0) × ℝ =>
        characteristic hH q.1.2.1 q.1.2.2 q.2) :=
      hc.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
    have hd := continuous_derivGBarX hH
    have : Continuous (fun q : (ℝ × Icc (0 : ℝ) u₀ × ℝ≥0) × ℝ =>
        1 / 2 * derivGBarX hH (Real.toNNReal q.2)
          (Real.toNNReal (characteristic hH q.1.2.1 q.1.2.2 q.2))) :=
      continuous_const.mul (hd.comp ((continuous_real_toNNReal.comp continuous_snd).prodMk
        (continuous_real_toNNReal.comp hχ)))
    exact this
  have h1 : Continuous (fun p : ℝ × Icc (0 : ℝ) u₀ × ℝ≥0 =>
      ∫ s in (0 : ℝ)..(p.2.1 : ℝ), F p s) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have h2 : Continuous (fun p : ℝ × Icc (0 : ℝ) u₀ × ℝ≥0 => ∫ s in (0 : ℝ)..p.1, F p s) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF continuous_fst
  have hEq : (fun p : ℝ × Icc (0 : ℝ) u₀ × ℝ≥0 => ∫ s in p.1..(p.2.1 : ℝ), F p s) =
      fun p => (∫ s in (0 : ℝ)..(p.2.1 : ℝ), F p s) - ∫ s in (0 : ℝ)..p.1, F p s := by
    funext p
    have hFp : Continuous (F p) := hF.comp (Continuous.prodMk_right p)
    rw [intervalIntegral.integral_interval_sub_left (hFp.intervalIntegrable _ _)
      (hFp.intervalIntegrable _ _)]
  exact Real.continuous_exp.comp (hEq ▸ h1.sub h2)

/-- Uniform continuity of `∂_r ḡ` on compact sets of the quadrant. -/
theorem uniformContinuousOn_derivGBarX {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    {K : Set (ℝ≥0 × ℝ≥0)} (hK : IsCompact K) :
    UniformContinuousOn (fun p : ℝ≥0 × ℝ≥0 => derivGBarX hH p.1 p.2) K :=
  hK.uniformContinuousOn_of_continuous (continuous_derivGBarX hH).continuousOn

/-- Uniform convergence of the averaged coefficient to `a = ½ ∂_r ḡ` along the characteristic
through `(u₁, r)`, as the second terminal radius `q → r` (proposal §4; `α_δ → a`). -/
theorem tendstoUniformlyOn_avgCoeff {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) (r : ℝ≥0) :
    TendstoUniformlyOn (fun q : ℝ≥0 => fun s : ℝ => XDep.avgCoeff hH u₁ r q s)
      (fun s : ℝ =>
        linearCoeff hH (Real.toNNReal s) (Real.toNNReal (characteristic hH u₁ r s)))
      (nhds r) (Icc 0 (u₁ : ℝ)) := by
  have hc : UniformContinuousOn
      (fun p : ℝ≥0 × ℝ => XDep.avgCoeff hH u₁ r p.1 p.2)
      (Metric.closedBall r 1 ×ˢ Icc 0 (u₁ : ℝ)) :=
    ((isCompact_closedBall r 1).prod isCompact_Icc).uniformContinuousOn_of_continuous
      (XDep.continuous_avgCoeff hH u₁ r).continuousOn
  have hr : Metric.closedBall r 1 ∈ nhds r :=
    Metric.closedBall_mem_nhds r (by norm_num)
  simpa only [nhdsWithin_eq_nhds.mpr hr, XDep.avgCoeff_self] using
    (hc.tendstoUniformlyOn (F := fun q s => XDep.avgCoeff hH u₁ r q s)
      (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1)))

end XDep
end Christodoulou.Bondi
