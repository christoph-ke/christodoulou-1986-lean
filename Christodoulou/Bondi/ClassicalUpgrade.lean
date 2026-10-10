module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.GBarX
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Christodoulou.Frozen.Bondi.IsCharacteristicMemIcc
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic
import Christodoulou.Frozen.Bondi.ContinuousGBarX
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Classical regularity from characteristic derivatives

A continuous field with continuous radial and characteristic derivatives has a continuous
time derivative and is jointly `C¹` on the closed strip. The proof compares nearby time slices
along a backward characteristic and a radial segment, then combines the coordinate derivatives
in a rectangle estimate that includes the sides and corners.
-/

public section

open Set MeasureTheory Filter Topology Real Asymptotics
open scoped NNReal ContDiff

namespace Christodoulou.Bondi.XCl

/-- Scalar first-order remainder on a closed interval, including a degenerate interval. -/
private theorem remainder_bound {f d : ℝ → ℝ} {a b c ε : ℝ}
    (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt f (d t) (Icc a b) t)
    (he : ∀ t ∈ Icc a b, |d t - c| ≤ ε) :
    |f b - f a - c * (b - a)| ≤ ε * (b - a) := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => f t - c * t) (f' := fun t => d t - c)
    (fun t ht => (hd t ht).sub (by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul c).hasDerivWithinAt))
    (fun t ht => by simpa only [Real.norm_eq_abs] using he t ht)
    (convex_Icc a b) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab),
    show f b - c * b - (f a - c * a) = f b - f a - c * (b - a) by ring] using hh

/-- Local forward increment estimate along the terminal characteristic and the radial segment. -/
private theorem forward_remainder {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H}
    (F : C(ℝ≥0 × ℝ≥0, ℝ)) (Q B : ℝ≥0 → ℝ≥0 → ℝ)
    (hrad : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      HasDerivWithinAt (fun s : ℝ => F (u, s.toNNReal)) (Q u r) (Ici 0) (r : ℝ))
    (hcurve : ∀ (v : Icc (0 : ℝ) u₀) (r : ℝ≥0) (χ : ℝ → ℝ),
      IsCharacteristic hH v r χ → ∀ t ∈ Icc 0 (v : ℝ),
        HasDerivWithinAt (fun s : ℝ => F (s.toNNReal, (χ s).toNNReal))
          (B t.toNNReal (χ t).toNNReal) (Icc 0 (v : ℝ)) t)
    (v : Icc (0 : ℝ) u₀) (r : ℝ≥0) {a b₀ q₀ g₀ ε : ℝ}
    (ha : a ∈ Icc 0 (v : ℝ)) (hε : 0 ≤ ε)
    (heB : ∀ t ∈ Icc a (v : ℝ),
      |B t.toNNReal (characteristic hH v r t).toNNReal - b₀| ≤ ε)
    (heQ : ∀ s ∈ Icc (r : ℝ) (characteristic hH v r a),
      |Q a.toNNReal s.toNNReal - q₀| ≤ ε)
    (heg : ∀ t ∈ Icc a (v : ℝ),
      |gBarX hH t.toNNReal (characteristic hH v r t).toNNReal - g₀| ≤ ε) :
    |F (Real.toNNReal (v : ℝ), r) - F (a.toNNReal, r) -
      (b₀ + g₀ / 2 * q₀) * ((v : ℝ) - a)| ≤
        ε * (2 + |q₀|) * ((v : ℝ) - a) := by
  let χ := characteristic hH v r
  have hχ := isCharacteristic_characteristic hH v r
  have hsub : Icc a (v : ℝ) ⊆ Icc 0 (v : ℝ) := Icc_subset_Icc ha.1 le_rfl
  have hat : a.toNNReal ≤ u₀ := by
    apply (NNReal.coe_le_coe).mp
    rw [Real.coe_toNNReal a ha.1]
    exact ha.2.trans v.2.2
  have hrχ := hχ.mem_Icc ha
  have hR : 0 ≤ χ a := r.coe_nonneg.trans hrχ.1
  have hterminal : χ (v : ℝ) = (r : ℝ) := hχ.1
  have eB := remainder_bound ha.2
    (fun t ht => (hcurve v r χ hχ t (hsub ht)).mono hsub) heB
  rw [hterminal, Real.toNNReal_coe] at eB
  have eQ := remainder_bound hrχ.1
    (c := q₀) (ε := ε)
    (fun s hs => by
      have hs0 : 0 ≤ s := r.coe_nonneg.trans hs.1
      have hh := (hrad a.toNNReal hat s.toNNReal).mono
        (show Icc (r : ℝ) (χ a) ⊆ Ici 0 from fun z hz => r.coe_nonneg.trans hz.1)
      simpa only [Real.coe_toNNReal s hs0] using hh) heQ
  rw [Real.toNNReal_coe] at eQ
  have eg := remainder_bound ha.2
    (f := χ) (d := fun t => charField hH t (χ t)) (c := -(g₀ / 2)) (ε := ε / 2)
    (fun t ht => (hχ.2 t (hsub ht)).mono hsub)
    (fun t ht => by
      dsimp only [charField]
      have hh := heg t ht
      rw [show -(1 / 2) * gBarX hH t.toNNReal (χ t).toNNReal - -(g₀ / 2) =
        -(gBarX hH t.toNNReal (χ t).toNNReal - g₀) / 2 by ring,
        abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right hh (by norm_num))
  rw [hterminal] at eg
  have eg' : |χ a - r - g₀ / 2 * ((v : ℝ) - a)| ≤ ε / 2 * ((v : ℝ) - a) := by
    convert eg using 1
    rw [← abs_neg]; congr 1; ring
  have eq : |q₀ * (χ a - r - g₀ / 2 * ((v : ℝ) - a))| ≤
      |q₀| * (ε / 2 * ((v : ℝ) - a)) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left eg' (abs_nonneg q₀)
  have hid : F (Real.toNNReal (v : ℝ), r) - F (a.toNNReal, r) -
      (b₀ + g₀ / 2 * q₀) * ((v : ℝ) - a) =
      (F (Real.toNNReal (v : ℝ), r) - F (a.toNNReal, (χ a).toNNReal) - b₀ * ((v : ℝ) - a)) +
      (F (a.toNNReal, (χ a).toNNReal) - F (a.toNNReal, r) - q₀ * (χ a - r)) +
      q₀ * (χ a - r - g₀ / 2 * ((v : ℝ) - a)) := by ring
  rw [hid]
  calc
    _ ≤ |F (Real.toNNReal (v : ℝ), r) - F (a.toNNReal, (χ a).toNNReal) - b₀ * ((v : ℝ) - a)| +
        |F (a.toNNReal, (χ a).toNNReal) - F (a.toNNReal, r) - q₀ * (χ a - r)| +
        |q₀ * (χ a - r - g₀ / 2 * ((v : ℝ) - a))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ε * ((v : ℝ) - a) + ε * (χ a - r) +
        |q₀| * (ε / 2 * ((v : ℝ) - a)) := add_le_add (add_le_add eB eQ) eq
    _ ≤ ε * (2 + |q₀|) * ((v : ℝ) - a) := by
      have hdisp : χ a - r ≤ ((v : ℝ) - a) / 2 := by linarith only [hrχ.2]
      have hm := mul_le_mul_of_nonneg_left hdisp hε
      have htime : 0 ≤ (v : ℝ) - a := sub_nonneg.mpr ha.2
      nlinarith only [hm, mul_nonneg hε htime,
        mul_nonneg (abs_nonneg q₀) (mul_nonneg hε htime)]

/-- Every point of the short backward characteristic stays within its time width. -/
private theorem path_close {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {v : Icc (0 : ℝ) u₀} {r : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH v r χ) {a u t : ℝ}
    (ha : 0 ≤ a) (hu : u ∈ Icc a (v : ℝ)) (ht : t ∈ Icc a (v : ℝ)) :
    (t, χ t) ∈ Icc 0 (u₀ : ℝ) ×ˢ Ici 0 ∧
      dist (t, χ t) (u, (r : ℝ)) ≤ (v : ℝ) - a := by
  have ht' : t ∈ Icc 0 (v : ℝ) := ⟨ha.trans ht.1, ht.2⟩
  have hb := hχ.mem_Icc ht'
  refine ⟨⟨⟨ht'.1, ht.2.trans v.2.2⟩, r.coe_nonneg.trans hb.1⟩, ?_⟩
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
  constructor
  · exact abs_le.mpr ⟨by linarith only [hu.2, ht.1], by linarith only [ht.2, hu.1]⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr hb.1)]
    linarith only [hb.2, ht.1, ht.2]

/-- The radial segment on the earlier slice stays within the same time width. -/
private theorem radial_close {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {v : Icc (0 : ℝ) u₀} {r : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH v r χ) {a u s : ℝ}
    (ha : 0 ≤ a) (hu : u ∈ Icc a (v : ℝ)) (hs : s ∈ Icc (r : ℝ) (χ a)) :
    (a, s) ∈ Icc 0 (u₀ : ℝ) ×ˢ Ici 0 ∧
      dist (a, s) (u, (r : ℝ)) ≤ (v : ℝ) - a := by
  have hab : a ≤ (v : ℝ) := hu.1.trans hu.2
  have hb := hχ.mem_Icc ⟨ha, hab⟩
  refine ⟨⟨⟨ha, hab.trans v.2.2⟩, r.coe_nonneg.trans hs.1⟩, ?_⟩
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
  constructor
  · rw [abs_of_nonpos (sub_nonpos.mpr hu.1)]
    linarith only [hu.2]
  · rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
    linarith only [hs.2, hb.2, hab]

/-- Characteristics and the radial derivative determine the time derivative on the strip. -/
private theorem hasDerivWithinAt_time {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (F : C(ℝ≥0 × ℝ≥0, ℝ)) (Q B : ℝ≥0 → ℝ≥0 → ℝ)
    (hQ : ContinuousOn (fun p : ℝ × ℝ => Q p.1.toNNReal p.2.toNNReal)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0))
    (hB : ContinuousOn (fun p : ℝ × ℝ => B p.1.toNNReal p.2.toNNReal)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0))
    (hrad : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      HasDerivWithinAt (fun s : ℝ => F (u, s.toNNReal)) (Q u r) (Ici 0) (r : ℝ))
    (hcurve : ∀ (v : Icc (0 : ℝ) u₀) (r : ℝ≥0) (χ : ℝ → ℝ),
      IsCharacteristic hH v r χ → ∀ t ∈ Icc 0 (v : ℝ),
        HasDerivWithinAt (fun s : ℝ => F (s.toNNReal, (χ s).toNNReal))
          (B t.toNNReal (χ t).toNNReal) (Icc 0 (v : ℝ)) t) :
    ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      HasDerivWithinAt (fun s : ℝ => F (s.toNNReal, r))
        (B u r + gBarX hH u r / 2 * Q u r) (Icc 0 (u₀ : ℝ)) (u : ℝ) := by
  intro u hu r
  have hp : ((u : ℝ), (r : ℝ)) ∈ Icc 0 (u₀ : ℝ) ×ˢ Ici 0 :=
    ⟨⟨u.coe_nonneg, by exact_mod_cast hu⟩, r.coe_nonneg⟩
  have hg : ContinuousOn (fun p : ℝ × ℝ => gBarX hH p.1.toNNReal p.2.toNNReal)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) :=
    ((continuous_gBarX hH).comp
      ((continuous_real_toNNReal.comp continuous_fst).prodMk
        (continuous_real_toNNReal.comp continuous_snd))).continuousOn
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  let ε := c / (2 + |Q u r|)
  have hden : 0 < 2 + |Q u r| := by linarith only [abs_nonneg (Q u r)]
  have he : 0 < ε := div_pos hc hden
  obtain ⟨δB, hδB, heB⟩ := Metric.continuousWithinAt_iff.mp (hB _ hp) ε he
  obtain ⟨δQ, hδQ, heQ⟩ := Metric.continuousWithinAt_iff.mp (hQ _ hp) ε he
  obtain ⟨δg, hδg, heg⟩ := Metric.continuousWithinAt_iff.mp (hg _ hp) ε he
  let δ := min δB (min δQ δg)
  have hδ : 0 < δ := lt_min hδB (lt_min hδQ hδg)
  have hlocal (a : ℝ) (v : Icc (0 : ℝ) u₀) (ha : 0 ≤ a)
      (hau : (u : ℝ) ∈ Icc a (v : ℝ)) (hwidth : (v : ℝ) - a < δ) :
      |F (Real.toNNReal (v : ℝ), r) - F (a.toNNReal, r) -
        (B u r + gBarX hH u r / 2 * Q u r) * ((v : ℝ) - a)| ≤
        c * ((v : ℝ) - a) := by
    have hχ := isCharacteristic_characteristic hH v r
    have hpath (t : ℝ) (ht : t ∈ Icc a (v : ℝ)) := path_close hχ ha hau ht
    have hradial (s : ℝ) (hs : s ∈ Icc (r : ℝ) (characteristic hH v r a)) :=
      radial_close hχ ha hau hs
    have hB' (t : ℝ) (ht : t ∈ Icc a (v : ℝ)) :
        |B t.toNNReal (characteristic hH v r t).toNNReal - B u r| ≤ ε := by
      have hh := heB (hpath t ht).1 ((hpath t ht).2.trans_lt
        (hwidth.trans_le (min_le_left δB (min δQ δg))))
      simpa only [Real.dist_eq, Real.toNNReal_coe] using hh.le
    have hQ' (s : ℝ) (hs : s ∈ Icc (r : ℝ) (characteristic hH v r a)) :
        |Q a.toNNReal s.toNNReal - Q u r| ≤ ε := by
      have hh := heQ (hradial s hs).1 ((hradial s hs).2.trans_lt
        (hwidth.trans_le ((min_le_right δB (min δQ δg)).trans (min_le_left δQ δg))))
      simpa only [Real.dist_eq, Real.toNNReal_coe] using hh.le
    have hg' (t : ℝ) (ht : t ∈ Icc a (v : ℝ)) :
        |gBarX hH t.toNNReal (characteristic hH v r t).toNNReal - gBarX hH u r| ≤ ε := by
      have hh := heg (hpath t ht).1 ((hpath t ht).2.trans_lt
        (hwidth.trans_le ((min_le_right δB (min δQ δg)).trans (min_le_right δQ δg))))
      simpa only [Real.dist_eq, Real.toNNReal_coe] using hh.le
    have hh := forward_remainder F Q B hrad hcurve v r
      ⟨ha, hau.1.trans hau.2⟩ he.le hB' hQ' hg'
    have hcancel : ε * (2 + |Q u r|) = c := div_mul_cancel₀ c (ne_of_gt hden)
    simpa only [hcancel] using hh
  filter_upwards [eventually_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ v in 𝓝 (u : ℝ), dist v (u : ℝ) < δ from Metric.ball_mem_nhds _ hδ)] with v hv hnear
  have hnear' : |v - u| < δ := by simpa only [Real.dist_eq] using hnear
  simp only [Real.norm_eq_abs, smul_eq_mul, Real.toNNReal_coe]
  by_cases huv : (u : ℝ) ≤ v
  · have hh := hlocal u ⟨v, hv⟩ u.coe_nonneg ⟨le_rfl, huv⟩
      (by simpa only [abs_of_nonneg (sub_nonneg.mpr huv)] using hnear')
    simpa only [Real.toNNReal_coe, abs_of_nonneg (sub_nonneg.mpr huv), mul_comm] using hh
  · have hvu : v ≤ (u : ℝ) := (lt_of_not_ge huv).le
    have hwidth : (u : ℝ) - v < δ := by
      rw [abs_of_nonpos (sub_nonpos.mpr hvu)] at hnear'
      linarith only [hnear']
    have hh := hlocal v ⟨u, hp.1⟩ hv.1 ⟨hvu, le_rfl⟩ hwidth
    rw [Real.toNNReal_coe] at hh
    have habs : |F (v.toNNReal, r) - F (u, r) -
        (v - u) * (B u r + gBarX hH u r / 2 * Q u r)| =
        |F (u, r) - F (v.toNNReal, r) -
        (B u r + gBarX hH u r / 2 * Q u r) * ((u : ℝ) - v)| := by
      rw [← abs_neg]; congr 1; ring
    rw [habs, abs_of_nonpos (sub_nonpos.mpr hvu)]
    convert hh using 1; ring

/-- The time derivative is continuous on a nondegenerate strip. -/
private theorem continuousOn_time_derivWithin {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hu₀ : 0 < u₀)
    (F : C(ℝ≥0 × ℝ≥0, ℝ)) (Q B : ℝ≥0 → ℝ≥0 → ℝ)
    (hQ : ContinuousOn (fun p : ℝ × ℝ => Q p.1.toNNReal p.2.toNNReal)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0))
    (hB : ContinuousOn (fun p : ℝ × ℝ => B p.1.toNNReal p.2.toNNReal)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0))
    (htime : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      HasDerivWithinAt (fun s : ℝ => F (s.toNNReal, r))
        (B u r + gBarX hH u r / 2 * Q u r) (Icc 0 (u₀ : ℝ)) (u : ℝ)) :
    ContinuousOn (fun p : ℝ × ℝ => derivWithin
      (fun s : ℝ => F (s.toNNReal, p.2.toNNReal)) (Icc 0 (u₀ : ℝ)) p.1)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) := by
  have hg := (continuous_gBarX hH).comp
      (show Continuous (fun p : ℝ × ℝ => (p.1.toNNReal, p.2.toNNReal)) from
        (continuous_real_toNNReal.comp continuous_fst).prodMk
          (continuous_real_toNNReal.comp continuous_snd))
  apply (hB.add ((hg.continuousOn.div_const 2).mul hQ)).congr
  intro p hp
  have hu : p.1.toNNReal ≤ u₀ := by
    apply (NNReal.coe_le_coe).mp
    rw [Real.coe_toNNReal p.1 hp.1.1]
    exact hp.1.2
  have hd := htime p.1.toNNReal hu p.2.toNNReal
  rw [Real.coe_toNNReal p.1 hp.1.1] at hd
  exact hd.derivWithin ((uniqueDiffOn_Icc (by exact_mod_cast hu₀)) _ hp.1)

/-- Scalar remainder on an arbitrary convex set, so endpoints may occur in either order. -/
private theorem convex_remainder {f d : ℝ → ℝ} {s : Set ℝ} {a b c ε : ℝ}
    (hs : Convex ℝ s) (ha : a ∈ s) (hb : b ∈ s)
    (hd : ∀ t ∈ s, HasDerivWithinAt f (d t) s t)
    (he : ∀ t ∈ s, |d t - c| ≤ ε) :
    |f b - f a - c * (b - a)| ≤ ε * |b - a| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => f t - c * t) (f' := fun t => d t - c)
    (fun t ht => (hd t ht).sub (by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul c).hasDerivWithinAt))
    (fun t ht => by simpa only [Real.norm_eq_abs] using he t ht) hs ha hb
  simpa only [Real.norm_eq_abs,
    show f b - c * b - (f a - c * a) = f b - f a - c * (b - a) by ring] using hh

/-- A point between two endpoints is at most their distance from the first endpoint. -/
private theorem abs_sub_le_of_mem_uIcc {a b t : ℝ} (ht : t ∈ uIcc a b) : |t - a| ≤ |b - a| := by
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1), abs_of_nonneg (sub_nonneg.mpr hab)]
    linarith only [ht.2]
  · rw [uIcc_of_ge hba] at ht
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonpos (sub_nonpos.mpr hba)]
    linarith only [ht.1]

/-- First-order rectangle estimate, including all sides and corners. -/
private theorem hasFDerivWithinAt_rectangle {T : ℝ} {f P Q : ℝ × ℝ → ℝ}
    (hP : ContinuousOn P (Icc 0 T ×ˢ Ici 0)) (hQ : ContinuousOn Q (Icc 0 T ×ˢ Ici 0))
    (htime : ∀ p ∈ Icc 0 T ×ˢ Ici 0,
      HasDerivWithinAt (fun t => f (t, p.2)) (P p) (Icc 0 T) p.1)
    (hrad : ∀ p ∈ Icc 0 T ×ˢ Ici 0,
      HasDerivWithinAt (fun t => f (p.1, t)) (Q p) (Ici 0) p.2)
    {p : ℝ × ℝ} (hp : p ∈ Icc 0 T ×ˢ Ici 0) :
    HasFDerivWithinAt f
      (P p • ContinuousLinearMap.fst ℝ ℝ ℝ + Q p • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (Icc 0 T ×ˢ Ici 0) p := by
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δP, hδP, heP⟩ := Metric.continuousWithinAt_iff.mp (hP p hp) (ε / 2) (half_pos hε)
  obtain ⟨δQ, hδQ, heQ⟩ := Metric.continuousWithinAt_iff.mp (hQ p hp) (ε / 2) (half_pos hε)
  have hδ : 0 < min δP δQ := lt_min hδP hδQ
  filter_upwards [eventually_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ y in 𝓝 p, dist y p < min δP δQ from Metric.ball_mem_nhds _ hδ)] with y hy hnear
  have htime_sub : uIcc p.1 y.1 ⊆ Icc 0 T :=
    uIcc_subset_Icc hp.1 hy.1
  have hrad_sub : uIcc p.2 y.2 ⊆ Ici 0 := ordConnected_Ici.uIcc_subset hp.2 hy.2
  have htime_mem (t : ℝ) (ht : t ∈ uIcc p.1 y.1) :
      (t, y.2) ∈ Icc 0 T ×ˢ Ici 0 := ⟨htime_sub ht, hy.2⟩
  have hrad_mem (t : ℝ) (ht : t ∈ uIcc p.2 y.2) :
      (p.1, t) ∈ Icc 0 T ×ˢ Ici 0 := ⟨hp.1, hrad_sub ht⟩
  have htime_dist (t : ℝ) (ht : t ∈ uIcc p.1 y.1) : dist (t, y.2) p ≤ dist y p := by
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le_max (abs_sub_le_of_mem_uIcc ht) le_rfl
  have hrad_dist (t : ℝ) (ht : t ∈ uIcc p.2 y.2) : dist (p.1, t) p ≤ dist y p := by
    rw [Prod.dist_eq, dist_self, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le ((abs_nonneg _).trans (le_max_left _ _))
      ((abs_sub_le_of_mem_uIcc ht).trans (by
        simpa only [Real.dist_eq] using le_max_right (|y.1 - p.1|) (dist y.2 p.2)))
  have eP := convex_remainder (f := fun t => f (t, y.2)) (convex_uIcc p.1 y.1)
    left_mem_uIcc right_mem_uIcc
    (fun t ht => by exact (htime (t, y.2) (htime_mem t ht)).mono htime_sub)
    (c := P p) (ε := ε / 2)
    (fun t ht => by
      have hh := heP (htime_mem t ht) ((htime_dist t ht).trans_lt
        (hnear.trans_le (min_le_left δP δQ)))
      simpa only [Real.dist_eq] using hh.le)
  have eQ := convex_remainder (f := fun t => f (p.1, t)) (convex_uIcc p.2 y.2)
    left_mem_uIcc right_mem_uIcc
    (fun t ht => by exact (hrad (p.1, t) (hrad_mem t ht)).mono hrad_sub)
    (c := Q p) (ε := ε / 2)
    (fun t ht => by
      have hh := heQ (hrad_mem t ht) ((hrad_dist t ht).trans_lt
        (hnear.trans_le (min_le_right δP δQ)))
      simpa only [Real.dist_eq] using hh.le)
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul, Real.norm_eq_abs]
  have hdecomp : f y - f p - (P p * (y.1 - p.1) + Q p * (y.2 - p.2)) =
      (f (y.1, y.2) - f (p.1, y.2) - P p * (y.1 - p.1)) +
      (f (p.1, y.2) - f (p.1, p.2) - Q p * (y.2 - p.2)) := by
    simp only [Prod.mk.eta]; ring
  rw [hdecomp]
  have hn1 : |y.1 - p.1| ≤ ‖y - p‖ := by
    rw [Prod.norm_def]; exact le_max_left _ _
  have hn2 : |y.2 - p.2| ≤ ‖y - p‖ := by
    rw [Prod.norm_def]; exact le_max_right _ _
  calc
    _ ≤ |f (y.1, y.2) - f (p.1, y.2) - P p * (y.1 - p.1)| +
        |f (p.1, y.2) - f (p.1, p.2) - Q p * (y.2 - p.2)| := abs_add_le _ _
    _ ≤ ε / 2 * |y.1 - p.1| + ε / 2 * |y.2 - p.2| := add_le_add eP eQ
    _ ≤ ε * ‖y - p‖ := by
      have h1 := mul_le_mul_of_nonneg_left hn1 (half_pos hε).le
      have h2 := mul_le_mul_of_nonneg_left hn2 (half_pos hε).le
      linarith only [h1, h2]

/-- Package the rectangle derivative by a continuous field of continuous linear maps. -/
private theorem contDiffOn_rectangle {T : ℝ} {f P Q : ℝ × ℝ → ℝ}
    (hP : ContinuousOn P (Icc 0 T ×ˢ Ici 0)) (hQ : ContinuousOn Q (Icc 0 T ×ˢ Ici 0))
    (htime : ∀ p ∈ Icc 0 T ×ˢ Ici 0,
      HasDerivWithinAt (fun t => f (t, p.2)) (P p) (Icc 0 T) p.1)
    (hrad : ∀ p ∈ Icc 0 T ×ˢ Ici 0,
      HasDerivWithinAt (fun t => f (p.1, t)) (Q p) (Ici 0) p.2) :
    ContDiffOn ℝ 1 f (Icc 0 T ×ˢ Ici 0) := by
  let L : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun p =>
    P p • ContinuousLinearMap.fst ℝ ℝ ℝ + Q p • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hL : ContinuousOn L (Icc 0 T ×ˢ Ici 0) :=
    (hP.smul continuousOn_const).add (hQ.smul continuousOn_const)
  intro p hp
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffWithinAt_succ_iff_hasFDerivWithinAt (by simp), insert_eq_of_mem hp]
  exact ⟨Icc 0 T ×ˢ Ici 0, self_mem_nhdsWithin, by simp, L,
    fun y hy => hasFDerivWithinAt_rectangle hP hQ htime hrad hy,
    (contDiffOn_zero.mpr hL) p hp⟩


theorem classical_upgrade_of_characteristics {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hu₀ : 0 < u₀)
    (F : C(ℝ≥0 × ℝ≥0, ℝ)) (Q B : ℝ≥0 → ℝ≥0 → ℝ)
    (hQ : ContinuousOn (fun p : ℝ × ℝ => Q (Real.toNNReal p.1) (Real.toNNReal p.2))
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0))
    (hB : ContinuousOn (fun p : ℝ × ℝ => B (Real.toNNReal p.1) (Real.toNNReal p.2))
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0))
    (hrad : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      HasDerivWithinAt (fun s : ℝ => F (u, Real.toNNReal s)) (Q u r) (Ici 0) (r : ℝ))
    (hcurve : ∀ (v : Icc (0 : ℝ) u₀) (r : ℝ≥0) (χ : ℝ → ℝ),
      IsCharacteristic hH v r χ → ∀ t ∈ Icc 0 (v : ℝ),
        HasDerivWithinAt (fun s : ℝ => F (Real.toNNReal s, Real.toNNReal (χ s)))
          (B (Real.toNNReal t) (Real.toNNReal (χ t))) (Icc 0 (v : ℝ)) t) :
    (∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      HasDerivWithinAt (fun s : ℝ => F (Real.toNNReal s, r))
        (B u r + gBarX hH u r / 2 * Q u r) (Icc 0 (u₀ : ℝ)) (u : ℝ)) ∧
    ContinuousOn
      (fun p : ℝ × ℝ => derivWithin (fun s : ℝ => F (Real.toNNReal s, Real.toNNReal p.2))
        (Icc 0 (u₀ : ℝ)) p.1) (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => F (Real.toNNReal p.1, Real.toNNReal p.2))
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) := by
  have ht := hasDerivWithinAt_time hH F Q B hQ hB hrad hcurve
  refine ⟨ht, continuousOn_time_derivWithin hH hu₀ F Q B hQ hB ht, ?_⟩
  have hg := (continuous_gBarX hH).comp
      (show Continuous (fun p : ℝ × ℝ => (p.1.toNNReal, p.2.toNNReal)) from
        (continuous_real_toNNReal.comp continuous_fst).prodMk
          (continuous_real_toNNReal.comp continuous_snd))
  apply contDiffOn_rectangle (hB.add ((hg.continuousOn.div_const 2).mul hQ)) hQ
  · intro p hp
    have hu : p.1.toNNReal ≤ u₀ := by
      apply (NNReal.coe_le_coe).mp
      rw [Real.coe_toNNReal p.1 hp.1.1]
      exact hp.1.2
    have hh := ht p.1.toNNReal hu p.2.toNNReal
    rw [Real.coe_toNNReal p.1 hp.1.1] at hh
    exact hh
  · intro p hp
    have hu : p.1.toNNReal ≤ u₀ := by
      apply (NNReal.coe_le_coe).mp
      rw [Real.coe_toNNReal p.1 hp.1.1]
      exact hp.1.2
    have hh := hrad p.1.toNNReal hu p.2.toNNReal
    rw [Real.coe_toNNReal p.2 hp.2] at hh
    exact hh

end Christodoulou.Bondi.XCl
