module
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.ConstantDataField
public import Mathlib.Topology.UniformSpace.Equicontinuity
import Christodoulou.Bondi.DerivEquicontinuity



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem iterate_deriv_uniformEquicontinuousOn {u₀ : ℝ≥0}
    {x : ℝ}
    {data : C(ℝ≥0, ℝ)}
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ) := by assumption)
    (hb : ∀ n, MemXBall u₀ x (h n) := by assumption)
    (hzero : h 0 = constantDataField data := by assumption)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n) data := by assumption) :
    UniformEquicontinuousOn
      (fun n (p : ℝ × ℝ) => derivWithin
        (fun s : ℝ => h n (p.1.toNNReal, s.toNNReal)) (Ici 0) p.2)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) :=
  XEq.iterate_deriv_uniformEquicontinuousOn data h hb hzero hstep

end Christodoulou.Bondi.Provider
