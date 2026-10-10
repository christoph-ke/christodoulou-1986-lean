/-
# `Christodoulou.Bondi.iterate_deriv_uniformEquicontinuousOn`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.ConstantDataField
public import Mathlib.Topology.UniformSpace.Equicontinuity
import Christodoulou.Bondi.Provider.IterateDerivUniformEquicontinuousOn



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi


theorem iterate_deriv_uniformEquicontinuousOn {u₀ : ℝ≥0} {x : ℝ}
    (data : C(ℝ≥0, ℝ))
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ)) (hb : ∀ n, MemXBall u₀ x (h n))
    (hzero : h 0 = constantDataField data)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n) data) :
    UniformEquicontinuousOn
      (fun n (p : ℝ × ℝ) => derivWithin
        (fun s : ℝ => h n (p.1.toNNReal, s.toNNReal)) (Ici 0) p.2)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.iterate_deriv_uniformEquicontinuousOn



end Christodoulou.Bondi

