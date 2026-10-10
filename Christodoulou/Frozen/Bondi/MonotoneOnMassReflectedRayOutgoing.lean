/-
# `Christodoulou.Bondi.monotoneOn_mass_reflectedRay_outgoing`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsClassicalSolutionIsSlice
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.ReflectedRay
import Christodoulou.Bondi.Provider.MonotoneOnMassReflectedRayOutgoing



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- m is nondecreasing (in r) on the terminal-time section u = u₁ of the reflected ray; when
the ray reaches the centre (χ(u₁) = 0) this section is the whole outgoing light ray u = u₁, r ≥
0 (the monotonicity of m in r at fixed u, [P] p. 344, (4.4)–(4.5)). Stated for arbitrary u₁, χ,
with m on the clamped strip slice; for an incoming ray the clamps are the identity there. -/
theorem monotoneOn_mass_reflectedRay_outgoing {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (u₁ : ℝ) (χ : ℝ → ℝ) :
    MonotoneOn (fun p : ℝ × ℝ => mass (H.curry (min (Real.toNNReal p.1) u₀))
        (hH.isSlice _ (min_le_right _ _)) (Real.toNNReal p.2))
      {p | p ∈ reflectedRay u₁ χ ∧ p.1 = u₁} :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.monotoneOn_mass_reflectedRay_outgoing



end Christodoulou.Bondi

