/-
# `Christodoulou.Bondi.hasDerivAt_xi`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.Xi
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Christodoulou.Bondi.Provider.HasDerivAtXi



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem hasDerivAt_xi (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => xi h hh (Real.toNNReal s))
      (gBar h hh r * (h r - mean h r) / (r : ℝ)) (r : ℝ) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.hasDerivAt_xi



end Christodoulou.Bondi

