# Christodoulou's self-gravitating scalar field in Lean

This repository formalizes analytic results from Demetrios Christodoulou, *The problem of a self-gravitating scalar field*, **Communications in Mathematical Physics 105** (1986), 337–361, DOI: [10.1007/BF01205930](https://doi.org/10.1007/BF01205930).

The library proves local existence and uniqueness for the uniformly decaying classical-solution class, small-data global existence with decay, zero limiting Bondi mass, Bondi mass monotonicity, and mass monotonicity along incoming rays. The geometric completeness conclusion of the paper's Theorem 3 is out of scope. This is a one-time export of source revision `89f7e13854ff259c459de7b705fb7ce11ed4e8f2`, with scope approved by Christoph Kehle on 2026-10-10.

All 198 author-approved anchor declarations are proved. The release contains 423 Lean modules, including proof infrastructure and providers. [Christodoulou.lean](Christodoulou.lean) imports the complete library; [depgraph/anchors.json](depgraph/anchors.json) lists every anchor, its file, source correspondence and release file hash. The reviewed [dependency graphs](depgraph/README.md) describe mathematical source dependencies; they are distinct from Lean proof terms and proof status.

## Build and audit

Install [Lean through elan](https://github.com/leanprover/elan) and use a current Git installation. The exact toolchain is **Lean `v4.35.0-rc3`**. Mathlib is pinned to **`7d6757bc18680044fc0ff6efc8ee20494b408556`**; all transitive dependency revisions are pinned in [lake-manifest.json](lake-manifest.json). Python 3.10 or newer is required for the audit.

From the repository root:

```sh
lake exe cache get
lake build
python3 scripts/check_axioms.py
```

The cache command obtains compiled Mathlib dependencies at the pinned revision. `lake build` checks the project. The audit prints the axioms of **every one of the 198 anchors**, checks that the frozen-file inventory and hashes match the release, and fails if an anchor is missing or uses any axiom beyond `propext`, `Classical.choice`, and `Quot.sound`. It also walks the types and bodies of every project declaration, including private declarations, checks stored declarations for conflicts, rejects project axioms, and requires every project source and built module to be imported by the umbrella module.

There are no admitted proofs or custom axioms. Ordinary library files do not contain expensive axiom-printing commands. This release has no hosted CI.

## Paper results and Lean declarations

Names in the table belong to `Christodoulou.Bondi`, except those explicitly prefixed by `Christodoulou.Radial`. The stage column follows the mathematical progression of the formalization. The complete correspondence, including supporting definitions and estimates, is in the anchor inventory.

| Stage | Paper results | Lean declarations |
|---|---|---|
| Radial mean | (3.7)–(3.9), regular centre | `Christodoulou.Radial.mean`, `mean_zero`, `mean_eq_integral`, `continuous_mean`, `hasDerivWithinAt_mul_mean`, `hasDerivAt_mean`, `eq_mean_of_hasDerivWithinAt_mul` (all in `Christodoulou.Radial`) |
| Slice classes and metric coefficient | (3.11), positivity, monotonicity and radial derivative of g | `IsSlice`, `IsDecaySlice`, `integrableOn_tail`, `g`, `continuous_g`, `g_pos`, `g_le_one`, `monotone_g`, `tendsto_g_atTop`, `hasDerivAt_g` |
| Radial mass | (3.12), (4.3)–(4.5) | `gMap`, `gBar`, `mass`, `gBar_le_g`, `hasDerivAt_deriv_gBar`, `mass_nonneg`, `mass_zero`, `mass_lt_half`, `hasDerivAt_mass`, `monotone_mass`, `mass_eq_integral` |
| Classical-solution interface and mean evolution | (3.13), (4.1)–(4.2) | `IsClassicalSolution`, `xi`, `intervalIntegrable_xi`, `hasDerivAt_xi`, `IsClassicalSolution.isSlice`, `hasDerivAt_mean_curry`, `evolution_mean` |
| Characteristic coefficient estimates | (7.1), inputs to (5.1) | `MemXBall`, `gX`, `gBarX`, `derivGBarX`, `charField`, `continuous_gBarX`, `hasDerivWithinAt_gBarX`, `derivGBarX_le`, `lipschitzWith_gBarX`, `isPicardLindelof_charField` |
| Terminal-point characteristics | (5.1)–(5.3), terminal bounds | `IsCharacteristic`, `exists_isCharacteristic`, `IsCharacteristic.eqOn`, `IsCharacteristic.mem_Icc`, `IsCharacteristic.eq_add_integral`, `IsCharacteristic.eq_sub_integral`, `IsCharacteristic.strictAntiOn`, `characteristicOn`, `characteristic` |
| Linear iteration step | (7.2), characteristic formula on p. 350 | `hBarX`, `linearCoeff`, `linearSource`, `linearStep`, `linearStep_zero`, `IsCharacteristic.hasDerivWithinAt_linearStep`, `IsCharacteristic.linearStep_eq_add_integral`, `eq_linearStep_of_hasDerivWithinAt` |
| Dependence on terminal point | Terminal form of (5.8); inverse convergence factor associated with (5.6) | `characteristic_sub_mem_Icc`, `characteristic_sub_mem_Icc_of_le`, `continuous_characteristic`, `hasDerivWithinAt_characteristic`, `continuous_exp_integral_linearCoeff` |
| Radial regularity at the centre | (9.4), (9.6), (9.17), estimates on p. 356 | `derivHBarX`, `deriv2GBarX`, `hasDerivWithinAt_hBarX`, `continuous_derivHBarX`, `hasDerivWithinAt_derivGBarX`, `continuous_deriv2GBarX`, `hasDerivWithinAt_linearSource`, `abs_deriv_linearSource_le` |
| Classical linear step and local iteration bounds | (9.16), (7.2)–(7.3), Lemma 1 | `derivLinearStep`, `continuous_linearStep`, `classical_upgrade_of_characteristics`, `linearStepMap`, `linearStep_classical`, `stepEta`, `linearStepMap_memXBall`, `xBallIterate`, `xBallIterate_rec`, `lemma1` |
| Local contraction and equicontinuity | Lemmas 2–3, (7.60), local forms of (9.27), (9.30)–(9.34) | `stepDelta`, `coefficient_y_lipschitz`, `linearStep_difference_integral`, `linearStep_y_lipschitz`, `lemma2`, `xBallIterate_time_bound`, `iterate_deriv_uniformEquicontinuousOn`, `lemma3` |
| Local existence | Theorem 1, pp. 348–351 | `xBallIterate_limit`, `isClassicalSolution_of_linearStepMap_eq`, `theorem1_of_lt`, `theorem1` |
| Uniqueness | Theorem 2, p. 351 | `exists_memXBall_of_isClassicalSolution`, `linearStep_eq_of_isClassicalSolution`, `classical_difference_integral_le`, `theorem2_of_memXBall`, `theorem2` |
| Small-data global iteration | (7.4), (9.1)–(9.3), (9.24)–(9.26), Lemmas 4–5 | `MemXPrimeBall`, `initialSize`, `smallDataG`, `contractionFactor`, `smallDataDelta`, `translatedDataField`, `linearStep_prime_bound`, `lemma4`, `linearStep_yPrime_lipschitz`, `lemma5` |
| Unscaled global existence | Analytic part of Theorem 3, p. 360 | `translated_iterate_deriv_uniformEquicontinuousOn`, `primeIterate_limit`, `global_exists_of_G`, `theorem3_unscaled` |
| Scaling and scale-invariant smallness | (4.13), d₀ on p. 352, analytic part of Theorem 3 | `radialScale`, `fieldScale`, `scaledInitialSize`, `scaleInvariantSize`, `initialSize_radialScale`, `scaleInvariantSize_radialScale`, `isClassicalSolution_fieldScale`, `radialDerivative_fieldScale`, `theorem3_analytic` |
| Bondi mass and its decay | M = lim m, (4.14)–(4.15), M₁ = 0 | `bondiMass`, `bondiMass_spec`, `mass_fieldScale`, `bondiMass_fieldScale`, `bondiMass_le_of_deriv_bound`, `tendsto_bondiMass_zero_of_decay`, `theorem3_mass_zero` |
| Mass evolution and Bondi's theorem | (4.6)–(4.7), M nonincreasing | `hasDerivAt_mass_curry`, `evolution_mass`, `tendsto_mul_one_sub_g`, `bondiMass_eq_integral_one_sub_g`, `antitoneOn_bondiMass`, `theorem3_bondi` |
| Mass along terminal-point incoming rays | (4.6) along (5.1) | `hasDerivAt_mass_characteristic`, `antitoneOn_mass_characteristic` |
| Printed uniform-decay hypotheses | Theorem 2 in its printed big-O form | `valueBound_weighted_iff_printed`, `radialDerivative_weighted_iff_printed`, `printedBound_iff_explicit`, `theorem2_printed`, `exists_memXBall_of_isClassicalSolution_printed` |
| Incoming rays from the initial slice | χ(u; r₀), pp. 345–346; reflection at the centre; radial and incoming mass monotonicity | `IsIncomingRay`, `exists_isIncomingRay`, `IsIncomingRay.unique`, `IsIncomingRay.isCharacteristic`, `reflectedRay`, `IsIncomingRay.antitoneOn_mass`, `monotoneOn_mass_reflectedRay_outgoing` |

The table does **not** assert the complete forward-flow conclusions (5.4)–(5.8). Dependence on a terminal point is proved; dependence of the forward flow on its initial radius remains open.

## Scope and remaining obligations

`IsClassicalSolution u₀ H` requires C¹ regularity on the closed strip `[0, u₀] × [0, ∞)`, a single constant C with `|H(u,r)| ≤ C(1+r)⁻³` throughout that strip, and equation (3.13) at interior points `0 < u < u₀`, `r > 0`. Values after `u₀` are unconstrained. This is the **restricted, uniformly decaying classical-solution class**, rather than the paper's most general classical-solution class. The slice interface requires C¹ regularity and cubic decay; the paper's finite-initial-mass generalization is not formalized. The solution predicate is degenerate when `u₀ = 0`; the local-existence theorem asserts positive time.

Theorems 1 and 2 are proved for the approved data and solution interfaces. Theorem 1 uses an alternative argument: contraction of the full iterate sequence, derivative convergence by interpolation with equicontinuity, and a classical fixed point of the linear step. Theorem 2 reconstructs the paper's one-sentence proof sketch using an integral inequality and factorial closure. The equivalence between global weighted bounds and printed uniform tail decay is proved for values and radial derivatives; `theorem2_printed` supplies the printed derivative hypotheses. Separate printed-form statements of Theorems 1 and 3 and of the mass-evolution anchors are not supplied.

The mass-evolution and Bondi-monotonicity anchors additionally assume a strip-uniform bound `|radialDerivative H u r| ≤ C(1+r)⁻⁴` and a slice-class family for every time. The terminal-point mass-on-characteristics anchors require `MemXBall` and that slice family. The later `IsIncomingRay.antitoneOn_mass` result uses the X-ball on the strip and does not require slices beyond it.

Theorem 3's analytic conclusion is proved, including scaling, global decay, zero limiting Bondi mass and nonincreasing Bondi mass. **Future timelike and null geodesic completeness is out of scope**, by the author's decision of 2026-10-10. The global existence roots do not additionally claim uniqueness or X′ membership of their scaled global solution.

The remaining recorded obligations and unformalized source claims are:

- The forward flow map `r₀ ↦ χ(·; r₀)`: coverage of the strip, ordering, regularity in the initial radius, ζ and the forward forms of (5.4)–(5.8). Existence and uniqueness up to the centre on each strip are proved; a global ray flow, rays beyond the strip and a geometric null-geodesic statement about the reflected outgoing part are not claimed.
- The uniform lower bound for the characteristic coefficient and the associated lower bound on the characteristics on p. 354; stability under a change of field, including the corrected (7.76); coherence in strip length and locality in the field.
- The printed Theorem-1 proof steps: (a) an Ascoli subsequence, (b) uniform convergence of the coefficients, (c) convergence of characteristics with its Gronwall bound, (d) passage to the limit in the p. 350 characteristic formula, and (e) the Cᵏ regularity remark on p. 351.
- The derivation of (4.6) from `E(n,n) = 0`, and the curvature expressions (4.8)–(4.12). The analytic mass-evolution law is proved directly from (3.13) and regularity at the centre. No equivalence with the full Einstein equations is claimed.
- Differentiability of the Bondi mass M and its derivative mass-loss formula. The library proves monotonicity of M; the characteristic derivative formula for m is stated at interior times, without endpoint derivatives.
- The p. 352 claim that G increases to its maximum at x₀ (`exists_G_peak`), the assertion that d₀ is a norm, and the equality `‖h₀‖_X′ = d` for the translated seed. The required upper bound is proved.
- The initial interface record defers equivalence between the interior equation and one-sided equations on the time edges, and the separate centre equation. Joint coefficient continuity is proved later; the printed uniform-decay bridge is also proved later.

Lemma 4 is proved for all positive radii, strengthening the printed restricted radius range, on each strip with its time clamp. The estimates used for the global iteration incorporate the recorded corrections to the paper's indices, denominators and powers. The existence of the Bondi mass uses slice decay, rather than a separate finite-M₀ assumption. These are the approved interpretations and reconstructed arguments used by the library.

Mathlib supplies the real analysis, calculus, integration, topology and Picard–Lindelöf infrastructure. The results named above are project declarations, proved using that pinned dependency. The dependency graphs identify external mathematical inputs explicitly. Source-topology coverage exclusions apply to the scope of each graph and are not a list of unfinished Lean anchors.

## License, citation and acknowledgements

Copyright © 2026 Christoph Kehle. The formalization, audit script and dependency data are released under the [Apache License 2.0](LICENSE). Mathlib and other dependencies retain their own licenses and notices; they are downloaded by Lake and are not vendored in this release. The paper and supporting papers are not distributed or relicensed here. Cite the paper by its DOI, and cite this formalization using [CITATION.cff](CITATION.cff).

This formalization was produced by Christoph Kehle with assistance from Claude Code and OpenAI Codex, using source-first statement review, frozen declarations, independent audits, and Lean kernel checking.
