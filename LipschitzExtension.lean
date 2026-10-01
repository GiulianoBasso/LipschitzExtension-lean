/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Analysis.Convex.RadialProjection
import LipschitzExtension.Combinatorics.Hypergeometric
import LipschitzExtension.Geometry.CAT0.Defs
import LipschitzExtension.Geometry.CAT0.GNPC
import LipschitzExtension.Geometry.Manifold.Riemannian.LengthSpace
import LipschitzExtension.Geometry.SimplicialComplex.Basic
import LipschitzExtension.Geometry.SimplicialComplex.Euclidean
import LipschitzExtension.Geometry.SimplicialComplex.Quasiconvex
import LipschitzExtension.MeasureTheory.Sphere.AvgDist
import LipschitzExtension.MeasureTheory.Sphere.Basic
import LipschitzExtension.MeasureTheory.Wasserstein.Defs
import LipschitzExtension.MeasureTheory.Wasserstein.Density
import LipschitzExtension.MeasureTheory.Wasserstein.Metric
import LipschitzExtension.Theorems.Barycentric
import LipschitzExtension.Theorems.Kirszbraun
import LipschitzExtension.Theorems.LangSchlichenmaier
import LipschitzExtension.Theorems.LeeNaorDoubling
import LipschitzExtension.Theorems.LeeNaorFinite
import LipschitzExtension.Theorems.LeeNaorFinite.Cutoff
import LipschitzExtension.Theorems.LeeNaorFinite.Local
import LipschitzExtension.Theorems.LeeNaorFinite.Scale
import LipschitzExtension.Theorems.Triangulation
import LipschitzExtension.Theorems.Whitney
import LipschitzExtension.Topology.EMetricSpace.Lipschitz
import LipschitzExtension.Topology.MetricSpace.AbsoluteExtendability
import LipschitzExtension.Topology.MetricSpace.Barycenter.Assignment
import LipschitzExtension.Topology.MetricSpace.Barycenter.Construction
import LipschitzExtension.Topology.MetricSpace.Barycenter.Contracting
import LipschitzExtension.Topology.MetricSpace.Barycenter.Defs
import LipschitzExtension.Topology.MetricSpace.Barycenter.Descombes
import LipschitzExtension.Topology.MetricSpace.Barycenter.EsSahibHeinich
import LipschitzExtension.Topology.MetricSpace.Barycenter.Uniform
import LipschitzExtension.Topology.MetricSpace.Bicombing.Defs
import LipschitzExtension.Topology.MetricSpace.Bicombing.Midpoint
import LipschitzExtension.Topology.MetricSpace.Bicombing.OfBarycenter
import LipschitzExtension.Topology.MetricSpace.LengthSpace
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.ConicalExtension
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.ConvexBody
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.Defs
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.GNPC
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.Sharpness
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.Simplex
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.SimplicialExtensor
import LipschitzExtension.Topology.MetricSpace.LocalExtension
import LipschitzExtension.Topology.MetricSpace.Nagata.Colored
import LipschitzExtension.Topology.MetricSpace.Nagata.Defs
import LipschitzExtension.Topology.MetricSpace.Nagata.Doubling
import LipschitzExtension.Topology.MetricSpace.PaddedDecomposition
import LipschitzExtension.Topology.MetricSpace.PointwiseLipschitz.Basic
import LipschitzExtension.Topology.MetricSpace.PointwiseLipschitz.Lower
import LipschitzExtension.Topology.MetricSpace.PointwiseLipschitz.Normed
import LipschitzExtension.Topology.MetricSpace.WhitneyCovering.Defs
import LipschitzExtension.Topology.MetricSpace.WhitneyCovering.Nagata
import LipschitzExtension.Topology.MetricSpace.WhitneyCovering.PartitionOfUnity
import LipschitzExtension.Topology.MetricSpace.WhitneyCovering.Refined

/-!
# Lipschitz extension theorems

This library formalizes Lipschitz extension theorems with explicit constants. It contains

* all numbered results of [Basso2024] (G. Basso, *Lipschitz extension theorems with explicit
  constants*), with the corrections of Section 9 of [BassoClaude2026];
* Section 2 of [Basso2024bicombings] (G. Basso, *Extending and improving conical bicombings*):
  barycenter maps and conical bicombings, with the proof of D. Descombes (PhD thesis, ETH Zürich
  2015, Chapter 6) and Lemma 3.3 of Basso–Miesch;
* results cited in these papers, with self-contained proofs: Lemma 2.4 of Basso–Wenger–Young,
  CAT(0) spaces and the Kirszbraun theorem of Lang–Schroeder, Vrecica's bound for the radial
  projection onto the boundary of a convex body, and the bound of Baader–Studer–Züst for the
  distortion of the boundary of a simplex.

## Main theorems

The main theorems are stated like Mathlib's `LipschitzOnWith.extend_real`: a map `f : X → Y` which
is `1`-Lipschitz on `A ⊆ X` has an extension `F : X → Y` with `LipschitzWith K F ∧ EqOn f F A`,
where `K = (…).toNNReal` for an explicit real constant `…`. They are in the folder `Theorems`, one
file per theorem, and in the namespace `LipschitzOnWith` (so `hf.extend_…` works for
`hf : LipschitzOnWith 1 f A`).

* `LipschitzOnWith.extend_nagata_lipschitzConnected'` and
  `LipschitzOnWith.extend_nagata_lipschitzConnected`: Theorem 1.1 (Lang–Schlichenmaier) with the
  bounds (1.2) and (1.1).
* `LipschitzOnWith.extend_nagata_isGNPC`: Theorem 1.2 (complete gNPC targets), with the variants
  `LipschitzOnWith.extend_nagata_barycenterMap`,
  `LipschitzOnWith.extend_nagata_barycenterMap_of_isClosed`,
  `LipschitzOnWith.extend_nagata_normedSpace` and `LipschitzOnWith.extend_nagata_isCAT0`.
* `LipschitzOnWith.extend_triangulation_isCAT0` and
  `LipschitzOnWith.extend_riemannian_triangulation_isCAT0` (and the primed versions): Theorem 1.3
  (bi-Lipschitz triangulations, complete CAT(0) targets).
* `LipschitzOnWith.extend_doubling_normedSpace`: Theorem 1.4 (Lee–Naor, doubling spaces).
* `LipschitzOnWith.extend_finite_normedSpace`: Theorem 1.5 (Lee–Naor, finite sets), and
  `LipschitzExtension.absLipExtConst_le_of_card_le`: the bound (1.6).
* `LipschitzOnWith.extend_isWhitneyFamily_simplicialExtensor`: Theorem 6.1 (length spaces).
* `LipschitzOnWith.extend_innerProductSpace_isCAT0`: Kirszbraun's theorem for CAT(0) targets
  (Lang–Schroeder).

## Further results

Of [Basso2024] (all in the namespace `LipschitzExtension`):
* Lemma 2.1 and Lemma 2.2: `dist_le_of_lipAt_of_isQuasiconvex`,
  `dist_le_of_lipAt_of_continuousAt` and `IsLengthSpace.dist_le_of_lipAt_of_continuousAt`;
* Theorem 2.4: `isGNPC_iff_nonempty_contractingBarycenterMap`;
* Proposition 3.1 and Lemma 3.2: `Nagata.exists_isWhitneyFamily`,
  `IsWhitneyFamily.exists_partitionOfUnity`;
* Lemma 5.2: `Triangulation.PureComplex.isQuasiconvex`;
* Lemma 7.1: `LCBall.lcBody`; Lemma 7.2: `exists_extension_simplexE`,
  `LipschitzConnected.exists_simplex_extension`; Proposition 7.3: `IsGNPC.lcBall`,
  `IsGNPC.lipschitzConnected`; Lemma 7.4 (equality case):
  `isLeast_lipschitz_conicalExtension_dirac`; Lemma 7.5: `sqrt_one_add_sphereAvgDist_sq_le`;
* Proposition 8.1: `LipschitzConnected.simplicialExtensor`; Lemma 8.2:
  `lipschitz_simplexBoundary_of_faces`; Proposition 8.4: `Nagata.exists_refinedCover`.

Of [Basso2024bicombings]:
* Theorem 2.6: `nonempty_conicalBicombing_iff_nonempty_contractingBarycenterMap`;
* Theorem 2.7: `ConicalBicombing.exists_contractingBarycenterMap`;
* Lemma 2.5: `ContractingBarycenterMap.toConicalBicombing`.

## Structure

* `Topology`: pointwise Lipschitz constants, length spaces, the reduction from local to global
  extensions, Nagata dimension and doubling, padded decompositions, Whitney coverings and their
  partitions of unity, Lipschitz connectedness and simplicial extensors, conical bicombings and
  barycenter maps, absolute Lipschitz extendability.
* `Geometry`: CAT(0) spaces, simplicial complexes, Riemannian manifolds as length spaces.
* `Analysis`, `MeasureTheory`, `Combinatorics`: the radial projection onto the boundary of a
  convex body, the normalized measure on spheres, Wasserstein spaces `P₁(X)`, a hypergeometric
  moment estimate.
* `Theorems`: the main theorems.

See `README.md` for a complete map between the papers and the Lean declarations.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
* [G. Basso, *Extending and improving conical bicombings*][Basso2024bicombings]
-/
