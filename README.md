# LipschitzExtension

![build](https://github.com/GiulianoBasso/Grunbaum-lean/actions/workflows/build.yml/badge.svg)

A Lean 4 / Mathlib library of Lipschitz extension theorems. It formalizes

> G. Basso, *Lipschitz extension theorems with explicit constants*,
> Anal. Geom. Metr. Spaces **12** (2024), Paper No. 20240010 (arXiv:2310.13554),

including all corrections of Section 9 of

> G. Basso, *Errata to the single-author papers of Giuliano Basso* (2026),

and Section 2 (barycenter maps and conical bicombings) of

> G. Basso, *Extending and improving conical bicombings*, Enseign. Math. **70** (2024), 165–196,

with the proof from D. Descombes' PhD thesis (*Spaces with convex geodesic bicombings*, ETH Zürich
2015, Chapter 6) and Lemma 3.3 of G. Basso and B. Miesch, *Conical geodesic bicombings on subsets
of normed vector spaces* (Adv. Geom. 2019). It also contains Lemma 2.4 of Basso–Wenger–Young,
*Undistorted fillings in subsets of metric spaces*, which the first paper cites for Lemma 2.1,
and the results that the first paper cites for Theorem 1.3 and Lemmas 7.1 and 8.2, with
self-contained proofs: CAT(0) spaces and the Kirszbraun theorem of Lang–Schroeder (for maps from
subsets of inner product spaces into complete CAT(0) spaces), Vrecica's bound for the radial
projection onto the boundary of a convex body, and the upper bound of Baader et al. for the
distortion of the boundary of a simplex.

The long-term goal is an exhaustive library of Lipschitz extension theorems.

* 56 files, about 18 600 lines: about 490 public theorems and 160 definitions and structures,
  plus about 300 private auxiliary lemmas.
* No `sorry`, no additional axioms: every declaration depends only on `propext`,
  `Classical.choice` and `Quot.sound` (checked for all declarations).
* Written to Mathlib's standards: Mathlib-like folder structure, Mathlib naming conventions,
  copyright headers and module docstrings, `fun x ↦ …`. It builds with Lean `v4.35.0-rc3` and
  Mathlib `v4.35.0-rc3` (the pinned version) without warnings under Mathlib's linter set
  (`weak.linter.mathlibStandardSet`, including the header linter), and `#lint` passes.
* Released under the Apache 2.0 license (`LICENSE`).

## Using the library

The main theorems are stated like Mathlib's `LipschitzOnWith.extend_real`: a map `f : X → Y`
which is `1`-Lipschitz on `A ⊆ X` has an extension `F : X → Y` with
`LipschitzWith K F ∧ EqOn f F A`, where `K = (…).toNNReal` for the explicit real constant `…` of
the paper. They are in the namespace `LipschitzOnWith`, so they can be applied with dot notation:

```lean
import LipschitzExtension

open LipschitzExtension

/- Theorem 1.2 for complete CAT(0) targets. -/
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] (hY : IsCAT0 Y)
    {n : ℕ} {c : ℝ} {A : Set X} (hA : Nagata n c A) {f : X → Y} (hf : LipschitzOnWith 1 f A) :
    ∃ F : X → Y,
      LipschitzWith (1000 * (c + 1) * Real.logb 2 (n + 2)).toNNReal F ∧ Set.EqOn f F A :=
  hf.extend_nagata_isCAT0 hA hY
```

Naming scheme: `LipschitzOnWith.extend_<source>_<target>`, where `<source>` is the hypothesis on
the domain (`nagata`, `doubling`, `finite`, `triangulation`, `isWhitneyFamily`, …) and `<target>`
the hypothesis on the target (`lipschitzConnected`, `isGNPC`, `isCAT0`, `normedSpace`, …); a
prime marks a variant with a different constant. All other declarations are in the namespace
`LipschitzExtension` and follow Mathlib's naming conventions. Paper numbers are given in the
docstrings and in the tables below.

## Main results: *Lipschitz extension theorems with explicit constants*

Every numbered result of the paper is formalized, with the corrections of the errata (see
"Deviations" for the few differences in form). All constants are explicit and appear in the Lean
statements. File paths are relative to the folder `LipschitzExtension/`.

| Paper | Lean name | File | Constant `K` |
|---|---|---|---|
| Theorem 1.1 (Lang–Schlichenmaier), bound (1.1) | `LipschitzOnWith.extend_nagata_lipschitzConnected` | `Theorems/LangSchlichenmaier.lean` | `10^(10^10) λ^(n+1) (c+1)^10 (n+1)^(10n)` |
| Theorem 1.1, bound (1.2) (errata item 6) | `LipschitzOnWith.extend_nagata_lipschitzConnected'` | `Theorems/LangSchlichenmaier.lean` | `10^14 (c+1)^10 (10^5 λ)^(n+1) (n+1)^(6n)` |
| Theorem 1.2 (complete gNPC targets) | `LipschitzOnWith.extend_nagata_isGNPC` | `Theorems/Barycentric.lean` | `1000 (c+1) log₂(n+2)` |
| Theorem 1.2 (targets with a barycenter map) | `LipschitzOnWith.extend_nagata_barycenterMap`, `…_of_isClosed` | `Theorems/Barycentric.lean` | `1000 (c+1) log₂(n+2)` |
| Theorem 1.2 for Banach spaces | `LipschitzOnWith.extend_nagata_normedSpace` | `Theorems/Barycentric.lean` | `1000 (c+1) log₂(n+2)` |
| Theorem 1.2 for complete CAT(0) spaces | `LipschitzOnWith.extend_nagata_isCAT0` | `Theorems/Barycentric.lean` | `1000 (c+1) log₂(n+2)` |
| Theorem 1.3, `h` with constants `s`, `sD` on `n`-simplices (errata item 4), `X` a length space | `LipschitzOnWith.extend_triangulation_isCAT0` | `Theorems/Triangulation.lean` | `D N^(10 log n)` |
| Theorem 1.3, `h` with constants `D⁻¹`, `D` on `n`-simplices (errata item 4) | `LipschitzOnWith.extend_triangulation_isCAT0'` | `Theorems/Triangulation.lean` | `D² N^(10 log n)` |
| Theorem 1.3 for Riemannian manifolds (both conventions) | `LipschitzOnWith.extend_riemannian_triangulation_isCAT0`, `…'` | `Theorems/Triangulation.lean` | `D N^(10 log n)`, `D² N^(10 log n)` |
| Theorem 1.4 (Lee–Naor, doubling) | `LipschitzOnWith.extend_doubling_normedSpace` | `Theorems/LeeNaorDoubling.lean` | `10^5 log M` |
| Theorem 1.4 for sets with at most `n ≥ 2` points | `LipschitzOnWith.extend_finite_normedSpace'` | `Theorems/LeeNaorDoubling.lean` | `10^5 log n` |
| Theorem 1.5 (Lee–Naor, finite sets) | `LipschitzOnWith.extend_finite_normedSpace` | `Theorems/LeeNaorFinite.lean` | `1000 log n / log log n` (errata) |
| (1.6): `æ(X) ≤ 1000 log n / log log n` if `X` has at most `n ≥ 3` points | `absLipExtConst_le_of_card_le`, `absLipExtendableWith_of_card_le` | `Theorems/LeeNaorFinite.lean` | — |
| Theorem 2.4 (complete: gNPC ⇔ barycenter map) | `isGNPC_iff_nonempty_contractingBarycenterMap` | `Topology/MetricSpace/Barycenter/Contracting.lean` | — |
| Theorem 6.1 (general Whitney theorem; length spaces, errata item 5) | `LipschitzOnWith.extend_isWhitneyFamily_simplicialExtensor` (construction: `exists_lipAt_extension_of_isWhitneyFamily`) | `Theorems/Whitney.lean` | `100 C α δ⁻¹ γ log₂(n+2)` |
| Proposition 7.3 (complete gNPC ⇒ `LC(B^(n+1), √(1 + c_n²))`) | `IsGNPC.lcBall` | `Topology/MetricSpace/LipschitzConnected/GNPC.lean` | `√(1 + c_n²)` |
| Proposition 7.3 (complete gNPC ⇒ `LC(n, √3)`) | `IsGNPC.lipschitzConnected` | `Topology/MetricSpace/LipschitzConnected/GNPC.lean` | `√3` |
| Proposition 8.1 (`LC(n - 1, λ)` ⇒ simplicial extensor) | `LipschitzConnected.simplicialExtensor` | `Topology/MetricSpace/LipschitzConnected/SimplicialExtensor.lean` | `λⁿ (√2)ⁿ⁻¹ √n (n!)²` |
| Lang–Schroeder, Theorem A (inner product space domains; cited for Theorem 1.3) | `LipschitzOnWith.extend_innerProductSpace_isCAT0` | `Theorems/Kirszbraun.lean` | `K` (for `K`-Lipschitz `f`) |

Sharpness results of Section 7.1, for `Y = (P₁(S^n), W₁)`, `f(x) = δ_x` and conical extensions `F`
of `f` (with respect to any conical bicombing on `P₁(S^n)`), where `R = sup_{z ∈ S^n} W₁(F(0), δ_z)`.
All in `Topology/MetricSpace/LipschitzConnected/Sharpness.lean`:

| Paper | Statement | Lean name |
|---|---|---|
| Lemma 7.4, equality case (`n ≥ 1`) | `Lip F = √(1 + R²)` | `isLeast_lipschitz_conicalExtension_dirac` |
| Lemma 7.5 (`n ≥ 1`) | `Lip F ≥ √(1 + c_n²)` | `sqrt_one_add_sphereAvgDist_sq_le` |
| Lemma 7.5 is attained (tip `ρ_n`) | `Lip F = √(1 + c_n²)` | `isLeast_lipschitz_conicalExtension_sphereP1` |
| Lemma 7.5 fails for `n = 0` (`c₀ = 1`) | | `not_forall_sqrt_one_add_sphereAvgDist_sq_le_zero`, `exists_lipschitz_conicalExtension_dirac_lt_zero`, `sphereAvgDist_zero` |

Supporting results:

| Paper | Lean name | File |
|---|---|---|
| Definition 1.1, `Nagata(n, c)` | `Nagata` | `Topology/MetricSpace/Nagata/Defs.lean` |
| Definition 1.2, `LC(n, λ)` | `LipschitzConnected` | `Topology/MetricSpace/LipschitzConnected/Defs.lean` |
| Definition 1.3, gNPC | `IsGNPC`, `ConicalMidpointMap` | `Topology/MetricSpace/Barycenter/Defs.lean`, `Topology/MetricSpace/Bicombing/Midpoint.lean` |
| Section 1.5: CAT(0) spaces are gNPC; complete gNPC spaces are geodesic | `IsCAT0.isGNPC`, `IsGNPC.isGeodesicSpace` | `Geometry/CAT0/GNPC.lean` |
| Definition 1.4, absolute extendability `æ(X)` | `AbsLipExtendableWith`, `absLipExtConst` | `Topology/MetricSpace/AbsoluteExtendability.lean` |
| Section 2.4: `P₁(X)`, `W₁ = ‖μ - ν‖_KR`, barycenter maps | `P1`, `P1.W1`, `ContractingBarycenterMap` | `MeasureTheory/Wasserstein/Defs.lean`, `Topology/MetricSpace/Barycenter/Contracting.lean` |
| Barycenter maps on finitely supported measures | `FinProb`, `FinProb.W1`, `BarycenterMap` | `Topology/MetricSpace/Barycenter/Defs.lean` |
| Definition 6.1, simplicial extensor | `SimplicialExtensor` | `Geometry/SimplicialComplex/Basic.lean` |
| Definition 6.2, Whitney covering | `IsWhitneyFamily` | `Topology/MetricSpace/WhitneyCovering/Defs.lean` |
| Lemma 2.1 | `dist_le_of_lipAt_of_isQuasiconvex` (and `dist_le_of_lipAtWithin_Icc`, `dist_le_of_lipAtWithin_segment` on segments) | `Topology/MetricSpace/LengthSpace.lean`, `Topology/MetricSpace/PointwiseLipschitz/Basic.lean` |
| Lemma 2.2 | `dist_le_of_lipAt_of_continuousAt` (normed spaces), `IsLengthSpace.dist_le_of_lipAt_of_continuousAt` (length spaces) | `Topology/MetricSpace/PointwiseLipschitz/Normed.lean`, `Topology/MetricSpace/LengthSpace.lean` |
| Length spaces (errata item 5) | `IsLengthSpace`, `IsLengthSpace.dist_le_of_lipLowerLE`, `isLengthSpace_normedSpace`, `isLengthSpace_of_isRiemannianManifold` | `Topology/MetricSpace/LengthSpace.lean`, `Geometry/Manifold/Riemannian/LengthSpace.lean` |
| Lemma 2.3 (replacement, errata item 1) | `exists_padded_family` | `Topology/MetricSpace/PaddedDecomposition.lean` |
| Theorem 2.4, finitely supported version | `IsGNPC.nonempty_barycenterMap`, `BarycenterMap.isGNPC` | `Topology/MetricSpace/Barycenter/Construction.lean`, `Topology/MetricSpace/Barycenter/Defs.lean` |
| Lemma 2.5 | `FinProb.W1_ofWeights_le` | `Topology/MetricSpace/Barycenter/Defs.lean` |
| Normed spaces have barycenter maps | `BarycenterMap.ofNormedSpace` | `Topology/MetricSpace/Barycenter/Defs.lean` |
| Proposition 3.1 (errata item 2) | `Nagata.exists_isWhitneyFamily`, `…'` | `Topology/MetricSpace/WhitneyCovering/Nagata.lean` |
| Lemma 3.2 (`∑ Lip φᵢ ≤ 2e log(m)/(δ r_j)`, errata item 2) | `IsWhitneyFamily.exists_partitionOfUnity_log`, `…_lipAt` | `Topology/MetricSpace/WhitneyCovering/PartitionOfUnity.lean` |
| Lemma 3.2 (`ℓ¹` form, used in the proofs) | `IsWhitneyFamily.exists_partitionOfUnity` | `Topology/MetricSpace/WhitneyCovering/PartitionOfUnity.lean` |
| Lemma 4.1 (corrected, errata item 1) | `exists_scale_map` | `Theorems/LeeNaorFinite/Scale.lean` |
| Lemma 4.2 | `cutoff`, `sum_cutoff_eq`, `eventually_sum_abs_cutoff_sub_le` | `Theorems/LeeNaorFinite/Cutoff.lean` |
| Section 4, the construction of Theorem 1.5 | `exists_lipAt_extension_of_finite` | `Theorems/LeeNaorFinite/Local.lean` |
| Section 5: simplices and pure complexes in `ℓ₂(V)` | `Triangulation.face`, `Triangulation.PureComplex` | `Geometry/SimplicialComplex/Euclidean.lean`, `Geometry/SimplicialComplex/Quasiconvex.lean` |
| Lemma 5.1 | `Triangulation.exists_mem_face_inter_dist_add_dist_le`, `exists_mem_simplex_inter_l2dist_le` | `Geometry/SimplicialComplex/Euclidean.lean` |
| Lemma 5.2 (errata item 3) | `Triangulation.PureComplex.isQuasiconvex`, `Triangulation.PureComplex.exists_polygonal` | `Geometry/SimplicialComplex/Quasiconvex.lean` |
| BWY, Corollary 4.3 (the part used, errata item 4) | `Triangulation.IsSimplexwiseBilip.dist_le`, `…le_dist` | `Theorems/Triangulation.lean` |
| CAT(0) spaces (Bridson–Haefliger), CN inequality | `IsCAT0`, `IsGeodesicSpace`, `IsCAT0.dist_sq_le` | `Geometry/CAT0/Defs.lean` |
| Section 7: `LC(K, λ)`; `LC(B^(n+1), λ)` | `LCBody`; `LCBall`, `lipschitzConnected_iff_forall_lcBall` | `Topology/MetricSpace/LipschitzConnected/ConvexBody.lean`, `Topology/MetricSpace/LipschitzConnected/Defs.lean` |
| Vrecica's theorem (radial projection onto `∂K`) | `norm_sub_le_of_mem_frontier`, `dist_radialProj_le` | `Analysis/Convex/RadialProjection.lean` |
| Lemma 7.1 | `LCBall.lcBody`, `LCBody.lcBall` | `Topology/MetricSpace/LipschitzConnected/ConvexBody.lean` |
| Lemma 7.2 | `exists_extension_simplexE` (and `LipschitzConnected.exists_simplex_extension` in `ℓ₂(I)`) | `Topology/MetricSpace/LipschitzConnected/Simplex.lean` |
| Section 7.1: `c_n`, normalized volume of `S^n`, `c_n ≤ √2` | `sphereAvgDist`, `sphereMeasure`, `integral_dist_eq_sphereAvgDist`, `sphereAvgDist_le_sqrt_two` | `MeasureTheory/Sphere/Basic.lean` |
| Section 7.1: `c₁ = 4/π`, `c₂ = 4/3` | `sphereAvgDist_one`, `sphereAvgDist_two` | `MeasureTheory/Sphere/AvgDist.lean` |
| Section 7.1: `λ₁ = √(1 + 16/π²)`, `λ₂ = 5/3`; `Lip F ≤ 3 Lip f` if the tip lies in `f(S^n)` | `IsGNPC.lcBall_one`, `IsGNPC.lcBall_two`, `dist_conicalExtension_le_three_mul` | `Topology/MetricSpace/LipschitzConnected/GNPC.lean`, `Topology/MetricSpace/LipschitzConnected/ConicalExtension.lean` |
| Lemma 7.4 (for `L`-Lipschitz maps: `√(L² + R²)`) | `conicalExtension`, `dist_conicalExtension_le` | `Topology/MetricSpace/LipschitzConnected/ConicalExtension.lean` |
| Section 2.4: `W₁` is a metric on `P₁(X)`; Section 7.1: the linear bicombing `(1 - t) μ + t ν` | `P1.eq_of_W1_eq_zero`, `MetricSpace (P1 X)`, `P1.linearBicombing`, `P1.W1_dirac_right` | `MeasureTheory/Wasserstein/Metric.lean` |
| Section 7.1: `ρ_n ∈ P₁(S^n)`, `∫ W₁(ν, δ_z) dρ_n(z) = c_n`, `R ≥ c_n` | `sphereP1`, `integral_dist_dirac_eq_sphereAvgDist`, `sphereAvgDist_le_iSup_dist_dirac` | `Topology/MetricSpace/LipschitzConnected/Sharpness.lean` |
| New (finding 7): `W₁(σ(μ, δ_u, t), δ_w) = (1 - t) W₁(μ, δ_w) + t d(u, w)` for every conical bicombing `σ` on `P₁(S^n)` | `dist_toFun_dirac_sphere` | `Topology/MetricSpace/LipschitzConnected/Sharpness.lean` |
| Lemma 8.2 | `exists_extension_simplexE_of_faces` (and `lipschitz_simplexBoundary_of_faces` in `ℓ₂(I)`) | `Topology/MetricSpace/LipschitzConnected/Simplex.lean` |
| Baader et al. (upper bound, cited for Lemma 8.2): `∂Δⁿ` is `√(2 + 2/(n-1))`-quasiconvex | `SimplexExt.isQuasiconvex_boundaryE`, `SimplexExt.exists_mem_boundaryE_dist_add_dist_le` | `Topology/MetricSpace/LipschitzConnected/Simplex.lean` |
| Lemma 8.3 (errata item 10) | `Nagata.exists_colored_cover` | `Topology/MetricSpace/Nagata/Colored.lean` |
| Proposition 8.4 (all three properties) | `Nagata.exists_refinedCover` | `Topology/MetricSpace/WhitneyCovering/Refined.lean` |
| Proposition 8.4, Whitney consequence (paragraph after the proof) | `Nagata.exists_isWhitneyFamily_refined` | `Topology/MetricSpace/WhitneyCovering/Refined.lean` |
| Doubling ⇒ Nagata | `Doubling.nagata` (`M² - 1`), `Doubling.nagata_cube` (`M³`) | `Topology/MetricSpace/Nagata/Doubling.lean` |
| BWY Lemma 2.4 | `dist_le_of_lipLowerLE_curve`, `eVariationOn_comp_le_of_lipLowerLE`, `dist_le_of_lipLowerLE_of_isQuasiconvex` | `Topology/MetricSpace/PointwiseLipschitz/Lower.lean` |
| Errata item 5 (reduction via `E × ℝ`) | `exists_lipschitz_extension_of_local`, `exists_lipschitz_extension_of_local_of_completeSpace` | `Topology/MetricSpace/LocalExtension.lean` |

The numerical estimates at the end of the proofs (for example the last display of Section 8, with
`10^14`) are private lemmas in the files of the corresponding theorems.

## Main results: barycenter maps and conical bicombings

Section 2 of *Extending and improving conical bicombings*. A *contracting barycenter map* is a
`1`-Lipschitz map `β : P₁(X) → X` with `β(δ_x) = x`; `\overline{conv}_σ(A)` is the closure of the
smallest `σ`-convex set containing `A`, and `spt μ` the support of `μ`. File paths are relative to
`LipschitzExtension/Topology/MetricSpace/` unless they start with `MeasureTheory/` or
`Combinatorics/`.

| Source | Statement | Lean name | File |
|---|---|---|---|
| Theorem 2.6 | complete `X`: conical bicombing exists ⇔ `X` is barycentric | `nonempty_conicalBicombing_iff_nonempty_contractingBarycenterMap` | `Barycenter/Contracting.lean` |
| Theorem 2.7 | complete `X`, conical bicombing `σ` ⇒ contracting `β` with `β(μ) ∈ \overline{conv}_σ(spt μ)` | `ConicalBicombing.exists_contractingBarycenterMap` | `Barycenter/Contracting.lean` |
| Lemma 2.5 | `σ_β(x, y, t) = β((1-t)δ_x + tδ_y)` is a reversible conical bicombing | `ContractingBarycenterMap.toConicalBicombing`, `…_apply`, `isReversible_toConicalBicombing` | `Barycenter/Contracting.lean`, `Bicombing/OfBarycenter.lean` |
| Definition 2.4 | contracting barycenter map | `ContractingBarycenterMap` | `Barycenter/Contracting.lean` |
| Section 2.1 | `P₁(X)`, `W₁`, `δ_x`, finitely supported measures | `P1`, `P1.W1`, `P1.dirac`, `FinProb.toP1`, `FinProb.W1_toP1` | `MeasureTheory/Wasserstein/Defs.lean` |
| Proposition 2.2 (the inequality needed) | optimal pairings of uniform measures, via Egerváry's theorem | `FinProb.exists_pairing_le_W1`, `exists_perm_potentials` | `Barycenter/Assignment.lean` |
| Introduction | conical bicombings, reversibility, `σ`-convex sets and hulls | `ConicalBicombing`, `IsReversible`, `IsConvex`, `convexHull`, `closure_convexHull_eq_sInter` | `Bicombing/Defs.lean` |
| Basso–Miesch, Lemma 3.3 | complete `X`: symmetric conical midpoints in closed `σ`-convex sets | `ConicalBicombing.midpointMap`, `isConvex_midpointMap`, `ConicalBicombing.isGNPC` | `Bicombing/Midpoint.lean` |
| Basso–Miesch, Proposition 1.3 | reversible bicombing `τ` with `\overline{conv}_τ ⊆ \overline{conv}_σ` | `ConicalBicombing.exists_reversible` | `Barycenter/Construction.lean` |
| Descombes, Theorem 6.1 (i), (ii), (iv) | Es-Sahib–Heinich barycenters of finite multisets | `ConicalMidpointMap.baryM`, `baryM_mem`, `dist_baryM_le` | `Barycenter/EsSahibHeinich.lean` |
| Descombes, Lemma 6.2 | `d(z, bar x) ≤ C(n,k)⁻¹ ∑_{#I = k} d(z, bar x_I)` | `dist_baryM_le_sum_powersetCard` | `Barycenter/Descombes.lean` |
| Descombes, Proposition 6.4 | `d(bar(k·x), bar((k+l)·x)) ≤ D/(2√k)` | `dist_baryM_nsmul_le`, `cauchySeq_baryM_nsmul` | `Barycenter/Descombes.lean` |
| (hypergeometric moments) | `∑_I ∑_j |i_j(I) - k| ≤ C((k+l)n, kn) · n · √k` | `sum_abs_card_filter_sub_le` | `Combinatorics/Hypergeometric.lean` |
| Descombes, Theorem 6.5 (i), (iii) | barycenter map on finitely supported measures | `ConicalMidpointMap.barycenterMap`, `barycenterMap_mem` | `Barycenter/Construction.lean` |
| Theorems 2.6, 2.7 for finitely supported measures | | `nonempty_conicalBicombing_iff_nonempty_barycenterMap`, `ConicalBicombing.exists_barycenterMap` | `Barycenter/Construction.lean` |
| Density of finitely supported measures | with atoms in `spt μ` | `P1.exists_finProb_W1_le` | `MeasureTheory/Wasserstein/Density.lean` |
| Complete spaces | gNPC ⇔ conical bicombing | `isGNPC_iff_nonempty_conicalBicombing` | `Barycenter/Construction.lean` |

## How the errata is used

* **Item 1.** Lemma 2.3 is replaced by the de-randomized random-radius partition
  (`exists_padded_family`). Lemma 4.1 uses `m = 1` and holds for `d(x, A) ≤ 2ⁿ/8`
  (`exists_scale_map`, with the `logStar = max 1 log` convention). Theorem 1.5 and (1.6) have the
  constant `1000`.
* **Item 2.** Proposition 3.1 has the corrected `α` and `γ`. Lemma 3.2 has the constant `2e`
  (`exists_partitionOfUnity_log`). Theorem 1.2 keeps its constant `1000 (c+1) log₂(n+2)`.
* **Item 3.** Lemma 5.2 uses a chain of `n`-simplices of minimal length (non-consecutive
  simplices are disjoint, `m + 1 ≤ N`), repeated to length `2^ℓ`
  (`Triangulation.exists_polygonal_of_chain`).
* **Item 4.** Theorem 1.3 is proved in both forms: with `D N^(10 log n)` if
  `s |u - v| ≤ d(h u, h v) ≤ s D |u - v|` on every `n`-simplex (`IsSimplexwiseBilip`), and with
  `D² N^(10 log n)` for the usual convention `D⁻¹ |u - v| ≤ d(h u, h v) ≤ D |u - v|`.
* **Item 5.** The local-to-global step works in `E × ℝ`, where `E` is the Kuratowski space
  `X →ᵇ ℝ`. Two points of `X` are joined by the polygonal path through `(x, ε)` and `(y, ε)`.
  If the target is complete, `A` need not be closed. Theorem 6.1 is proved for length spaces
  (`LipschitzOnWith.extend_isWhitneyFamily_simplicialExtensor`, via Lemma 2.2 for length spaces);
  real normed spaces are length spaces (`isLengthSpace_normedSpace`).
* **Item 6.** The constant `α = 40·16³(c+1)⁴128ⁿ` enters the proof of Theorem 1.1. The bound (1.2)
  holds with `10^14` in place of `3·10^10` (`LipschitzOnWith.extend_nagata_lipschitzConnected'`;
  with `3·10^10` the final estimate of the proof fails already for `n = 0`, by a factor of about
  `150`, even with the exact constant of Proposition 8.1). The bound (1.1) holds as stated; we
  derive it from (1.2) (finding 11).
* **Item 8.** `N + 1 = max 1 ⌊log₂ log n⌋`.
* **Item 10.** Lemma 8.3 holds with diameter `2(c+1)(n+2)s` and same-colour distance `≥ s`.

## Deviations from the papers

* **Form of the statements.** The main theorems conclude `∃ F, LipschitzWith K F ∧ EqOn f F A`
  with `K = (…).toNNReal`, where `…` is the constant of the paper. Since `Real.toNNReal x = x` for
  `x ≥ 0`, this is the paper's statement whenever the constant is nonnegative, which is automatic
  under the hypotheses of the theorems. The old form `dist (F x) (F y) ≤ K * dist x y` follows
  with `LipschitzWith.dist_le_mul` and `Real.coe_toNNReal`.
* **No superfluous hypotheses.** The main theorems do not assume `c ≥ 0` (for a nonempty set,
  `Nagata(n, c)` forces `c ≥ 0`: `Nagata.nonneg`), `λ ≥ 0` (for `λ < 1`, a Lipschitz connected
  space has at most one point) or `[Nonempty Y]` (trivial cases:
  `exists_lipschitzWith_eqOn_of_nonempty`, `exists_lipschitzWith_eqOn_empty`,
  `exists_lipschitzWith_eqOn_of_subsingleton`). The remaining extra hypotheses are harmless:
  * `λ ≥ 1` and `[Nonempty Y]` in Proposition 8.1 (a standing assumption of Section 8; for
    `λ < 1` the space `Y` has at most one point). For `n = 0` the formal statement assumes
    `LC(0, λ)` (`n - 1 = 0` in `ℕ`).
  * `3 ≤ n` in Theorem 1.5 and (1.6) (needed: `log log n ≤ 0` for `n ≤ 2`; also assumed in
    Section 4), `2 ≤ n` for the consequence of Theorem 1.4 for sets with at most `n` points.
  * `C ≥ 1` in Theorem 6.1 (necessary, see finding 1).
* **Theorem 1.3** is proved for every length space `X` (`IsLengthSpace`: any two points are joined
  by curves of length at most their distance plus `ε`) with a triangulation `h : Σ → X` as in the
  theorem, where `Σ = K.carrier ⊆ ℓ₂(V)` is the union of the `n`-simplices `K.facets` of a finite
  pure complex with vertex set `V`. Compactness, connectedness and smoothness of `X` are not needed
  (compactness and connectedness follow from the other assumptions). The Riemannian version uses
  Mathlib's `IsRiemannianManifold` (the distance is the infimum of the lengths of `C¹` paths); such
  manifolds are length spaces (`isLengthSpace_of_isRiemannianManifold`). The part of Corollary 4.3
  of BWY that is needed (`h` is `s D N^(10 log n)`-Lipschitz and `h⁻¹` is `s⁻¹`-Lipschitz for the
  `ℓ₂`-metric on `Σ`) is proved directly, and the Kirszbraun theorem of Lang–Schroeder is proved for
  domains in real inner product spaces (all that is needed).
* **Theorem 6.1** is proved for length spaces `X` (errata item 5), which include all real normed
  spaces, with `C ≥ 1`.
* **Lemma 7.1** is stated as the two implications `LC(B^(m+1), λ) ⇒ LC(K, (R/r)² λ)` and
  `LC(K, λ_K) ⇒ LC(B^(m+1), (R/r) λ_K)`, for any bounds `r ≤ ‖x‖ ≤ R` on `∂K` (this is equivalent
  to the inequalities between the smallest constants). Vrecica's theorem is proved with our own
  elementary argument (`norm_sub_le_of_mem_frontier`).
* **Lemma 8.2** uses an explicit two-segment path instead of the theorem of Baader et al. and
  Lemma 2.1 (finding 10).
* **Lemma 3.2** is proved in two forms: for the pointwise Lipschitz constant of `z ↦ (φᵢ(z))ᵢ` in
  `ℓ¹` (`exists_partitionOfUnity`, the quantity used in the proofs, which is at most
  `∑ Lip φᵢ(z)`) and for `∑ Lip φᵢ(z)` as in the paper (`exists_partitionOfUnity_lipAt`,
  `exists_partitionOfUnity_log`). That each `φᵢ` is Lipschitz (never used) is not stated.
* **Proposition 8.4** is stated with all three properties (`Nagata.exists_refinedCover`), for the
  covering of `{z | 0 < d(z, A)}` (`A` need not be closed). The Whitney family obtained after the
  proof is `Nagata.exists_isWhitneyFamily_refined`.
* **Absolute extendability.** Lean has no type of all metric spaces: `æ(X)` (`absLipExtConst`)
  quantifies over the metric spaces `Xᵉ ⊇ X` (isometric embeddings) and the Banach spaces `Y` of
  fixed, arbitrary universes, and takes values in `[0, ∞]` (`∞` if `X` is not absolutely Lipschitz
  extendable). The bound (1.6) holds for all universes.
* **Section 7.1.** The normalized Riemannian volume of `S^n` is Mathlib's surface measure
  `volume.toSphere` divided by its mass, and `c_n` is defined with the base point `e₀`
  (`integral_dist_eq_sphereAvgDist`: every base point gives the same value, by reflection
  invariance). Lemma 7.4 is proved for `L`-Lipschitz maps. In the equality case of Lemma 7.4 and
  in Lemma 7.5, `f(x) = δ_x` is any map `ℝ^(n+1) → P₁(S^n)` that equals `δ_x` on `S^n` (only these
  values enter the conical extension), and "`Lip F`" is the least `K` with
  `d(F x, F y) ≤ K |x - y|` on the closed unit ball (`IsLeast`). Lemma 7.5 is formalized for
  `n ≥ 1` only; it is false for `n = 0` (finding 8).
* **`W₁`** is defined by the Kantorovich–Rubinstein formula
  `W₁(μ, ν) = sup {∫ f dμ - ∫ f dν : f 1-Lipschitz}`, exactly as in Section 2.4 of *Lipschitz
  extension theorems with explicit constants*. *Extending and improving conical bicombings*
  defines `W₁` by couplings and quotes the duality theorem. The Kantorovich–Rubinstein `W₁` is
  always at most the coupling `W₁`, so "contracting" in our sense is at least as strong, and the
  formal Theorem 2.7 is at least as strong as the paper's; for uniform measures the needed half of
  the duality is proved (`FinProb.exists_pairing_le_W1`).
* **Measures.** `X` carries its Borel σ-algebra (`[MeasurableSpace X] [BorelSpace X]`); "Radon" is
  `Measure.InnerRegular` (inner regular by compact sets); `spt μ` is Mathlib's `Measure.support`.
* **Bicombings** are functions `X → X → ℝ → X`; all conditions are imposed for parameters in
  `[0, 1]` only.
* **Proof of Theorem 2.7.** The paper first replaces `σ` by a reversible bicombing (Basso–Miesch,
  Proposition 1.3). We use the symmetric conical midpoint map of Basso–Miesch, Lemma 3.3,
  directly: Descombes' construction only needs the two-point barycenter, and the midpoint map
  takes values in every closed `σ`-convex set containing the two points. Proposition 1.3 (with the
  hull inclusion) is then a corollary (`ConicalBicombing.exists_reversible`).
* **Theorem 6.5** of the thesis is proved by approximating a measure by uniform measures on
  multisets (rounded weights) rather than first defining the barycenter for rational weights. The
  equivariance statements (Theorem 6.1 (iii), Theorem 6.5 (ii)) are not formalized.

## Findings during the formalization

These are small points about the papers that are not in the errata.

*Lipschitz extension theorems with explicit constants* and BWY:

1. **Theorem 6.1 needs `C ≥ 1` (or `n ≥ 1`).** For `n = 0`, `A = X = ℝ`, the empty Whitney
   family and `Y = ℝ` (a `(0, 0)`-simplicial extensor), the statement would give a `0`-Lipschitz
   extension of `f = id`. The appeal to Lemma 2.2 needs the constant to be `≥ 1`.
   `C ≥ 1` holds automatically if `n ≥ 1` and `Y` has two points.
2. **Theorem 1.5** in the introduction should assume `n ≥ 3`, as Section 4 does.
3. **Proof of Proposition 3.1.** The estimate `diam M ≤ s` is not enough, since
   `s`-multiplicity uses `diam < s`. Choosing `ρ(w)` with `d(ρ(w), w) < r^(k+1)` (strict) and
   arguing with finitely many members fixes this.
4. **Proof of Theorem 1.2** assumes that `A` is closed, but the statement does not. The
   completeness of `Y` closes the gap (`exists_lipschitz_extension_of_local_of_completeSpace`).
5. **BWY, Lemma 2.4.** "`ℓ(f∘γ) ≤ C ℓ(γ)` for every curve" needs rectifiable curves when `C = 0`.
   A counterexample is the inverse of the parametrization of a snowflake curve. Also,
   `Lip f(x) ≤ C` implies `lip f(x) ≤ C` only for `C ≥ 0`.
6. **Proof of Lemma 7.4.** The law of cosines and the discriminant computation can be replaced by
   a two-line argument: for `|x| = r ≤ s = |y|` and `z = (r/s) y` one has `⟨x - z, y - z⟩ ≤ 0`, so
   `d(F x, F y) ≤ L |x - z| + R |z - y| ≤ √(L² + R²) · √(|x - z|² + |z - y|²) ≤ √(L² + R²) |x - y|`.
   This also gives the version for `L`-Lipschitz maps (`√(L² + R²)`), so no rescaling of `Y` is
   needed in the proof of Proposition 7.3.
7. **Equality case of Lemma 7.4 and Lemma 7.5.** Lemma 7.5 is stated for every conical
   extension, i.e. every tip and every conical bicombing on `P₁(S^n)`, and its proof applies the
   equality case of Lemma 7.4 to such an extension. That equality case does not name a bicombing
   (as written, it is the lemma's arbitrary `σ`), but its proof computes with the linear
   bicombing only (`F(x) = (1 - r) μ + r δ_{x/|x|}`). The gap is closed by an averaging argument:
   every conical bicombing `σ` on `P₁(S^n)` satisfies
   `W₁(σ(μ, δ_u, t), δ_w) = (1 - t) W₁(μ, δ_w) + t |u - w|` for all `μ ∈ P₁(S^n)`,
   `u, w ∈ S^n` and `t ∈ [0, 1]` (`dist_toFun_dirac_sphere`: `≤` is the conical inequality, both
   sides have average `c_n` over `w`, and `ρ_n` has full support). Consequently the displayed
   formula `W₁(F(x), F(y)) = (s - r) W₁(μ, δ_y) + r d(x, y)` of the proof holds for every `σ` (`≥`
   by comparing both points with `δ_y`, `≤` by the conical inequality), so the paper's argument
   goes through, and both statements hold for every conical bicombing when `n ≥ 1`.
8. **Lemma 7.5 needs `n ≥ 1`.** For `n = 0` we have `c₀ = 1`. The space `P₁(S⁰)` is isometric to
   the interval `[0, 2]`, so the linear bicombing is its only conical bicombing, and the conical
   extension of `x ↦ δ_x` with tip `(δ₁ + δ₋₁)/2` is `1`-Lipschitz (even an isometry), while
   `1 < √2 = √(1 + c₀²)` (`not_forall_sqrt_one_add_sphereAvgDist_sq_le_zero`). Likewise, the
   sentence before Lemma 7.5 (the constants `λ_n` are best possible for conical extensions) fails
   for `n = 0`. The equality case of Lemma 7.4 correctly assumes `n ≥ 1`: for `n = 0` one has
   `Lip F = R` for every tip.
9. **Proof of Lemma 3.2.** "Clearly, `Lip ψ_i(x) = m ψ_i(x)^((m-1)/m)`" holds only with `≤`: at an
   isolated point of `X` every pointwise Lipschitz constant vanishes, and in general
   `d(·, X \ U_i)` can have pointwise Lipschitz constants smaller than `1`. Only `≤` is used.
10. **Proof of Lemma 8.2.** The theorem of Baader et al. and Lemma 2.1 can be replaced by an
    explicit path with two segments. Let `p, q ∈ ∂Δⁿ` with `p_a = 0` and `q_b = 0`, `a ≠ b`, and
    let `r_a = r_b = 0` and `r_i = (p_i + q_i)/2 + (p_b + q_a)/(2(n-1))` for `i ≠ a, b`. Then `r`
    shares a facet with `p` and with `q`, and `|p - r| + |r - q| ≤ √(2 + 2/(n-1)) |p - q|`, since
    `(2 + 2/(n-1)) |p - q|² - 2 (|p - r|² + |r - q|²) = (p_b - q_a)²/(n-1) + 4U (1 + 2/(n-1)) ≥ 0`
    with `U = ¼ ∑_{i ≠ a, b} (p_i - q_i)²`. In particular `∂Δⁿ` is `√(2 + 2/(n-1))`-quasiconvex
    (`SimplexExt.isQuasiconvex_boundaryE`).
11. **The bound (1.2) is never worse than (1.1).** After Theorem 1.1 the paper remarks that,
    depending on `n`, one might prefer (1.1) or (1.2). In fact (1.2) is at most (1.1) for all `n`
    and all `c, λ ≥ 0`, even with the corrected constant `10^14`: comparing the two bounds reduces to
    `10^(5n+19) ≤ 10^(10^10) (n + 1)^(4n)`, which is clear if `5n + 19 ≤ 10^10` and follows from
    `(n + 1)^(4n) ≥ 10^(8n) ≥ 10^(5n+19)` otherwise (then `n + 1 ≥ 100`). The library derives
    (1.1) from (1.2) in this way (`LipschitzOnWith.extend_nagata_lipschitzConnected`).

*Extending and improving conical bicombings* and Descombes' thesis:

12. **Proof of Theorem 2.7.** The reversible bicombing of Basso–Miesch, Proposition 1.3, is not
    needed; the symmetric midpoint map of their Lemma 3.3 suffices (see above).
13. **Proof of Theorem 2.7, last step.** The convex hull property does not follow from the
    density of measures with rational weights alone: one needs finitely supported approximations
    whose atoms lie in `spt μ`. These exist because `μ` is inner regular
    (`P1.exists_finProb_W1_le`).
14. **Proof of Lemma 2.5.** In the displayed inequality (2.2) the second `σ_{xy}(t)` should be
    `σ_{xz}(t)`, and the reversibility of `σ_β` is asserted but not proved; it holds because
    `(1-t)δ_x + tδ_y = tδ_y + (1-t)δ_x`. The displayed formula in the proof of Proposition 2.2 has
    index typos (`δ_{i,π(i)} d(x_i, y_j)`).
15. **Descombes' thesis.** In the proof of Theorem 6.1, "(iii) reduces (iv)" should read "(ii)
    reduces (iv)" (permutation invariance). In Proposition 6.4, `D` (a bound for the distances
    between the points `xᵢ`) is not defined. The relation `bar_n(x) = bar_n(x¹)` used in Lemma 6.2
    for `n = 2` holds by the symmetry of the midpoint map rather than by construction.

## Not formalized (yet)

* Results that *Lipschitz extension theorems with explicit constants* only quotes and does not use
  in its proofs: the bound `æ(X) ≤ √n` for `n`-point spaces (Basso; Kadets–Snobar), the structural
  properties of gNPC spaces mentioned in Section 1.5 (closure under Gromov–Hausdorff limits,
  `ℓ_p`-products and `1`-Lipschitz retractions; contractibility), and the results of
  Naor–Silberman and Brudnyi–Brudnyi discussed after Theorem 1.2.
* The (unused) fact that the functions `φᵢ` of Lemma 3.2 are Lipschitz.
* From *Extending and improving conical bicombings*: Lemma 2.1 (push-forwards), the exact
  formulas of Proposition 2.2 and Lemma 2.3 (only the inequalities used are proved),
  Kantorovich–Rubinstein duality for general measures, and Sections 3–6 (injective hulls,
  Theorems 1.1, 1.2, 1.4 and the boundary constructions).

## Roadmap towards an exhaustive library

Possible next steps, roughly in order of effort:

* McShane–Whitney extension and its vector-valued variants. Much of this is already in Mathlib
  (`LipschitzOnWith.extend_real`).
* Kirszbraun's theorem for Hilbert targets (inner product spaces are CAT(0)) and the Lang–Schroeder
  theorem for curvature bounded above by `κ`.
* The `√n` bound for extensions to `n` points (Basso, *Lipschitz extensions to finitely many
  points*); `æ(X)` is defined in `Topology/MetricSpace/AbsoluteExtendability.lean`.
* Johnson–Lindenstrauss–Schechtman (`O(log n)`) as a corollary, and Johnson–Lindenstrauss for
  Hilbert targets.
* Injective hulls and Theorem 1.1 of *Extending and improving conical bicombings*.
* Lower bounds (Naor–Rabani).

## Building

Requirements: `elan` (the Lean version manager; it installs the toolchain pinned in
`lean-toolchain` automatically), `git`, and internet access for the Mathlib cache. In the project
folder (on Windows in PowerShell or in the VS Code terminal) run

```
lake exe cache get   # clone Mathlib and download its prebuilt files (about 7 GB in .lake/)
lake build           # build the library (a few minutes)
```

In VS Code with the Lean 4 extension, open this folder (File → Open Folder) and then any `.lean`
file.

**Using it inside an existing Lean project** with the same Mathlib version: copy the folder
`LipschitzExtension/` and the file `LipschitzExtension.lean` into the project root, and add to its
`lakefile.toml`

```
[[lean_lib]]
name = "LipschitzExtension"
```

Then `import LipschitzExtension` (or individual modules) works.

## GitHub

The folder can be pushed as it is to a new GitHub repository. The workflows in
`.github/workflows` are those of the standard Lean project template (`lake new … math`):

* `lean_action_ci.yml` builds the library on every push and pull request and publishes the
  documentation (doc-gen4) on GitHub Pages;
* `update.yml` (started by hand) checks for a newer Mathlib release and opens a pull request that
  updates the dependency, or an issue if the update breaks the build;
* `create-release.yml` creates a release tag whenever `lean-toolchain` changes.

For the documentation and the update workflow, in the repository settings: under
**Actions → General** check "Allow GitHub Actions to create and approve pull requests", and under
**Pages** select "GitHub Actions" as the source. The citation keys used in the docstrings
(`[Basso2024]`, …) are defined in `docs/references.bib`.

Once the repository is on GitHub, another Lake project (with the same Mathlib version) can use the
library as a dependency:

```
[[require]]
name = "LipschitzExtension"
git = "https://github.com/<user>/<repository>"
rev = "main"
```

## Layout

```
LipschitzExtension/
  Analysis/Convex/RadialProjection.lean   Vrecica's bound for the radial projection onto ∂K
  Combinatorics/Hypergeometric.lean       a hypergeometric moment estimate (Descombes)
  Geometry/
    CAT0/                   CAT(0) spaces, CAT(0) ⇒ gNPC
    Manifold/Riemannian/    Riemannian manifolds are length spaces
    SimplicialComplex/      simplicial complexes, simplices in ℓ₂(V), Lemmas 5.1, 5.2
  MeasureTheory/
    Sphere/                 the normalized measure on S^n, c_n, c₁ = 4/π, c₂ = 4/3
    Wasserstein/            P₁(X), W₁ (a metric), density of finitely supported measures
  Topology/
    EMetricSpace/Lipschitz.lean   trivial cases of extension problems
    MetricSpace/
      PointwiseLipschitz/   pointwise Lipschitz constants, Lemma 2.1 on segments, BWY Lemma 2.4,
                            Lemma 2.2 for normed spaces
      LengthSpace.lean      length spaces, Lemmas 2.1 and 2.2 for length spaces
      LocalExtension.lean   from local to global extensions (errata item 5)
      AbsoluteExtendability.lean   æ(X) (Definition 1.4)
      Nagata/               Nagata(n, c), doubling spaces, colored coverings (Lemma 8.3)
      PaddedDecomposition.lean     the replacement of Lemma 2.3 (errata item 1)
      WhitneyCovering/      Whitney families, Proposition 3.1, Lemma 3.2, Proposition 8.4
      LipschitzConnected/   LC(n, λ), simplicial extensors, Lemmas 7.1, 7.2, 7.4, 7.5, 8.2,
                            Propositions 7.3, 8.1
      Bicombing/            conical bicombings, σ-convex hulls, midpoint maps, Lemma 2.5 (E&I)
      Barycenter/           barycenter maps, Descombes' construction, Theorems 2.6, 2.7 (E&I),
                            Theorem 2.4
  Theorems/
    LangSchlichenmaier.lean Theorem 1.1 (bounds (1.1) and (1.2))
    Barycentric.lean        Theorem 1.2
    Triangulation.lean      Theorem 1.3
    LeeNaorDoubling.lean    Theorem 1.4
    LeeNaorFinite.lean      Theorem 1.5 and (1.6); LeeNaorFinite/: Lemmas 4.1, 4.2 and the
                            construction of Section 4
    Whitney.lean            Theorem 6.1
    Kirszbraun.lean         Kirszbraun's theorem for CAT(0) targets (Lang–Schroeder)
```

(E&I = *Extending and improving conical bicombings*; all other numbers refer to *Lipschitz
extension theorems with explicit constants*. Equations are numbered within sections, as in the
paper: (1.1), (1.2) are the bounds of Theorem 1.1, (1.4) that of Theorem 1.2, (1.5) that of
Theorem 1.5 and (1.6) the bound for `æ(X)`.)

## Credits

Formalized by Claude (Anthropic), directed by Giuliano Basso, September 2026. Released under the
Apache 2.0 license.
