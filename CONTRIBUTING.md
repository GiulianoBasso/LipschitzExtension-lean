# Contributing

Conventions for extending the `LipschitzExtension` library. The library follows the conventions
of Mathlib (naming, style, documentation); see the
[Mathlib contribution guidelines](https://leanprover-community.github.io/contribute/index.html).

## Principles

1. **Faithful statements.** Every theorem that formalizes a result from the literature says so in
   its docstring (paper, numbering, errata item). Extra hypotheses are listed and justified in the
   module docstring. If a published statement is false or incomplete, record it in `README.md`
   ("Findings during the formalization").
2. **Explicit constants.** State constants explicitly, as real expressions, not as `∃ C`.
3. **No `sorry`, no axioms.** The main branch builds without `sorry`, `admit`, `native_decide`
   or `axiom`. Check new main theorems with `#print axioms`.
4. **Mathlib style.** Every file starts with the copyright header (Apache 2.0) and a module
   docstring (`# Title`, summary, `## Main definitions`, `## Main statements`, optionally
   `## Implementation notes` and `## Proof outline`, `## References`). Every public definition
   has a docstring. Lines have at most 100 characters; use `fun x ↦ …`. The build must be free of
   warnings under the linters enabled in `lakefile.toml` (Mathlib's standard set, including the
   header linter), and `#lint in LipschitzExtension` must pass.

## Where things go

* General notions and results go into the Mathlib-like folders (`Topology/MetricSpace/…`,
  `Geometry/…`, `Analysis/…`, `MeasureTheory/…`, `Combinatorics/…`), in the namespace
  `LipschitzExtension`.
* Each main extension theorem gets its own file in `Theorems/`. Auxiliary constructions that are
  only used for one theorem go into a subfolder of the same name (e.g. `Theorems/LeeNaorFinite/`).
  Numerical estimates that are only used in one proof are `private`.
* Add every new file to `LipschitzExtension.lean` and the result to the tables in `README.md`.

## Naming

* Main extension theorems live in the namespace `LipschitzOnWith` (so that dot notation works for
  `hf : LipschitzOnWith 1 f A`) and are called `LipschitzOnWith.extend_<source>_<target>`, where
  `<source>` names the hypothesis on the domain (`nagata`, `doubling`, `finite`,
  `triangulation`, `isWhitneyFamily`, …) and `<target>` the hypothesis on the target
  (`lipschitzConnected`, `isGNPC`, `isCAT0`, `normedSpace`, `barycenterMap`, …). A prime marks a
  variant with a different constant.
* Everything else follows Mathlib's naming conventions: `snake_case` for theorems, describing the
  statement (`exists_lipAt_extension_of_isWhitneyFamily`), `UpperCamelCase` for `Prop`-valued
  definitions and structures (`Nagata`, `IsWhitneyFamily`, `LipschitzConnected`), `lowerCamelCase`
  for data (`conicalExtension`, `sphereAvgDist`); a definition `Foo` appears as `foo` in theorem
  names. Theorems whose main hypothesis is `h : Foo …` go into the namespace `Foo` when this
  makes dot notation useful (`Nagata.exists_isWhitneyFamily`,
  `LipschitzConnected.simplicialExtensor`). Paper numbers appear in docstrings, not in names.

## Statement conventions

* Maps are total functions `f : X → Y`; "1-Lipschitz on `A`" is `LipschitzOnWith 1 f A`.
* Main theorems conclude `∃ F : X → Y, LipschitzWith K F ∧ EqOn f F A`, like Mathlib's
  `LipschitzOnWith.extend_real`, with `K = (…).toNNReal` for an explicit real constant. Avoid
  superfluous hypotheses such as `[Nonempty Y]` (use `exists_lipschitzWith_eqOn_of_nonempty`,
  `exists_lipschitzWith_eqOn_empty` and `exists_lipschitzWith_eqOn_of_subsingleton` for the
  trivial cases) and `0 ≤ c` when they follow from the other hypotheses.
* Internal results may use `∀ x y, dist (F x) (F y) ≤ K * dist x y` with `K : ℝ`;
  `LipschitzWith.of_dist_le'` converts to the `LipschitzWith` form.
* Pointwise Lipschitz constants: `LipAt f x L` means `limsup_{x' → x} d(f x, f x')/d(x, x') ≤ L`;
  `LipLowerLE f x C` is the lower version of Basso–Wenger–Young.
* Distances to sets: `Metric.infDist` (beware: it is `0` for the empty set).
* Cardinalities of possibly infinite sets: `Set.encard` (`Set.ncard` is `0` for infinite sets).
* Diameters of test sets: `Metric.ediam` (`Metric.diam` is `0` for unbounded sets).
* Sums over infinite index types: work with explicit `Finset`s (`finsum` is `0` for infinite
  support).
* Simplicial complexes for Theorem 1.3 live in `EuclideanSpace ℝ V` for a finite vertex type `V`
  (`Triangulation.face σ` is the simplex spanned by `σ : Finset V`, `PureComplex` a finite set of
  `n`-simplices); the complexes for Theorem 6.1 live in `ℓ₂(I)` for arbitrary `I`, modelled by
  finitely supported functions (`simplex σ`, `l2dist`).
* CAT(0) spaces follow Bridson–Haefliger (comparison triangles in `EuclideanSpace ℝ (Fin 2)`).
* `LC(K, λ)` for convex bodies is `LCBody K λ Y`; `LC(B^(m+1), λ)` is `LCBall m λ Y`.
* The absolute extendability constant `æ(X)` is `absLipExtConst X ∈ [0, ∞]`, with the ambient
  spaces and targets in fixed universes.

## Workflow for a new result

1. Write the definitions and the exact statements with `sorry` and check that they compile.
2. Review the statements against the source (hypotheses, constants, degenerate cases such as
   `A = ∅`, `n = 0`, empty targets).
3. Fill in the proofs, split into helper lemmas.
4. Add the result to the tables in `README.md` and the import to `LipschitzExtension.lean`.

Compile a single file with `lake env lean LipschitzExtension/<path>.lean` (its imports must be
built) and the whole library with `lake build`.

## Mathlib API notes (Mathlib `v4.35.0-rc3`)

* `Set.mem_setOf_eq` is deprecated; use `Set.mem_ofPred_eq`.
* `EMetric.diam` is now `Metric.ediam`.
* `Real.log_two_lt_d9`, `Real.exp_one_gt_d9`, … are in `Mathlib.Analysis.Complex.ExponentialBounds`.
* Avoid `import Mathlib` in library files; import the specific modules.
* `push_neg` is now `push Not`; `if_pos`/`if_neg` are deprecated (`ite_eq_left`, `ite_eq_right`),
  and so is `dif_pos` (`dite_eq_left`).
* Big-operator names use `finsetSum`: `continuous_finsetSum`, `integral_finsetSum_measure`,
  `Measure.finsetSum_apply`.
* Sections: a declaration only takes the section `variable`s mentioned in its header (use
  `include x in` otherwise); check new statements with `#check @name`.
* `EuclideanSpace.norm_single` is deprecated; use `PiLp.norm_single`.
* `(P1 X, W₁)` is a `MetricSpace` (`MeasureTheory/Wasserstein/Metric.lean`) with `dist = W1`
  definitionally (`P1.dist_eq_W1`); the sphere measure `sphereMeasure n` has `IsOpenPosMeasure`,
  so continuous functions that agree almost everywhere agree (`Continuous.ae_eq_iff_eq`).
* Unused automatically included instance variables (e.g. `[DecidableEq V]`) trigger the
  `unusedSectionVars` or `unusedDecidableInType` linters: use `omit [DecidableEq V] in`, or drop the
  binder from the statement and use `classical` in the proof.
* Riemannian manifolds: `open Bundle` is needed for the instances of `RiemannianBundle`;
  `IsRiemannianManifold.out`, `exists_lt_of_riemannianEDist_lt`, `riemannianEDist_le_pathELength`,
  `pathELength_add` relate the distance to lengths of `C¹` paths.
* Lengths of curves: `eVariationOn γ (Icc a b)`, additive via `eVariationOn.Icc_add_Icc`;
  `IsQuasiconvex`, `IsLengthSpace` and the BWY lemmas in
  `Topology/MetricSpace/PointwiseLipschitz/Lower.lean` and `Topology/MetricSpace/LengthSpace.lean`
  convert pointwise Lipschitz bounds into global ones.
* Convex bodies: `gauge`, `gauge_eq_one_iff_mem_frontier`; the radial projection `radialProj` and
  Vrecica's bound are in `Analysis/Convex/RadialProjection.lean`.
* Huge numerals such as `10 ^ (10 ^ 10)` must never be evaluated: abstract them with
  `generalize (10 : ℝ) ^ (10 ^ 10) = M` before calling `norm_num` or `simp`.
