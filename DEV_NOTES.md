# Development notes (for future sessions)

## Status (2026-09-30, after the sixth phase)

* Library `LipschitzExtension` complete for the paper *Lipschitz extension theorems with explicit
  constants* + errata Section 9: Theorems 1.1, 1.2 (now also for complete gNPC targets,
  `langSchlichenmaier_gNPC`), 1.4, 1.5, 2.4, 6.1 and all lemmas they need, plus BWY Lemma 2.4.
* Second phase (same day): Section 2 of *Extending and improving conical bicombings* (Enseign.
  Math. 70 (2024)): Lemma 2.5, Theorems 2.6 and 2.7 on `P₁(X)` (Radon = `InnerRegular`, `W₁` in
  Kantorovich–Rubinstein form), via Descombes' thesis Ch. 6 (Thm 6.1, Lemma 6.2, Prop 6.4,
  Thm 6.5) and Basso–Miesch Lemma 3.3. Files: `Bicombing/*`, `Wasserstein/*`,
  `Barycenter/{Uniform,Assignment,EsSahibHeinich,Hypergeometric,Descombes,Construction,
  Contracting}.lean`. Numbering of that paper: Prop 2.2, Lemma 2.3, Def 2.4, Lemma 2.5,
  Thm 2.6 (equivalence), Thm 2.7 (existence + convex hull property).
* Third phase: Proposition 7.3 (complete gNPC ⇒ `LC(B^(n+1), √(1 + c_n²))` and `LC(n, √3)`),
  Lemma 7.4 for `L`-Lipschitz maps (short proof via an obtuse angle + Cauchy–Schwarz), the
  normalized surface measure of `S^n` (`volume.toSphere`) and `c_n ≤ √2`. Files:
  `LangSchlichenmaier/{SphereMeasure,ConicalExtension,LipConnectedGNPC}.lean`.
* Fourth phase: the equality case of Lemma 7.4 and Lemma 7.5 (targets `P₁(S^n)`), for every
  conical bicombing on `P₁(S^n)` and `n ≥ 1`, plus the failure of Lemma 7.5 for `n = 0`. New:
  `(P₁(X), W₁)` is a metric space and has the linear conical bicombing (`Wasserstein/Metric.lean`);
  `ρ_n` has full support; the averaging identity `dist_toFun_dirac_sphere` (every conical
  bicombing on `P₁(S^n)` satisfies `W₁(σ(μ, δ_u, t), δ_w) = (1 - t) W₁(μ, δ_w) + t |u - w|`),
  which closes a gap in the paper's proof. File: `LangSchlichenmaier/ConicalExtensionSharp.lean`.
* Fifth phase: all remaining parts of *Lipschitz extension theorems with explicit constants*, so
  that every numbered result is formalized. Theorem 1.3 (errata items 3, 4; both constants
  `D N^(10 log n)` and `D² N^(10 log n)`) for length spaces and Riemannian manifolds (Mathlib's
  `IsRiemannianManifold`), with CAT(0) spaces (Bridson–Haefliger) and the Lang–Schroeder Kirszbraun
  theorem for inner product space domains (`CAT0/`), Lemmas 5.1, 5.2 (`Triangulation/`); Lemma 7.1
  with an own proof of Vrecica's bound (`RadialProjection.lean`, `ConvexBody.lean`), Lemma 7.2
  (`n²λ`), Lemma 8.2 (explicit two-segment path instead of Baader et al.), Proposition 8.1 with
  `λⁿ(√2)ⁿ⁻¹√n(n!)²` (`SimplexSharp.lean`, `SimplicialExtensorSharp.lean`), (1.2) with `10^14`
  (`GeneralSharp.lean`), `c₁ = 4/π`, `c₂ = 4/3` (`SphereConstants.lean`, cone formula for the
  sphere measure), λ₁, λ₂ and "`Lip F ≤ 3 Lip f`" (`LipConnectedConstants.lean`), Lemma 3.2 with
  `∑ Lip φᵢ` (`PartitionOfUnityPointwise.lean`), Proposition 8.4 with all three properties
  (`RefinedCover.lean`), Theorem 6.1 and Lemma 2.2 for length spaces (`Basic/LengthSpace.lean`,
  `GeneralWhitneyLength.lean`), `æ(X)` and (1.3) (`LeeNaor/AbsoluteExtendability.lean`), CAT(0) ⇒
  gNPC and Theorem 1.2 for CAT(0) targets (`CAT0/GNPC.lean`). `LCBall` moved to `LipConnected.lean`.
  Two new findings (README 9, 10). An independent statement audit found no discrepancies.
* Sixth phase (polish to Mathlib standards): Mathlib-like folder structure (`Topology/`,
  `Geometry/`, `Analysis/`, `MeasureTheory/`, `Combinatorics/`, and `Theorems/` with one file per
  main theorem; the file paths and names in the notes on the earlier phases above refer to the
  old layout, see the README "Layout" for the new one); Mathlib naming (main theorems `LipschitzOnWith.extend_<source>_<target>`,
  e.g. Theorem 1.1 = `LipschitzOnWith.extend_nagata_lipschitzConnected`); main theorems conclude
  `∃ F, LipschitzWith (…).toNNReal F ∧ EqOn f F A` and no longer assume `0 ≤ c`, `0 ≤ λ` or
  `[Nonempty Y]` (helpers in `Topology/EMetricSpace/Lipschitz.lean`); Apache 2.0 license
  (`LICENSE`, copyright headers "Giuliano Basso"), header linter on, `fun x ↦`, Mathlib-format
  module docstrings, `#lint` clean. The weaker self-contained versions of Proposition 8.1,
  Lemma 7.2 and Lemma 8.2 were removed (only the paper's constants remain); (1.1) is now derived
  from (1.2) (README finding 11: (1.2) is never worse than (1.1)). Theorem 6.1 is stated for
  length spaces only (normed spaces are length spaces). Equation numbers follow the paper
  (numbered within sections): the æ bound is (1.6), not (1.3). A scratch check showed that every
  old main statement follows from the new one.
* No `sorry`; only standard axioms (checked for all declarations); zero warnings with Mathlib's
  linter set including the header linter; `#lint in LipschitzExtension` passes. See `README.md`.
* Sources are stored in this project under `LipschitzExtension/…` (same layout as the repository;
  `.gitignore` is just `/.lake`, and `.github/workflows/` holds the three workflows of the official
  `lake new LipschitzExtension math` template, stored here under `LipschitzExtension/.github/…`).
* Toolchain: Lean/Mathlib `v4.35.0-rc3`. The `lakefile.toml` uses the template's `leanOptions`
  (`weak.linter.mathlibStandardSet = true`, `maxSynthPendingDepth = 3`) plus
  `autoImplicit = false`, and a `git` require for Mathlib.
* Delivered to the user as the zip `LipschitzExtension-lean.zip` (top folder
  `LipschitzExtension-lean`, ready for GitHub; no `.git`).

## Setting up the Cowork sandbox

`releases.lean-lang.org` is blocked, but GitHub and `cache.mathlib.org` work.

```
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
curl -sSL -o lean.tar.zst https://github.com/leanprover/lean4/releases/download/v4.35.0-rc3/lean-4.35.0-rc3-linux.tar.zst
zstd -dc lean.tar.zst | tar -x
elan toolchain link leanprover/lean4:v4.35.0-rc3 $PWD/lean-4.35.0-rc3-linux
# restore the project files, then in the project root:
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update   # clones Mathlib and dependencies
lake exe cache get                         # prebuilt Mathlib from cache.mathlib.org
lake build
```

Machine: 2 cores, 8 GB RAM. A compile of one file with analysis imports peaks at about 3 GB
(shared memory-mapped `.olean`s); never `import Mathlib` in full.

## Workflow that worked well

1. Write definitions and exact statements with `sorry`; build these skeletons (`lake build <module>`).
2. Give each file to a separate agent; agents compile only their file with
   `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true
   -DmaxSynthPendingDepth=3 <file>` (same options and linters as `lake build`; never `lake build`
   concurrently) and must not change statements.
   Pitfall: a `def`/`theorem` whose header does not mention a section `variable` does not take it
   as an argument (a skeleton `theorem isGNPC : IsGNPC X` silently dropped `σ`); check
   `#check @name` of every skeleton declaration.
3. Rebuild everything, `#print axioms` on the main theorems, independent statement audit.

Useful checks at the end of a phase: a script that extracts the statement text of every public
declaration before and after the agents' work (they must coincide), and `#print axioms` for all
public theorems (generated from the sources) with a filter for non-standard axioms.

## Next steps (see README "Roadmap")

Kirszbraun for Hilbert targets (inner product spaces are CAT(0)), the `√n` bound for finitely many
points, Johnson–Lindenstrauss–Schechtman, injective hulls (Theorem 1.1 of *Extending and improving
conical bicombings*).
