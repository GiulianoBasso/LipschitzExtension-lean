/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.ConicalExtension
import LipschitzExtension.MeasureTheory.Sphere.Basic
import LipschitzExtension.MeasureTheory.Wasserstein.Metric
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Module

/-!
# Sharpness of the constants for conical extensions

This file proves the equality case of Lemma 7.4 and Lemma 7.5 of [Basso2024], which show that for
`n ≥ 1` the constants `λ_n = √(1 + c_n²)` of Proposition 7.3 are optimal for conical extensions.
Throughout, `Y = (P₁(S^n), W₁)` is the `1`-Wasserstein space of the unit sphere
`S^n ⊆ ℝ^(n+1)` (with the Euclidean metric), `f(x) = δ_x` for `x ∈ S^n`, and `σ` is an arbitrary
conical bicombing on `P₁(S^n)`, for example the linear bicombing `(μ, ν, t) ↦ (1 - t) μ + t ν`
(`P1.linearBicombing`).

**Lemma 7.4** of [Basso2024], equality case: for `n ≥ 1`, the conical extension `F` of `f` with
tip `μ ∈ P₁(S^n)` satisfies `Lip F = √(1 + R²)`, where `R = sup_{z ∈ S^n} W₁(μ, δ_z)`.

**Lemma 7.5** of [Basso2024]: every conical extension `F` of `f` satisfies
`Lip F ≥ √(1 + c_n²)`.

## Main definitions

* `sphereP1 n`: the normalized surface measure `ρ_n` of `S^n` as an element of `P₁(S^n)`.

## Main statements

* `integral_dist_dirac_eq_sphereAvgDist`: `∫ W₁(ν, δ_z) dρ_n(z) = c_n` for every `ν ∈ P₁(S^n)`.
* `sphereAvgDist_le_iSup_dist_dirac`: `c_n ≤ sup_{z ∈ S^n} W₁(μ, δ_z)` for every `μ ∈ P₁(S^n)`.
* `dist_toFun_dirac_sphere`: the *averaging identity*: every conical bicombing `σ` on `P₁(S^n)`
  satisfies `W₁(σ(μ, δ_u, t), δ_w) = (1 - t) W₁(μ, δ_w) + t |u - w|` for all `μ ∈ P₁(S^n)`,
  `u, w ∈ S^n` and `t ∈ [0, 1]`, as the linear bicombing does.
* `isLeast_lipschitz_conicalExtension_dirac`: the equality case of Lemma 7.4 of [Basso2024]
  (`n ≥ 1`), for every conical bicombing and every tip.
* `sqrt_one_add_sphereAvgDist_sq_le`: Lemma 7.5 of [Basso2024] (`n ≥ 1`), for every conical
  bicombing and every tip.
* `isLeast_lipschitz_conicalExtension_sphereP1`: the bound of Lemma 7.5 is attained for the tip
  `ρ_n`.
* `sphereAvgDist_zero`, `exists_lipschitz_conicalExtension_dirac_lt_zero`,
  `not_forall_sqrt_one_add_sphereAvgDist_sq_le_zero`: Lemma 7.5 fails for `n = 0`. Indeed
  `c₀ = 1`, but the conical extension with tip `(δ₁ + δ₋₁)/2` for the linear bicombing is
  `1`-Lipschitz, and `1 < √2 = √(1 + c₀²)`.

## Implementation notes

In the equality case of Lemma 7.4 and in Lemma 7.5, `f` is any map `ℝ^(n+1) → P₁(S^n)` with
`f(x) = δ_x` for `x ∈ S^n` (only these values enter the conical extension), and the Lipschitz
constant `Lip F` on the closed unit ball `B^(n+1)` is expressed as the least `K` with
`d(F x, F y) ≤ K |x - y|` for `x, y ∈ B^(n+1)` (`IsLeast`).

*Remarks on the paper.* Lemma 7.5 is stated (for all `n`) for every conical extension, i.e. every
tip and every conical bicombing, and its proof applies the equality case of Lemma 7.4 to such an
extension. That equality case (stated for `n ≥ 1`) does not name a bicombing, but its proof
computes with the linear bicombing only. The averaging identity closes this gap, so both
statements hold for every conical bicombing when `n ≥ 1`. Lemma 7.5 is false for `n = 0`; there
the linear bicombing is the only conical bicombing, since `P₁(S⁰)` is isometric to the interval
`[0, 2]`.

## Proof outline

*The averaging identity.* The inequality `≤` is the conical inequality (compare with the constant
geodesic at `δ_w`). Both sides have the same average `c_n` over `w ∈ S^n` with respect to `ρ_n`,
because `∫ W₁(ν, δ_w) dρ_n(w) = c_n` for every `ν ∈ P₁(S^n)` by Fubini's theorem. Since `ρ_n` has
full support and both sides are continuous in `w`, they agree everywhere.

*The equality case of Lemma 7.4.* The upper bound is Lemma 7.4 (`dist_conicalExtension_le` with
`L = 1`). For the lower bound, let `ŷ ∈ S^n` with `W₁(μ, δ_ŷ) = R` (the maximum is attained since
`S^n` is compact), let `w ⊥ ŷ` be a unit vector (here `n ≥ 1` is used) and, for small `a > 0`,
let `x̂ = (1 - 2a²) ŷ + 2a √(1 - a²) w ∈ S^n`, so that `|x̂ - ŷ| = 2a`. Put `x = x̂ / 2` and
`y = (1/2 + R a) ŷ`. Comparing both `F(x)` and `F(y)` with `δ_ŷ` (averaging identity) gives
`W₁(F(x), F(y)) ≥ W₁(F(x), δ_ŷ) - W₁(F(y), δ_ŷ) = a R² + a = a (1 + R²)`, while
`|x - y| = a √(1 + R² + 2 R a)`. Letting `a → 0` gives `Lip F ≥ √(1 + R²)`. (The paper argues
through the exact value of `(s - r) R + r |x̂ - ŷ|` and a discriminant computation instead of this
explicit family of points.)

*Lemma 7.5.* As in the paper, integrating `W₁(μ, δ_z)` over `z ∈ S^n` with respect to `ρ_n` and
using Fubini's theorem gives `c_n ≤ R`, so the claim follows from the equality case of Lemma 7.4.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open MeasureTheory Metric Set

namespace LipschitzExtension

/-- The normalized surface measure `ρ_n` of `S^n` as an element of `P₁(S^n)`. -/
noncomputable def sphereP1 (n : ℕ) : P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) where
  toMeasure := sphereMeasure n
  isProbabilityMeasure := inferInstance
  innerRegular := by
    infer_instance
  exists_integrable_dist := by
    obtain ⟨q₀, hq₀⟩ :=
      (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin (n + 1)))) (r := 1)).2
        zero_le_one
    exact ⟨⟨q₀, hq₀⟩, (continuous_id.dist continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)⟩

/-- The underlying measure of `sphereP1 n` is `sphereMeasure n`. -/
theorem toMeasure_sphereP1 (n : ℕ) : (sphereP1 n).toMeasure = sphereMeasure n :=
  rfl

/-- `W₁(ρ_n, δ_z) = c_n` for every `z ∈ S^n`. -/
theorem dist_sphereP1_dirac (n : ℕ) (z : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    dist (sphereP1 n) (P1.dirac z) = sphereAvgDist n := by
  rw [P1.dist_eq_W1, P1.W1_dirac_right, toMeasure_sphereP1]
  exact integral_dist_eq_sphereAvgDist n z.2

/-- The unit sphere is nonempty. -/
private theorem nonempty_sphere (n : ℕ) :
    Nonempty (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ((NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin (n + 1))))).2
    zero_le_one).to_subtype

/-- `z ↦ W₁(μ, δ_z)` is continuous (`z ↦ δ_z` is an isometry). -/
private theorem continuous_dist_dirac (n : ℕ)
    (μ : P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    Continuous fun z : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦ dist μ (P1.dirac z) :=
  continuous_const.dist P1.isometry_dirac.continuous

/-- `z ↦ W₁(μ, δ_z)` is bounded above on the (compact) sphere. -/
private theorem bddAbove_dist_dirac (n : ℕ)
    (μ : P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    BddAbove (range fun z : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      dist μ (P1.dirac z)) :=
  (isCompact_range (continuous_dist_dirac n μ)).bddAbove

/-- `∫ W₁(ν, δ_z) dρ_n(z) = c_n` for every `ν ∈ P₁(S^n)`: by Fubini's theorem, since
`∫ |w - z| dρ_n(z) = c_n` for every `w ∈ S^n`. -/
theorem integral_dist_dirac_eq_sphereAvgDist (n : ℕ)
    (ν : P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    ∫ z, dist ν (P1.dirac z) ∂(sphereMeasure n) = sphereAvgDist n := by
  -- `(z, w) ↦ d(w, z)` is integrable on `S^n × S^n` (continuous on a compact space)
  have hint : Integrable
      (Function.uncurry fun z w : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦ dist w z)
      ((sphereMeasure n).prod ν.toMeasure) :=
    (continuous_snd.dist continuous_fst).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc ∫ z, dist ν (P1.dirac z) ∂(sphereMeasure n)
      = ∫ w, ∫ z, dist w z ∂(sphereMeasure n) ∂ν.toMeasure := by
        rw [← integral_integral_swap hint]
        simp_rw [P1.dist_eq_W1, P1.W1_dirac_right]
    _ = ∫ w, sphereAvgDist n ∂ν.toMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
        simp_rw [dist_comm w]
        exact integral_dist_eq_sphereAvgDist n w.2
    _ = sphereAvgDist n := by simp

/-- `c_n ≤ sup_{z ∈ S^n} W₁(μ, δ_z)` for every `μ ∈ P₁(S^n)`: integrate `W₁(μ, δ_z)` over `z` with
respect to `ρ_n` and use Fubini's theorem (the proof of Lemma 7.5 of [Basso2024]). -/
theorem sphereAvgDist_le_iSup_dist_dirac (n : ℕ)
    (μ : P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    sphereAvgDist n ≤
      ⨆ z : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, dist μ (P1.dirac z) := by
  rw [← integral_dist_dirac_eq_sphereAvgDist n μ]
  calc ∫ z, dist μ (P1.dirac z) ∂(sphereMeasure n)
      ≤ ∫ _z, ⨆ z, dist μ (P1.dirac z) ∂(sphereMeasure n) :=
        integral_mono ((continuous_dist_dirac n μ).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) (integrable_const _)
          fun z ↦ le_ciSup (bddAbove_dist_dirac n μ) z
    _ = ⨆ z, dist μ (P1.dirac z) := by simp

/-- **Averaging identity.** Every conical bicombing `σ` on `P₁(S^n)` satisfies
`W₁(σ(μ, δ_u, t), δ_w) = (1 - t) W₁(μ, δ_w) + t |u - w|` for all `u, w ∈ S^n` and `t ∈ [0, 1]`.
The inequality `≤` is the conical inequality against the constant geodesic at `δ_w`; both sides
have average `c_n` over `w` (`integral_dist_dirac_eq_sphereAvgDist`), and `ρ_n` has full
support. -/
theorem dist_toFun_dirac_sphere {n : ℕ}
    (σ : ConicalBicombing (P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))
    (μ : P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (u w : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (σ μ (P1.dirac u) t) (P1.dirac w) = (1 - t) * dist μ (P1.dirac w) + t * dist u w := by
  -- the defect `h ≥ 0` is continuous with integral `0`, hence identically `0`
  have hc : Continuous fun w : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      (1 - t) * dist μ (P1.dirac w) + t * dist u w - dist (σ μ (P1.dirac u) t) (P1.dirac w) :=
    ((continuous_const.mul (continuous_dist_dirac n μ)).add
      (continuous_const.mul (continuous_const.dist continuous_id))).sub
        (continuous_dist_dirac n _)
  have hnonneg : 0 ≤ fun w : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      (1 - t) * dist μ (P1.dirac w) + t * dist u w - dist (σ μ (P1.dirac u) t) (P1.dirac w) :=
    fun w ↦ by
      have h := σ.dist_toFun_le μ (P1.dirac u) (P1.dirac w) ht
      rw [P1.isometry_dirac.dist_eq] at h
      exact sub_nonneg.2 h
  have hint : ∫ w, ((1 - t) * dist μ (P1.dirac w) + t * dist u w -
      dist (σ μ (P1.dirac u) t) (P1.dirac w)) ∂(sphereMeasure n) = 0 := by
    have hi : ∀ g : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → ℝ, Continuous g →
        Integrable g (sphereMeasure n) := fun g hg ↦
      hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hu : ∫ w, dist u w ∂(sphereMeasure n) = sphereAvgDist n := by
      simp_rw [dist_comm u]
      exact integral_dist_eq_sphereAvgDist n u.2
    have i1 : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
        (1 - t) * dist μ (P1.dirac w)) (sphereMeasure n) :=
      hi _ (continuous_const.mul (continuous_dist_dirac n μ))
    have i2 : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
        t * dist u w) (sphereMeasure n) :=
      hi _ (continuous_const.mul (continuous_const.dist continuous_id))
    have i3 : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
        dist (σ μ (P1.dirac u) t) (P1.dirac w)) (sphereMeasure n) :=
      hi _ (continuous_dist_dirac n _)
    have i12 : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
        (1 - t) * dist μ (P1.dirac w) + t * dist u w) (sphereMeasure n) :=
      i1.add i2
    rw [integral_sub i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_dist_dirac_eq_sphereAvgDist, integral_dist_dirac_eq_sphereAvgDist, hu]
    ring
  have hzero := (hc.ae_eq_iff_eq (sphereMeasure n) continuous_zero).1
    ((integral_eq_zero_iff_of_nonneg hnonneg
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 hint)
  have h := congr_fun hzero w
  simp only [Pi.zero_apply] at h
  linarith

/-! ### The equality case of Lemma 7.4 -/

section EqualityCase

/-- Comparing both points with `δ_q`:
`W₁(σ(μ, δ_u, s), σ(μ, δ_q, t)) ≥ (t - s) W₁(μ, δ_q) + s d(u, q)`. -/
private theorem le_dist_toFun_dirac {n : ℕ}
    (σ : ConicalBicombing (P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))
    (μ : P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (u q : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (t - s) * dist μ (P1.dirac q) + s * dist u q ≤
      dist (σ μ (P1.dirac u) s) (σ μ (P1.dirac q) t) := by
  have h1 := dist_toFun_dirac_sphere σ μ u q hs
  have h2 := σ.dist_toFun_right μ (P1.dirac q) ht
  have h3 := dist_triangle (σ μ (P1.dirac u) s) (σ μ (P1.dirac q) t) (P1.dirac q)
  linarith

/-- Along the ray through `u ∈ S^n`, the conical extension of `f(x) = δ_x` is
`F(t u) = σ(μ, δ_u, t)`. -/
private theorem conicalExtension_dirac_smul {n : ℕ}
    (σ : ConicalBicombing (P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))
    (μ : P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    {f : EuclideanSpace ℝ (Fin (n + 1)) → P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)}
    (hf : ∀ x (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      f x = P1.dirac ⟨x, hx⟩) (u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) {t : ℝ}
    (ht : 0 ≤ t) :
    conicalExtension σ μ f (t • (u : EuclideanSpace ℝ (Fin (n + 1)))) = σ μ (P1.dirac u) t := by
  rw [conicalExtension_smul_of_mem_sphere _ _ _ u.2 ht, hf u u.2]

/-- For orthonormal `e, w`: `‖u e + v w‖² = u² + v²`. -/
private theorem norm_smul_add_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e w : E} (he : ‖e‖ = 1) (hw : ‖w‖ = 1) (hew : inner ℝ e w = 0) (u v : ℝ) :
    ‖u • e + v • w‖ ^ 2 = u ^ 2 + v ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hew,
    he, hw, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  ring

/-- For orthonormal `e, w`: `‖u e + v w‖ = √(u² + v²)`. -/
private theorem norm_smul_add_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e w : E} (he : ‖e‖ = 1) (hw : ‖w‖ = 1) (hew : inner ℝ e w = 0) (u v : ℝ) :
    ‖u • e + v • w‖ = √(u ^ 2 + v ^ 2) := by
  rw [← norm_smul_add_smul_sq he hw hew, Real.sqrt_sq (norm_nonneg _)]

/-- For `n ≥ 1`, every vector of `ℝ^(n+1)` is orthogonal to some unit vector (the orthogonal
complement of `ℝ y` has dimension at least `n`). -/
private theorem exists_norm_eq_one_inner_eq_zero {n : ℕ} (hn : 1 ≤ n)
    (y : EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ w : EuclideanSpace ℝ (Fin (n + 1)), ‖w‖ = 1 ∧ inner ℝ y w = 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · refine ⟨EuclideanSpace.single 0 1, by rw [PiLp.norm_single, norm_one], inner_zero_left _⟩
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have h := Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := n) hy
  have hne : (ℝ ∙ y)ᗮ ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at h
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨‖v‖⁻¹ • v, norm_smul_inv_norm hv0, ?_⟩
  rw [real_inner_smul_right, Submodule.mem_orthogonal_singleton_iff_inner_right.1 hv, mul_zero]

/-- The key estimate of the equality case: if `F` is `K`-Lipschitz on the ball, `y ∈ S^n`,
`R = W₁(μ, δ_y)`, `w ⊥ y` is a unit vector and `0 < a ≤ 1/(2(R + 1))`, then
`1 + R² ≤ K √(1 + R² + 2 a R)`. We test with the points `x = x̂ / 2` and `y' = (1/2 + R a) y` of
the ball, where `x̂ = (1 - 2a²) y + 2a √(1 - a²) w ∈ S^n`: then `|x̂ - y| = 2a`,
`|x - y'| = a √(1 + R² + 2 a R)` and `W₁(F x, F y') ≥ a (1 + R²)`. -/
private theorem one_add_sq_le_mul_sqrt {n : ℕ}
    (σ : ConicalBicombing (P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))
    (μ : P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    {f : EuclideanSpace ℝ (Fin (n + 1)) → P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)}
    (hf : ∀ x (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      f x = P1.dirac ⟨x, hx⟩) {K : ℝ}
    (hK : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        dist (conicalExtension σ μ f x)
          (conicalExtension σ μ f y) ≤ K * dist x y)
    (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) {w : EuclideanSpace ℝ (Fin (n + 1))}
    (hw : ‖w‖ = 1) (hyw : inner ℝ (y : EuclideanSpace ℝ (Fin (n + 1))) w = 0) {a : ℝ}
    (ha : 0 < a) (haR : 2 * a * (dist μ (P1.dirac y) + 1) ≤ 1) :
    1 + dist μ (P1.dirac y) ^ 2 ≤
      K * √(1 + dist μ (P1.dirac y) ^ 2 + 2 * a * dist μ (P1.dirac y)) := by
  set R := dist μ (P1.dirac y) with hRdef
  have hR0 : 0 ≤ R := dist_nonneg
  have hy1 : ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := mem_sphere_zero_iff_norm.1 y.2
  have ha1 : a ^ 2 ≤ 1 := by nlinarith
  have hRa : R * a ≤ 1 / 2 := by nlinarith
  set b := √(1 - a ^ 2) with hbdef
  have hb : b ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (by linarith)
  -- the point `u = x̂ ∈ S^n`, with `‖u - y‖ = 2a`
  set u : EuclideanSpace ℝ (Fin (n + 1)) := (1 - 2 * a ^ 2) • (y : _) + (2 * a * b) • w
    with hudef
  have hu : u ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    rw [mem_sphere_zero_iff_norm, hudef, norm_smul_add_smul hy1 hw hyw,
      show (1 - 2 * a ^ 2) ^ 2 + (2 * a * b) ^ 2 = 1 by linear_combination (4 * a ^ 2) * hb,
      Real.sqrt_one]
  have hdist : dist (⟨u, hu⟩ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) y = 2 * a := by
    rw [Subtype.dist_eq, dist_eq_norm,
      show u - y = (-(2 * a ^ 2)) • (y : EuclideanSpace ℝ (Fin (n + 1))) + (2 * a * b) • w by
        rw [hudef]; module,
      norm_smul_add_smul hy1 hw hyw,
      show (-(2 * a ^ 2)) ^ 2 + (2 * a * b) ^ 2 = (2 * a) ^ 2 by
        linear_combination (4 * a ^ 2) * hb,
      Real.sqrt_sq (by linarith)]
  -- the points `x = u / 2` and `y' = (1/2 + R a) y` of the ball
  have hs : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have ht : 1 / 2 + R * a ∈ Icc (0 : ℝ) 1 := ⟨by positivity, by linarith⟩
  have hxB : (1 / 2 : ℝ) • u ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, mem_sphere_zero_iff_norm.1 hu]
    norm_num
  have hyB : (1 / 2 + R * a) • (y : EuclideanSpace ℝ (Fin (n + 1))) ∈
      closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, hy1, mul_one, Real.norm_of_nonneg ht.1]
    exact ht.2
  have hxy : dist ((1 / 2 : ℝ) • u) ((1 / 2 + R * a) • (y : EuclideanSpace ℝ (Fin (n + 1)))) =
      a * √(1 + R ^ 2 + 2 * a * R) := by
    rw [dist_eq_norm,
      show (1 / 2 : ℝ) • u - (1 / 2 + R * a) • (y : EuclideanSpace ℝ (Fin (n + 1))) =
        (-(a ^ 2 + R * a)) • (y : EuclideanSpace ℝ (Fin (n + 1))) + (a * b) • w by
        rw [hudef]; module,
      norm_smul_add_smul hy1 hw hyw,
      show (-(a ^ 2 + R * a)) ^ 2 + (a * b) ^ 2 = a ^ 2 * (1 + R ^ 2 + 2 * a * R) by
        linear_combination a ^ 2 * hb,
      Real.sqrt_mul' _ (by positivity), Real.sqrt_sq ha.le]
  -- `F(x) = σ(μ, δ_u, 1/2)` and `F(y') = σ(μ, δ_y, 1/2 + R a)`
  have hup := hK _ hxB _ hyB
  rw [conicalExtension_dirac_smul σ μ hf ⟨u, hu⟩ hs.1, conicalExtension_dirac_smul σ μ hf y ht.1,
    hxy] at hup
  have hlow := le_dist_toFun_dirac σ μ ⟨u, hu⟩ y hs ht
  rw [hdist] at hlow
  -- hence `a (1 + R²) ≤ W₁(F x, F y') ≤ K a √(1 + R² + 2 a R)`
  have h : a * (1 + R ^ 2) ≤ a * (K * √(1 + R ^ 2 + 2 * a * R)) := by
    have h' : (1 / 2 + R * a - 1 / 2) * R + 1 / 2 * (2 * a) = a * (1 + R ^ 2) := by ring
    have h'' : K * (a * √(1 + R ^ 2 + 2 * a * R)) = a * (K * √(1 + R ^ 2 + 2 * a * R)) := by
      ring
    rw [← h', ← h'']
    exact hlow.trans hup
  exact le_of_mul_le_mul_left h ha

end EqualityCase

/-- **Lemma 7.4** of [Basso2024], equality case: for `Y = (P₁(S^n), W₁)` with `n ≥ 1`,
`f(x) = δ_x` on `S^n`, any conical bicombing `σ` on `P₁(S^n)` and any tip `μ ∈ P₁(S^n)`, the
conical extension `F` of `f` has Lipschitz constant exactly `√(1 + R²)` on `B^(n+1)`, where
`R = sup_{z ∈ S^n} W₁(μ, δ_z)`. -/
theorem isLeast_lipschitz_conicalExtension_dirac {n : ℕ} (hn : 1 ≤ n)
    (σ : ConicalBicombing (P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))
    (μ : P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    {f : EuclideanSpace ℝ (Fin (n + 1)) → P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)}
    (hf : ∀ x (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      f x = P1.dirac ⟨x, hx⟩) :
    IsLeast {K : ℝ | ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
          dist (conicalExtension σ μ f x)
            (conicalExtension σ μ f y) ≤ K * dist x y}
      (√(1 + (⨆ z : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        dist μ (P1.dirac z)) ^ 2)) := by
  constructor
  · -- the upper bound is Lemma 7.4 with `L = 1`
    intro x hx y hy
    have h1 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        ∀ y ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, dist (f x) (f y) ≤ 1 * dist x y :=
      fun x hx y hy ↦ by rw [hf x hx, hf y hy, P1.isometry_dirac.dist_eq, one_mul]; rfl
    have h2 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        dist μ (f x) ≤ ⨆ z : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
          dist μ (P1.dirac z) :=
      fun x hx ↦ by rw [hf x hx]; exact le_ciSup (bddAbove_dist_dirac n μ) ⟨x, hx⟩
    have h := dist_conicalExtension_le σ μ h1 h2 hx hy
    rwa [one_pow] at h
  · -- the lower bound: the supremum `R` is attained at some `y ∈ S^n`
    intro K hK
    have := nonempty_sphere n
    obtain ⟨y, -, hy⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
      (continuous_dist_dirac n μ).continuousOn
    have hR : (⨆ z : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, dist μ (P1.dirac z)) =
        dist μ (P1.dirac y) :=
      le_antisymm (ciSup_le fun z ↦ hy (mem_univ z)) (le_ciSup (bddAbove_dist_dirac n μ) y)
    rw [hR]
    set R := dist μ (P1.dirac y) with hRdef
    have hR0 : 0 ≤ R := dist_nonneg
    obtain ⟨w, hw, hyw⟩ := exists_norm_eq_one_inner_eq_zero hn (y : EuclideanSpace ℝ (Fin (n + 1)))
    -- let `a → 0⁺` in `1 + R² ≤ K √(1 + R² + 2 a R)`
    have hlim : 1 + R ^ 2 ≤ K * √(1 + R ^ 2) := by
      have hc : Continuous fun a : ℝ ↦ K * √(1 + R ^ 2 + 2 * a * R) := by fun_prop
      have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simp only [mul_zero, zero_mul, add_zero] at ht
      have hpos : (0 : ℝ) < 1 / (2 * (R + 1)) := by positivity
      refine ge_of_tendsto ht ?_
      filter_upwards [Ioo_mem_nhdsGT hpos] with a ha
      refine one_add_sq_le_mul_sqrt σ μ hf hK y hw hyw ha.1 ?_
      have h := ha.2
      rw [lt_div_iff₀ (by positivity)] at h
      linarith
    have hpos : 0 < √(1 + R ^ 2) := Real.sqrt_pos.2 (by positivity)
    refine le_of_mul_le_mul_right ?_ hpos
    rwa [Real.mul_self_sqrt (by positivity)]

/-- **Lemma 7.5** of [Basso2024]: for `n ≥ 1`, every conical extension `F` of `f(x) = δ_x` into
`P₁(S^n)` (for any conical bicombing `σ` and any tip `μ`) satisfies `Lip F ≥ √(1 + c_n²)`. -/
theorem sqrt_one_add_sphereAvgDist_sq_le {n : ℕ} (hn : 1 ≤ n)
    (σ : ConicalBicombing (P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))
    (μ : P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    {f : EuclideanSpace ℝ (Fin (n + 1)) → P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)}
    (hf : ∀ x (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      f x = P1.dirac ⟨x, hx⟩) {K : ℝ}
    (hK : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        dist (conicalExtension σ μ f x)
          (conicalExtension σ μ f y) ≤ K * dist x y) :
    √(1 + sphereAvgDist n ^ 2) ≤ K := by
  refine (Real.sqrt_le_sqrt ?_).trans ((isLeast_lipschitz_conicalExtension_dirac hn σ μ hf).2 hK)
  have h := pow_le_pow_left₀ (sphereAvgDist_nonneg n) (sphereAvgDist_le_iSup_dist_dirac n μ) 2
  linarith

/-- The bound of Lemma 7.5 of [Basso2024] is attained: for `n ≥ 1` and any conical bicombing, the
conical extension of `f(x) = δ_x` with tip `ρ_n` has Lipschitz constant exactly `√(1 + c_n²)`. -/
theorem isLeast_lipschitz_conicalExtension_sphereP1 {n : ℕ} (hn : 1 ≤ n)
    (σ : ConicalBicombing (P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))
    {f : EuclideanSpace ℝ (Fin (n + 1)) → P1 (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)}
    (hf : ∀ x (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      f x = P1.dirac ⟨x, hx⟩) :
    IsLeast {K : ℝ | ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
          dist (conicalExtension σ (sphereP1 n) f x)
            (conicalExtension σ (sphereP1 n) f y) ≤ K * dist x y}
      (√(1 + sphereAvgDist n ^ 2)) := by
  have := nonempty_sphere n
  have h := isLeast_lipschitz_conicalExtension_dirac hn σ (sphereP1 n) hf
  simp_rw [dist_sphereP1_dirac, ciSup_const] at h
  exact h

/-! ### The case `n = 0` -/

/-- In dimension one, `‖x‖ = |x 0|`. -/
private theorem norm_eq_abs_apply_zero (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

/-- In dimension one, `d(x, y) = |x 0 - y 0|`. -/
private theorem dist_eq_abs_sub_apply_zero (x y : EuclideanSpace ℝ (Fin 1)) :
    dist x y = |x 0 - y 0| := by
  rw [dist_eq_norm, norm_eq_abs_apply_zero, PiLp.sub_apply]

/-- A point of `S⁰ ⊆ ℝ¹` has coordinate `±1`. -/
private theorem apply_eq_one_or_neg_one_zero {x : EuclideanSpace ℝ (Fin 1)}
    (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) : x 0 = 1 ∨ x 0 = -1 := by
  rw [mem_sphere_zero_iff_norm, norm_eq_abs_apply_zero] at hx
  exact (abs_eq zero_le_one).1 hx

/-- The distance to a fixed point is integrable on `S⁰` (it is bounded by `1 + ‖q‖`). -/
private theorem integrable_dist_sphere_zero (q : EuclideanSpace ℝ (Fin (0 + 1))) :
    Integrable (fun x : sphere (0 : EuclideanSpace ℝ (Fin (0 + 1))) 1 ↦ dist x.1 q)
      (sphereMeasure 0) := by
  refine Integrable.of_bound (by fun_prop) (1 + ‖q‖) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, dist_eq_norm]
  calc ‖x.1 - q‖ ≤ ‖x.1‖ + ‖q‖ := norm_sub_le _ _
    _ = 1 + ‖q‖ := by rw [mem_sphere_zero_iff_norm.1 x.2]

/-- `c₀ = 1`: the average distance to a point of `S⁰ = {±1}`. -/
theorem sphereAvgDist_zero : sphereAvgDist 0 = 1 := by
  set e₀ : EuclideanSpace ℝ (Fin (0 + 1)) := EuclideanSpace.single 0 1 with he₀
  have hn : ‖e₀‖ = 1 := by rw [he₀, PiLp.norm_single, norm_one]
  have hme : e₀ ∈ sphere (0 : EuclideanSpace ℝ (Fin (0 + 1))) 1 :=
    mem_sphere_zero_iff_norm.2 hn
  have hme' : -e₀ ∈ sphere (0 : EuclideanSpace ℝ (Fin (0 + 1))) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_neg, hn]
  -- by symmetry, `2 c₀ = ∫ (‖x - e₀‖ + ‖x + e₀‖) dρ₀(x)` (as in `sphereAvgDist_le_sqrt_two`)
  have h2 : 2 * sphereAvgDist 0 = ∫ x, (dist x.1 e₀ + dist x.1 (-e₀)) ∂(sphereMeasure 0) := by
    rw [integral_add (integrable_dist_sphere_zero _) (integrable_dist_sphere_zero _),
      integral_dist_eq_sphereAvgDist 0 hme, integral_dist_eq_sphereAvgDist 0 hme', two_mul]
  -- and `‖x - e₀‖ + ‖x + e₀‖ = |x₀ - 1| + |x₀ + 1| = 2` for `x ∈ S⁰`, since `x₀ = ±1`
  have h3 : ∀ x : sphere (0 : EuclideanSpace ℝ (Fin (0 + 1))) 1,
      dist x.1 e₀ + dist x.1 (-e₀) = 2 := fun x ↦ by
    rw [dist_eq_abs_sub_apply_zero, dist_eq_abs_sub_apply_zero, PiLp.neg_apply, he₀,
      PiLp.single_eq_same]
    rcases apply_eq_one_or_neg_one_zero x.2 with hx | hx <;> rw [hx] <;> norm_num
  simp_rw [h3, integral_const, probReal_univ, one_smul] at h2
  linarith

/-- The point `e₀ = 1` of `S⁰`. -/
private noncomputable def ePlusZero : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  ⟨EuclideanSpace.single 0 1, by rw [mem_sphere_zero_iff_norm, PiLp.norm_single, norm_one]⟩

/-- The point `-e₀ = -1` of `S⁰`. -/
private noncomputable def eMinusZero : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  ⟨-EuclideanSpace.single 0 1, by
    rw [mem_sphere_zero_iff_norm, norm_neg, PiLp.norm_single, norm_one]⟩

private theorem ePlusZero_apply : (ePlusZero : EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
  simp [ePlusZero]

private theorem eMinusZero_apply : (eMinusZero : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
  simp [eMinusZero]

/-- Every function on `S⁰ = {±e₀}` is affine in the coordinate:
`g(z) = (g(e₀) + g(-e₀)) / 2 + z₀ (g(e₀) - g(-e₀)) / 2`. -/
private theorem apply_eq_average_zero (g : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 → ℝ)
    (z : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    g z = (g ePlusZero + g eMinusZero) / 2 +
      (z : EuclideanSpace ℝ (Fin 1)) 0 * (g ePlusZero - g eMinusZero) / 2 := by
  rcases apply_eq_one_or_neg_one_zero z.2 with h | h
  · have hz : z = ePlusZero :=
      Subtype.ext (PiLp.ext fun i ↦ by rw [Fin.fin_one_eq_zero i, h, ePlusZero_apply])
    rw [h, hz]
    ring
  · have hz : z = eMinusZero :=
      Subtype.ext (PiLp.ext fun i ↦ by rw [Fin.fin_one_eq_zero i, h, eMinusZero_apply])
    rw [h, hz]
    ring

/-- The tip `(δ_{e₀} + δ_{-e₀}) / 2 ∈ P₁(S⁰)`. -/
private noncomputable def tipZero : P1 (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  P1.convexComb (P1.dirac ePlusZero) (P1.dirac eMinusZero) ⟨1 / 2, by norm_num⟩

private theorem integral_dirac_sphere_zero (g : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 → ℝ)
    (z : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    ∫ w, g w ∂(P1.dirac z).toMeasure = g z :=
  integral_dirac g z

/-- `∫ g d((δ_{e₀} + δ_{-e₀}) / 2) = (g(e₀) + g(-e₀)) / 2`. -/
private theorem integral_tipZero {g : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 → ℝ}
    (hg : LipschitzWith 1 g) :
    ∫ z, g z ∂tipZero.toMeasure = (g ePlusZero + g eMinusZero) / 2 := by
  rw [tipZero, P1.integral_convexComb _ _ _ ((P1.dirac _).integrable_of_lipschitzWith hg)
    ((P1.dirac _).integrable_of_lipschitzWith hg), integral_dirac_sphere_zero,
    integral_dirac_sphere_zero]
  ring

/-- The pairing of the conical extension `F` (with tip `(δ_{e₀} + δ_{-e₀}) / 2`) with a
`1`-Lipschitz function `g` on `S⁰`: `∫ g dF(x) = (g(e₀) + g(-e₀)) / 2 + x₀ (g(e₀) - g(-e₀)) / 2`
(for `x ≠ 0`, `F(x) = (1 - ‖x‖) F(0) + ‖x‖ δ_{x / ‖x‖}` and `‖x‖ (x / ‖x‖)₀ = x₀`). -/
private theorem integral_conicalExtension_dirac_zero
    {f : EuclideanSpace ℝ (Fin 1) → P1 (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)}
    (hf : ∀ x (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1), f x = P1.dirac ⟨x, hx⟩)
    {g : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 → ℝ} (hg : LipschitzWith 1 g)
    {x : EuclideanSpace ℝ (Fin 1)} (hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    ∫ z, g z ∂(conicalExtension P1.linearBicombing tipZero f x).toMeasure =
      (g ePlusZero + g eMinusZero) / 2 + x 0 * (g ePlusZero - g eMinusZero) / 2 := by
  have hx1 : ‖x‖ ∈ Icc (0 : ℝ) 1 := ⟨norm_nonneg x, mem_closedBall_zero_iff.1 hx⟩
  have key : ‖x‖ * ∫ z, g z ∂(f (‖x‖⁻¹ • x)).toMeasure =
      ‖x‖ * ((g ePlusZero + g eMinusZero) / 2) + x 0 * ((g ePlusZero - g eMinusZero) / 2) := by
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have hr : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hu : ‖x‖⁻¹ • x ∈ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
      rw [hf _ hu, integral_dirac_sphere_zero, apply_eq_average_zero g]
      simp only [PiLp.smul_apply, smul_eq_mul]
      field_simp
  change ∫ z, g z ∂(P1.linearBicombing tipZero (f (‖x‖⁻¹ • x)) ‖x‖).toMeasure = _
  rw [P1.linearBicombing_apply _ _ hx1, P1.integral_convexComb _ _ _
    (tipZero.integrable_of_lipschitzWith hg) ((f _).integrable_of_lipschitzWith hg),
    integral_tipZero hg]
  linear_combination key

/-- **Lemma 7.5 of [Basso2024] fails for `n = 0`**: the conical extension of `f(x) = δ_x` into
`P₁(S⁰)` with tip `(δ₁ + δ₋₁)/2` for the linear bicombing is `K`-Lipschitz for some
`K < √(1 + c₀²)` (namely `K = 1`, while `√(1 + c₀²) = √2`). -/
theorem exists_lipschitz_conicalExtension_dirac_lt_zero :
    ∃ μ : P1 (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1), ∃ K < √(1 + sphereAvgDist 0 ^ 2),
      ∀ f : EuclideanSpace ℝ (Fin 1) → P1 (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1),
        (∀ x (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1), f x = P1.dirac ⟨x, hx⟩) →
        ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1,
          ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1,
            dist (conicalExtension P1.linearBicombing μ f x)
              (conicalExtension P1.linearBicombing μ f y) ≤ K * dist x y := by
  refine ⟨tipZero, 1, ?_, fun f hf x hx y hy ↦ ?_⟩
  · rw [sphereAvgDist_zero, Real.lt_sqrt zero_le_one]
    norm_num
  rw [one_mul, P1.dist_eq_W1]
  refine P1.W1_le fun g hg ↦ ?_
  rw [integral_conicalExtension_dirac_zero hf hg hx, integral_conicalExtension_dirac_zero hf hg hy,
    dist_eq_abs_sub_apply_zero]
  -- `|g(e₀) - g(-e₀)| ≤ d(e₀, -e₀) = 2`
  have h2 : |(g ePlusZero - g eMinusZero) / 2| ≤ 1 := by
    have h := hg.dist_le_mul ePlusZero eMinusZero
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Subtype.dist_eq, dist_eq_abs_sub_apply_zero,
      ePlusZero_apply, eMinusZero_apply] at h
    rw [abs_div, abs_two, div_le_one two_pos]
    norm_num at h
    exact h
  calc (g ePlusZero + g eMinusZero) / 2 + x 0 * (g ePlusZero - g eMinusZero) / 2 -
        ((g ePlusZero + g eMinusZero) / 2 + y 0 * (g ePlusZero - g eMinusZero) / 2)
      = (x 0 - y 0) * ((g ePlusZero - g eMinusZero) / 2) := by ring
    _ ≤ |(x 0 - y 0) * ((g ePlusZero - g eMinusZero) / 2)| := le_abs_self _
    _ = |x 0 - y 0| * |(g ePlusZero - g eMinusZero) / 2| := abs_mul _ _
    _ ≤ |x 0 - y 0| := mul_le_of_le_one_right (abs_nonneg _) h2

/-- **Lemma 7.5 of [Basso2024] needs `n ≥ 1`**: the statement of Lemma 7.5
(`sqrt_one_add_sphereAvgDist_sq_le`) is false for `n = 0`. -/
theorem not_forall_sqrt_one_add_sphereAvgDist_sq_le_zero :
    ¬ ∀ (σ : ConicalBicombing (P1 (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)))
        (μ : P1 (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1))
        (f : EuclideanSpace ℝ (Fin 1) → P1 (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)),
        (∀ x (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1), f x = P1.dirac ⟨x, hx⟩) →
        ∀ K : ℝ, (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1,
          ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1,
            dist (conicalExtension σ μ f x) (conicalExtension σ μ f y) ≤ K * dist x y) →
        √(1 + sphereAvgDist 0 ^ 2) ≤ K := by
  intro h
  obtain ⟨μ, K, hK, hlip⟩ := exists_lipschitz_conicalExtension_dirac_lt_zero
  classical
  let f : EuclideanSpace ℝ (Fin 1) → P1 (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    fun x ↦ if hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 then P1.dirac ⟨x, hx⟩ else μ
  have hf : ∀ x (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1), f x = P1.dirac ⟨x, hx⟩ :=
    fun x hx ↦ dite_eq_left hx
  exact absurd (h P1.linearBicombing μ f hf K (hlip f hf)) (not_le.2 hK)

end LipschitzExtension
