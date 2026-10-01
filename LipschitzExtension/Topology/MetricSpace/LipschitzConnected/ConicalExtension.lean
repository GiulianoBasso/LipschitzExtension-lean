/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Bicombing.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Conical extensions

This file proves Lemma 7.4 of [Basso2024] on conical extensions. Let `σ` be a conical bicombing on
a metric space `Y`, let `p ∈ Y`, and let `f` be a map on the unit sphere `S` of a real inner
product space `E`. The *conical extension* of `f` with tip `p` is the map
`F(x) = σ(p, f(x/|x|), |x|)` on the closed unit ball, see (7.2) of [Basso2024]. Thus `F(0) = p`,
`F = f` on `S`, and `t ↦ F(t u)`, `t ∈ [0, 1]`, is the geodesic `σ(p, f(u), ·)` for `u ∈ S`.

**Lemma 7.4** of [Basso2024]: if `f` is `1`-Lipschitz on `S` and `d(p, f(x)) ≤ R` for all
`x ∈ S`, then `F` is `√(1 + R²)`-Lipschitz on the unit ball.

## Main definitions

* `conicalExtension σ p f`: the conical extension of `f` with tip `p`.

## Main statements

* `dist_conicalExtension_le`: Lemma 7.4 of [Basso2024] for `L`-Lipschitz maps `f`: the conical
  extension is `√(L² + R²)`-Lipschitz on the unit ball.
* `dist_conicalExtension_le_three_mul`: if the tip lies in `f(S)`, then the conical extension is
  `3 L`-Lipschitz (the remark before Lemma 7.4 of [Basso2024]).

## Implementation notes

We prove Lemma 7.4 for `L`-Lipschitz maps `f` (with the constant `√(L² + R²)`), so that no
rescaling of `Y` is needed in the proof of Proposition 7.3. Our proof is simpler than the proof
of the paper, which uses the law of cosines and the discriminant of a quadratic polynomial.

The equality case of Lemma 7.4 (for `Y = P₁(S^n)` and `f(x) = δ_x`) and Lemma 7.5 are proved in
`LipschitzExtension.Topology.MetricSpace.LipschitzConnected.Sharpness`.

## Proof outline

Let `x, y` be points of the unit ball with `r = |x| ≤ s = |y|` and `y ≠ 0`, and let `z = (r/s) y`.
By the conical inequality, `d(F x, F z) ≤ r · d(f(x/r), f(y/s)) ≤ L |x - z|`, and
`d(F z, F y) = (s - r) d(p, f(y/s)) ≤ R |z - y|`. Since
`⟨x - z, y - z⟩ = (s - r)(⟨x, y⟩/s - r) ≤ 0`, we have `|x - z|² + |z - y|² ≤ |x - y|²`, and the
Cauchy–Schwarz inequality gives `L |x - z| + R |z - y| ≤ √(L² + R²) · |x - y|`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open Metric Set

namespace LipschitzExtension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Y : Type*} [MetricSpace Y]

/-- The conical extension `F(x) = σ(p, f(x/|x|), |x|)` of a map `f` on the unit sphere, with tip
`F(0) = p`, see (7.2) of [Basso2024]. Only the values of `f` on the unit sphere matter. -/
noncomputable def conicalExtension (σ : ConicalBicombing Y) (p : Y) (f : E → Y) : E → Y :=
  fun x ↦ σ p (f (‖x‖⁻¹ • x)) ‖x‖

/-- The conical extension maps `0` to the tip `p`. -/
theorem conicalExtension_zero (σ : ConicalBicombing Y) (p : Y) (f : E → Y) :
    conicalExtension σ p f 0 = p := by
  simp only [conicalExtension, norm_zero]
  exact σ.toFun_zero _ _

/-- The conical extension of `f` agrees with `f` on the unit sphere. -/
theorem conicalExtension_eq_of_mem_sphere (σ : ConicalBicombing Y) (p : Y) (f : E → Y) {x : E}
    (hx : x ∈ sphere (0 : E) 1) : conicalExtension σ p f x = f x := by
  simp only [conicalExtension, mem_sphere_zero_iff_norm.1 hx, inv_one, one_smul]
  exact σ.toFun_one _ _

/-- Along the ray through `u ∈ S`, the conical extension is the geodesic from the tip:
`F(t u) = σ(p, f(u), t)` for `t ≥ 0`. -/
theorem conicalExtension_smul_of_mem_sphere (σ : ConicalBicombing Y) (p : Y) (f : E → Y)
    {u : E} (hu : u ∈ sphere (0 : E) 1) {t : ℝ} (ht : 0 ≤ t) :
    conicalExtension σ p f (t • u) = σ p (f u) t := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [zero_smul, conicalExtension_zero]
    exact (σ.toFun_zero _ _).symm
  · have hn : ‖t • u‖ = t := by
      rw [norm_smul_of_nonneg ht.le, mem_sphere_zero_iff_norm.1 hu, mul_one]
    simp only [conicalExtension, hn, inv_smul_smul₀ ht.ne']

/-- The Cauchy–Schwarz inequality in `ℝ²`: `L a + R b ≤ √(L² + R²) √(a² + b²)`. -/
private theorem mul_add_mul_le_sqrt_mul_sqrt (L R a b : ℝ) :
    L * a + R * b ≤ √(L ^ 2 + R ^ 2) * √(a ^ 2 + b ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  nlinarith [sq_nonneg (L * b - R * a)]

/-- If `‖u‖ = 1` and `‖x‖ = r ≤ s`, then `‖x - r u‖² + ‖r u - s u‖² ≤ ‖x - s u‖²`, since
`⟪x - r u, r u - s u⟫ = (s - r) (r - ⟪x, u⟫) ≥ 0`. -/
private theorem sq_norm_sub_add_sq_norm_sub_le {x u : E} {r s : ℝ} (hu : ‖u‖ = 1)
    (hx : ‖x‖ = r) (hrs : r ≤ s) :
    ‖x - r • u‖ ^ 2 + ‖r • u - s • u‖ ^ 2 ≤ ‖x - s • u‖ ^ 2 := by
  have h1 : x - s • u = (x - r • u) + (r • u - s • u) := by abel
  have h2 : inner ℝ (x - r • u) (r • u - s • u) = (s - r) * (r - inner ℝ x u) := by
    rw [← sub_smul, real_inner_smul_right, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hu]
    ring
  have h3 : inner ℝ x u ≤ r := by
    have h := real_inner_le_norm x u
    rwa [hx, hu, mul_one] at h
  have h4 : 0 ≤ (s - r) * (r - inner ℝ x u) := mul_nonneg (sub_nonneg.2 hrs) (sub_nonneg.2 h3)
  rw [h1, norm_add_sq_real, h2]
  linarith

/-- Comparison of `x` with the point `‖x‖ u` on the ray through `u ∈ S` (conical inequality):
`d(F x, F(‖x‖ u)) ≤ ‖x‖ d(f(x / ‖x‖), f u) ≤ L ‖x - ‖x‖ u‖`. -/
private theorem dist_conicalExtension_norm_smul_le (σ : ConicalBicombing Y) (p : Y) {f : E → Y}
    {L : ℝ}
    (hf : ∀ x ∈ sphere (0 : E) 1, ∀ y ∈ sphere (0 : E) 1, dist (f x) (f y) ≤ L * dist x y)
    {x u : E} (hx : x ∈ closedBall (0 : E) 1) (hu : u ∈ sphere (0 : E) 1) :
    dist (conicalExtension σ p f x) (conicalExtension σ p f (‖x‖ • u)) ≤
      L * ‖x - ‖x‖ • u‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hx' : ‖x‖⁻¹ • x ∈ sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  rw [conicalExtension_smul_of_mem_sphere σ p f hu hr.le]
  calc dist (σ p (f (‖x‖⁻¹ • x)) ‖x‖) (σ p (f u) ‖x‖)
      ≤ (1 - ‖x‖) * dist p p + ‖x‖ * dist (f (‖x‖⁻¹ • x)) (f u) :=
        σ.conical _ _ _ _ ⟨hr.le, mem_closedBall_zero_iff.1 hx⟩
    _ ≤ ‖x‖ * (L * dist (‖x‖⁻¹ • x) u) := by
        rw [dist_self, mul_zero, zero_add]
        exact mul_le_mul_of_nonneg_left (hf _ hx' _ hu) hr.le
    _ = L * ‖x - ‖x‖ • u‖ := by
        rw [dist_eq_norm, mul_left_comm, ← norm_smul_of_nonneg hr.le, smul_sub,
          smul_inv_smul₀ hr.ne']

/-- Comparison of two points on the ray through `u ∈ S` (geodesic from the tip):
`d(F(r u), F(s u)) = |r - s| d(p, f u) ≤ R ‖r u - s u‖`. -/
private theorem dist_conicalExtension_smul_smul_le (σ : ConicalBicombing Y) (p : Y) {f : E → Y}
    {R : ℝ} (hR : ∀ x ∈ sphere (0 : E) 1, dist p (f x) ≤ R) {u : E} (hu : u ∈ sphere (0 : E) 1)
    {r s : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    dist (conicalExtension σ p f (r • u)) (conicalExtension σ p f (s • u)) ≤
      R * ‖r • u - s • u‖ := by
  rw [conicalExtension_smul_of_mem_sphere σ p f hu hr.1,
    conicalExtension_smul_of_mem_sphere σ p f hu hs.1, σ.dist_toFun_toFun _ _ hr hs, ← sub_smul,
    norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.1 hu, mul_one, mul_comm R]
  exact mul_le_mul_of_nonneg_left (hR u hu) (abs_nonneg _)

/-- Lemma 7.4 for `y = s u` with `u ∈ S` and `‖x‖ ≤ s ≤ 1`, via the intermediate point
`z = ‖x‖ u`. -/
private theorem dist_conicalExtension_smul_le (σ : ConicalBicombing Y) (p : Y) {f : E → Y}
    {L R : ℝ}
    (hf : ∀ x ∈ sphere (0 : E) 1, ∀ y ∈ sphere (0 : E) 1, dist (f x) (f y) ≤ L * dist x y)
    (hR : ∀ x ∈ sphere (0 : E) 1, dist p (f x) ≤ R) {x u : E} {s : ℝ}
    (hx : x ∈ closedBall (0 : E) 1) (hu : u ∈ sphere (0 : E) 1) (hxs : ‖x‖ ≤ s) (hs : s ≤ 1) :
    dist (conicalExtension σ p f x) (conicalExtension σ p f (s • u)) ≤
      √(L ^ 2 + R ^ 2) * dist x (s • u) := by
  have h1 := dist_conicalExtension_norm_smul_le σ p hf hx hu
  have h2 := dist_conicalExtension_smul_smul_le σ p hR hu
    ⟨norm_nonneg x, mem_closedBall_zero_iff.1 hx⟩ ⟨(norm_nonneg x).trans hxs, hs⟩
  have h3 := sq_norm_sub_add_sq_norm_sub_le (mem_sphere_zero_iff_norm.1 hu) rfl hxs
  set F := conicalExtension σ p f
  calc dist (F x) (F (s • u)) ≤ dist (F x) (F (‖x‖ • u)) + dist (F (‖x‖ • u)) (F (s • u)) :=
        dist_triangle _ _ _
    _ ≤ L * ‖x - ‖x‖ • u‖ + R * ‖‖x‖ • u - s • u‖ := add_le_add h1 h2
    _ ≤ √(L ^ 2 + R ^ 2) * √(‖x - ‖x‖ • u‖ ^ 2 + ‖‖x‖ • u - s • u‖ ^ 2) :=
        mul_add_mul_le_sqrt_mul_sqrt _ _ _ _
    _ ≤ √(L ^ 2 + R ^ 2) * dist x (s • u) := by
        rw [dist_eq_norm]
        exact mul_le_mul_of_nonneg_left
          ((Real.sqrt_le_sqrt h3).trans_eq (Real.sqrt_sq (norm_nonneg _))) (Real.sqrt_nonneg _)

/-- Lemma 7.4 when `‖x‖ ≤ ‖y‖`. -/
private theorem dist_conicalExtension_le_of_norm_le (σ : ConicalBicombing Y) (p : Y) {f : E → Y}
    {L R : ℝ}
    (hf : ∀ x ∈ sphere (0 : E) 1, ∀ y ∈ sphere (0 : E) 1, dist (f x) (f y) ≤ L * dist x y)
    (hR : ∀ x ∈ sphere (0 : E) 1, dist p (f x) ≤ R) {x y : E} (hx : x ∈ closedBall (0 : E) 1)
    (hy : y ∈ closedBall (0 : E) 1) (hxy : ‖x‖ ≤ ‖y‖) :
    dist (conicalExtension σ p f x) (conicalExtension σ p f y) ≤ √(L ^ 2 + R ^ 2) * dist x y := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [norm_zero, norm_le_zero_iff] at hxy
    simp [hxy]
  have hs : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hu : ‖y‖⁻¹ • y ∈ sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
  have h := dist_conicalExtension_smul_le σ p hf hR hx hu hxy (mem_closedBall_zero_iff.1 hy)
  rwa [smul_inv_smul₀ hs.ne'] at h

/-- **Lemma 7.4** of [Basso2024] (for `L`-Lipschitz maps): the conical extension of an
`L`-Lipschitz map on the unit sphere whose values are within `R` of the tip `p` is
`√(L² + R²)`-Lipschitz on the closed unit ball. -/
theorem dist_conicalExtension_le (σ : ConicalBicombing Y) (p : Y) {f : E → Y} {L R : ℝ}
    (hf : ∀ x ∈ sphere (0 : E) 1, ∀ y ∈ sphere (0 : E) 1, dist (f x) (f y) ≤ L * dist x y)
    (hR : ∀ x ∈ sphere (0 : E) 1, dist p (f x) ≤ R) {x y : E} (hx : x ∈ closedBall (0 : E) 1)
    (hy : y ∈ closedBall (0 : E) 1) :
    dist (conicalExtension σ p f x) (conicalExtension σ p f y) ≤ √(L ^ 2 + R ^ 2) * dist x y := by
  rcases le_total ‖x‖ ‖y‖ with hxy | hxy
  · exact dist_conicalExtension_le_of_norm_le σ p hf hR hx hy hxy
  · rw [dist_comm, dist_comm x y]
    exact dist_conicalExtension_le_of_norm_le σ p hf hR hy hx hxy

/-- The remark before Lemma 7.4 of [Basso2024]: a conical extension whose tip lies in `f(S)` is
`3 L`-Lipschitz on the closed unit ball if `f` is `L`-Lipschitz on the unit sphere `S` (in fact
`√5 L`-Lipschitz, by Lemma 7.4 with `R = 2 L`). -/
theorem dist_conicalExtension_le_three_mul (σ : ConicalBicombing Y) {f : E → Y}
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ sphere (0 : E) 1, ∀ y ∈ sphere (0 : E) 1, dist (f x) (f y) ≤ L * dist x y)
    {q : E} (hq : q ∈ sphere (0 : E) 1) {x y : E} (hx : x ∈ closedBall (0 : E) 1)
    (hy : y ∈ closedBall (0 : E) 1) :
    dist (conicalExtension σ (f q) f x) (conicalExtension σ (f q) f y) ≤ 3 * L * dist x y := by
  have hR : ∀ z ∈ sphere (0 : E) 1, dist (f q) (f z) ≤ 2 * L := by
    intro z hz
    have hqz : dist q z ≤ 2 := by
      calc dist q z ≤ dist q 0 + dist 0 z := dist_triangle _ _ _
        _ = 2 := by
          rw [mem_sphere] at hq hz
          rw [hq, dist_comm, hz]
          norm_num
    calc dist (f q) (f z) ≤ L * dist q z := hf q hq z hz
      _ ≤ L * 2 := mul_le_mul_of_nonneg_left hqz hL
      _ = 2 * L := mul_comm _ _
  have key := dist_conicalExtension_le σ (f q) hf hR hx hy
  have h5 : √(L ^ 2 + (2 * L) ^ 2) ≤ 3 * L := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  exact key.trans (mul_le_mul_of_nonneg_right h5 dist_nonneg)

end LipschitzExtension
