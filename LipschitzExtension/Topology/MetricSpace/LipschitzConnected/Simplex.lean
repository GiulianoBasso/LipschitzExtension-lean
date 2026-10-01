/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Geometry.SimplicialComplex.Basic
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.Defs
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.ConvexBody
import LipschitzExtension.Geometry.SimplicialComplex.Quasiconvex

/-!
# Lipschitz extensions from the boundary of a simplex

This file proves Lemmas 7.2 and 8.2 of [Basso2024] on extensions of maps from the boundary of a
simplex to the whole simplex. Let `Δⁿ ⊆ ℝ^(n+1)` be the standard `n`-simplex (see (7.1) of
[Basso2024]) with the Euclidean metric, and let `∂Δⁿ` be its boundary.

**Lemma 7.2** of [Basso2024]: if `Y` satisfies `LC(n - 1, λ)` for some `n ≥ 1`, then every
`L`-Lipschitz map `f : ∂Δⁿ → Y` admits an `n² λ L`-Lipschitz extension `F : Δⁿ → Y`.

**Lemma 8.2** of [Basso2024]: if `Y` satisfies `LC(n - 1, λ)` for some `n ≥ 2` and `f : ∂Δⁿ → Y`
is `L`-Lipschitz on every `(n - 1)`-face of `Δⁿ`, then `f` admits a
`√(2 + 2/(n - 1)) n² λ L`-Lipschitz extension `F : Δⁿ → Y`.

The proof of Lemma 8.2 in [Basso2024] quotes the upper bound of Baader, Studer and Züst for the
distortion of `∂Δⁿ`; we prove it here in the form that `∂Δⁿ` is `√(2 + 2/(n - 1))`-quasiconvex.
Finally, we transfer both lemmas to the simplices `simplex σ ⊆ ℓ₂(I)` of
`LipschitzExtension.Geometry.SimplicialComplex.Basic`, as needed for Proposition 8.1.

## Main definitions

* `SimplexExt.simplexE ι`, `SimplexExt.boundaryE ι`, `SimplexExt.bary ι`: the standard simplex in
  `EuclideanSpace ℝ ι`, its boundary and its barycenter; `Δⁿ = SimplexExt.simplexE (Fin (n + 1))`
  and `∂Δⁿ = SimplexExt.boundaryE (Fin (n + 1))`.
* `SimplexExt.restr σ`, `SimplexExt.liftE σ`: the restriction of `x : I →₀ ℝ` to `σ` and the
  extension by zero of `v : EuclideanSpace ℝ σ`, which identify `simplex σ` isometrically with
  `SimplexExt.simplexE σ`.

## Main statements

* `exists_extension_simplexE`: Lemma 7.2 of [Basso2024].
* `SimplexExt.exists_extension_euclid`: Lemma 7.2 for the standard simplex with `k + 1` vertices
  under `LC(B^k, λ)`, with one extension for all admissible Lipschitz constants.
* `SimplexExt.exists_mem_boundaryE_dist_add_dist_le`, `SimplexExt.isQuasiconvex_boundaryE`: the
  upper bound of Baader, Studer and Züst: for `n ≥ 2`, any two points of `∂Δⁿ` are joined in
  `∂Δⁿ` by a path with two segments whose length is at most `√(2 + 2/(n - 1))` times their
  distance.
* `SimplexExt.lipschitz_boundaryE_of_faces`: a map which is `L`-Lipschitz on every facet of `Δⁿ`,
  `n ≥ 2`, is `√(2 + 2/(n - 1)) L`-Lipschitz on `∂Δⁿ`.
* `exists_extension_simplexE_of_faces`: Lemma 8.2 of [Basso2024].
* `LipschitzConnected.exists_simplex_extension`: Lemma 7.2 for the simplices `simplex σ ⊆ ℓ₂(I)`
  used in the proof of Proposition 8.1 (`LipschitzConnected.simplicialExtensor`): under
  `LC(n, λ)`, the constant for a simplex with `k + 1` vertices, `1 ≤ k ≤ n + 1`, is `k² λ`.
* `lipschitz_simplexBoundary_of_faces`: the main step of Lemma 8.2 for these simplices: a map which
  is `L`-Lipschitz on every facet of a simplex with `k + 1 ≥ 3` vertices is
  `√(2 + 2/(k - 1)) L`-Lipschitz on its boundary.

## Proof outline

*Lemma 7.2.* We follow the paper. A simplex `Δ` with `k + 1` vertices lies in the affine
hyperplane `b + H₀`, where `b` is its barycenter and `H₀ = {v | ∑ v_i = 0}` is a `k`-dimensional
inner product space. The set `K = Δ - b ⊆ H₀` is a convex body with `0` in its interior, inradius
`r = 1/√(k(k+1))` and circumradius `R = √(k/(k+1))`, so that `(R/r)² = k²`. The frontier of `K` in
`H₀` is `∂Δ - b`: points with positive barycentric coordinates are interior points, and a point
`v` with a vanishing coordinate is the limit of the points `t v ∉ K` as `t → 1⁺`. Hence Lemma 7.1
(`LCBall.lcBody`, applied with `LC(B^k, λ)`) gives the claim. One extension works for all
admissible `L` simultaneously (`SimplexExt.exists_extension_euclid`): apply the lemma with the
optimal Lipschitz constant, which is attained.

*Lemma 8.2.* The paper combines the theorem of Baader, Studer and Züst (`∂Δⁿ` with its length
metric is `√(2 + 2/(n-1))`-bi-Lipschitz equivalent to `∂Δⁿ` with the Euclidean metric) with
Lemma 2.1 of [Basso2024] (Lemma 2.4 of Basso, Wenger and Young). We give a short explicit
argument instead (`SimplexExt.exists_mem_boundaryE_dist_add_dist_le`). Let `p, q ∈ ∂Δⁿ` with
`p_a = 0` and `q_b = 0`, where `a ≠ b` (if `a = b`, then `p` and `q` lie in a common facet). Put
`r_a = r_b = 0` and `r_i = (p_i + q_i)/2 + (p_b + q_a)/(2(n - 1))` for `i ≠ a, b`. Then `r ∈ Δⁿ`
lies in the facets `{x_a = 0}` and `{x_b = 0}`, and with `u_i = (p_i - q_i)/2`,
`U = ∑_{i ≠ a, b} u_i²` and `m = n - 1` we have
`|p - r|² + |r - q|² = p_b² + q_a² + 2U + (p_b + q_a)²/(2m)` and `|p - q|² = p_b² + q_a² + 4U`.
Hence `(|p - r| + |r - q|)² ≤ 2(|p - r|² + |r - q|²) ≤ (2 + 2/m) |p - q|²`, since
`(2 + 2/m)|p - q|² - 2(|p - r|² + |r - q|²) = (p_b - q_a)²/m + 4U(1 + 2/m) ≥ 0`.
Consequently `∂Δⁿ` is `√(2 + 2/(n-1))`-quasiconvex (the segments `[p, r]` and `[r, q]` lie in
facets), and a map which is `L`-Lipschitz on every facet is `√(2 + 2/(n-1)) L`-Lipschitz on `∂Δⁿ`
(compare `f(p)` and `f(q)` with `f(r)`). Lemma 8.2 now follows from Lemma 7.2.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* S. Baader, L. Studer and R. Züst, *Distortion of spheres and surfaces in space*, Q. J. Math. 71
  (2020), no. 3, 981–988
* G. Basso, S. Wenger and R. Young, *Undistorted fillings in subsets of metric spaces*, Adv. Math.
  423 (2023), Paper No. 109024
-/

open Set Metric Finset

namespace LipschitzExtension

namespace SimplexExt

/-! ### Geometry of the standard simplex in `EuclideanSpace ℝ ι` -/

section Euclid

variable {ι : Type*} [Fintype ι]

/-- The standard simplex `{v | 0 ≤ v i for all i, ∑ i, v i = 1}` in `EuclideanSpace ℝ ι`; for
`ι = Fin (n + 1)` this is `Δⁿ`, see (7.1) of [Basso2024]. -/
def simplexE (ι : Type*) [Fintype ι] : Set (EuclideanSpace ℝ ι) :=
  {v | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1}

/-- The boundary of the standard simplex in `EuclideanSpace ℝ ι`: the points of the simplex with
a vanishing coordinate, i.e. the union of its facets. -/
def boundaryE (ι : Type*) [Fintype ι] : Set (EuclideanSpace ℝ ι) :=
  {v | v ∈ simplexE ι ∧ ∃ i, v i = 0}

/-- The standard simplex is convex. -/
theorem convex_simplexE : Convex ℝ (simplexE ι) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i ↦ ?_, ?_⟩
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2]
    linarith

/-- The barycenter of the standard simplex, with all coordinates equal to `1 / #ι`. -/
noncomputable def bary (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun _ ↦ ((Fintype.card ι : ℝ))⁻¹

/-- All coordinates of the barycenter `SimplexExt.bary ι` are equal to `1 / #ι`. -/
@[simp] theorem bary_apply (i : ι) : bary ι i = (Fintype.card ι : ℝ)⁻¹ := rfl

/-- For `v` in the standard simplex, the coordinates of `v - bary ι` sum to `0`. -/
theorem sum_sub_bary {v : EuclideanSpace ℝ ι} (hv : v ∈ simplexE ι) [Nonempty ι] :
    ∑ i, (v - bary ι) i = 0 := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [PiLp.sub_apply, bary_apply, Finset.sum_sub_distrib, hv.2, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hN, sub_self]

end Euclid

/-! ### Transport between `I →₀ ℝ` and `EuclideanSpace ℝ σ` -/

section Transport

variable {I : Type*} (σ : Finset I)

/-- Restriction of a finitely supported function to `σ`. -/
noncomputable def restr (x : I →₀ ℝ) : EuclideanSpace ℝ σ :=
  WithLp.toLp 2 fun i : σ ↦ x i

open Classical in
/-- Extension by zero of a vector indexed by `σ`. -/
noncomputable def liftE (v : EuclideanSpace ℝ σ) : I →₀ ℝ :=
  Finsupp.onFinset σ (fun i ↦ if h : i ∈ σ then v ⟨i, h⟩ else 0) (by
    intro i hi
    by_contra h
    exact hi (dite_eq_right h))

/-- The extension by zero agrees with `v` on `σ`. -/
theorem liftE_apply_of_mem (v : EuclideanSpace ℝ σ) {i : I} (hi : i ∈ σ) :
    liftE σ v i = v ⟨i, hi⟩ := by
  rw [liftE, Finsupp.onFinset_apply, dite_eq_left hi]

/-- The extension by zero vanishes outside `σ`. -/
theorem liftE_apply_of_notMem (v : EuclideanSpace ℝ σ) {i : I} (hi : i ∉ σ) :
    liftE σ v i = 0 := by
  rw [liftE, Finsupp.onFinset_apply, dite_eq_right hi]

/-- The extension by zero of a vector indexed by `σ` is supported in `σ`. -/
theorem support_liftE (v : EuclideanSpace ℝ σ) : (↑(liftE σ v).support : Set I) ⊆ ↑σ := by
  intro i hi
  exact Finset.mem_coe.mpr (Finsupp.support_onFinset_subset (Finset.mem_coe.mp hi))

/-- `SimplexExt.restr σ` is a left inverse of `SimplexExt.liftE σ`. -/
theorem restr_liftE (v : EuclideanSpace ℝ σ) : restr σ (liftE σ v) = v := by
  ext i
  exact liftE_apply_of_mem σ v i.2

/-- `SimplexExt.liftE σ` is a left inverse of `SimplexExt.restr σ` on the functions supported in
`σ`. -/
theorem liftE_restr {x : I →₀ ℝ} (hx : (↑x.support : Set I) ⊆ ↑σ) :
    liftE σ (restr σ x) = x := by
  ext i
  by_cases hi : i ∈ σ
  · rw [liftE_apply_of_mem σ _ hi]
    rfl
  · rw [liftE_apply_of_notMem σ _ hi]
    by_contra h
    exact hi (hx (Finsupp.mem_support_iff.mpr (Ne.symm h)))

/-- The extension by zero is an isometry from `EuclideanSpace ℝ σ` to `I →₀ ℝ` with the `ℓ₂`
distance `l2dist`. -/
theorem l2dist_liftE (v w : EuclideanSpace ℝ σ) :
    l2dist (liftE σ v) (liftE σ w) = dist v w := by
  rw [l2dist_eq_dist_euclidean (support_liftE σ v) (support_liftE σ w)]
  exact congrArg₂ dist (restr_liftE σ v) (restr_liftE σ w)

/-- The restriction to `σ` maps `simplex σ` to the standard simplex `SimplexExt.simplexE σ`. -/
theorem restr_mem_simplexE {x : I →₀ ℝ} (hx : x ∈ simplex σ) : restr σ x ∈ simplexE σ := by
  refine ⟨fun i ↦ hx.1 i, ?_⟩
  change ∑ i : σ, x i = 1
  rw [Finset.sum_coe_sort σ (fun i ↦ x i)]
  exact hx.2.2

/-- The restriction to `σ` maps the boundary `simplexBoundary σ` to `SimplexExt.boundaryE σ`. -/
theorem restr_mem_boundaryE {x : I →₀ ℝ} (hx : x ∈ simplexBoundary σ) :
    restr σ x ∈ boundaryE σ := by
  obtain ⟨hx, i, hi, hxi⟩ := hx
  exact ⟨restr_mem_simplexE σ hx, ⟨i, hi⟩, hxi⟩

/-- The extension by zero maps `SimplexExt.boundaryE σ` to the boundary `simplexBoundary σ`. -/
theorem liftE_mem_simplexBoundary {v : EuclideanSpace ℝ σ} (hv : v ∈ boundaryE σ) :
    liftE σ v ∈ simplexBoundary σ := by
  obtain ⟨⟨h0, h1⟩, i, hi⟩ := hv
  refine ⟨⟨fun j ↦ ?_, support_liftE σ v, ?_⟩, i.1, i.2, ?_⟩
  · by_cases hj : j ∈ σ
    · rw [liftE_apply_of_mem σ v hj]
      exact h0 _
    · rw [liftE_apply_of_notMem σ v hj]
  · rw [← Finset.sum_coe_sort σ (fun j ↦ liftE σ v j)]
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ ↦ liftE_apply_of_mem σ v j.2
  · rw [liftE_apply_of_mem σ v i.2]
    exact hi

end Transport

variable {ι : Type*} [Fintype ι]

/-! ### The distortion of the boundary of a simplex (Baader, Studer and Züst) -/

/-- The squared Euclidean distance as a sum of squares. -/
private theorem dist_sq_eq_sum (x y : EuclideanSpace ℝ ι) :
    dist x y ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)]
  simp only [Real.dist_eq, sq_abs]

/-- Splitting a sum over `ι` at two distinct indices. -/
private theorem sum_eq_add_add_sum_erase [DecidableEq ι] {a b : ι} (hab : a ≠ b) (f : ι → ℝ) :
    ∑ i, f i = f a + f b + ∑ i ∈ (univ.erase a).erase b, f i := by
  rw [← Finset.add_sum_erase _ _ (mem_univ a),
    ← Finset.add_sum_erase _ _ (mem_erase.mpr ⟨Ne.symm hab, mem_univ b⟩), add_assoc]

/-- The algebraic core of Lemma 8.2: with `S = |p - r|² + |r - q|² - p_b² - q_a²` and
`W = |p - q|² - p_b² - q_a²`, we have `2 (|p - r|² + |r - q|²) ≤ (2 + 2/m) |p - q|²`. -/
private theorem two_mul_le_of_eq {m P Q W S : ℝ} (hm : 0 < m) (hW : 0 ≤ W)
    (hS : S = W / 2 + 2 * m * ((P + Q) / (2 * m)) ^ 2) :
    2 * (P ^ 2 + Q ^ 2 + S) ≤ (2 + 2 / m) * (P ^ 2 + Q ^ 2 + W) := by
  have e : (2 + 2 / m) * (P ^ 2 + Q ^ 2 + W) - 2 * (P ^ 2 + Q ^ 2 + S) =
      (P - Q) ^ 2 / m + W * (1 + 2 / m) := by
    rw [hS]
    field_simp
    ring
  have : 0 ≤ (P - Q) ^ 2 / m + W * (1 + 2 / m) := by positivity
  linarith

/-- The upper bound of Baader, Studer and Züst for the distortion of `∂Δⁿ`, the geometric part of
the proof of **Lemma 8.2** of [Basso2024]: two points `p, q` of the boundary of a simplex with
`n + 1` vertices, `n ≥ 2`, are joined through a point `r` of the simplex which shares a facet with
each of them (`p a = r a = 0` and `r b = q b = 0`), with
`|p - r| + |r - q| ≤ √(2 + 2/(n - 1)) |p - q|`. -/
theorem exists_mem_boundaryE_dist_add_dist_le {n : ℕ} (hι : Fintype.card ι = n + 1) (hn : 2 ≤ n)
    {p q : EuclideanSpace ℝ ι} (hp : p ∈ boundaryE ι) (hq : q ∈ boundaryE ι) :
    ∃ r ∈ simplexE ι, ∃ a b : ι, p a = 0 ∧ r a = 0 ∧ r b = 0 ∧ q b = 0 ∧
      dist p r + dist r q ≤ √(2 + 2 / ((n : ℝ) - 1)) * dist p q := by
  classical
  obtain ⟨⟨hp0, hp1⟩, a, hpa⟩ := hp
  obtain ⟨⟨hq0, hq1⟩, b, hqb⟩ := hq
  have hm : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hc1 : 1 ≤ √(2 + 2 / ((n : ℝ) - 1)) := by
    rw [Real.one_le_sqrt]
    have : 0 ≤ 2 / ((n : ℝ) - 1) := by positivity
    linarith
  by_cases hab : a = b
  · subst hab
    refine ⟨p, ⟨hp0, hp1⟩, a, a, hpa, hpa, hpa, hqb, ?_⟩
    rw [dist_self, zero_add]
    exact le_mul_of_one_le_left dist_nonneg hc1
  set m : ℝ := (n : ℝ) - 1 with hm_def
  set c : ℝ := (p b + q a) / (2 * m) with hc_def
  have hc0 : 0 ≤ c := div_nonneg (add_nonneg (hp0 b) (hq0 a)) (by positivity)
  set s : Finset ι := (univ.erase a).erase b with hs_def
  have hscard : (s.card : ℝ) = m := by
    rw [hs_def, card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hab, mem_univ b⟩),
      card_erase_of_mem (mem_univ a), card_univ, hι, show n + 1 - 1 - 1 = n - 1 by omega,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hsplit := fun f ↦ sum_eq_add_add_sum_erase (ι := ι) hab f
  -- the auxiliary point `r`
  let r : EuclideanSpace ℝ ι :=
    WithLp.toLp 2 fun i ↦ if i = a ∨ i = b then 0 else (p i + q i) / 2 + c
  have hra : r a = 0 := by simp [r]
  have hrb : r b = 0 := by simp [r]
  have hrs : ∀ i ∈ s, r i = (p i + q i) / 2 + c := by
    intro i hi
    have hib : i ≠ b := (mem_erase.mp hi).1
    have hia : i ≠ a := (mem_erase.mp (mem_erase.mp hi).2).1
    simp [r, hia, hib]
  have hps : ∑ i ∈ s, p i = 1 - p b := by
    have := hsplit fun i ↦ p i
    rw [hp1, hpa] at this
    linarith
  have hqs : ∑ i ∈ s, q i = 1 - q a := by
    have := hsplit fun i ↦ q i
    rw [hq1, hqb] at this
    linarith
  have hr : r ∈ simplexE ι := by
    refine ⟨fun i ↦ ?_, ?_⟩
    · by_cases hi : i = a ∨ i = b
      · simp [r, hi]
      · have e : r i = (p i + q i) / 2 + c := by simp [r, hi]
        have := hp0 i
        have := hq0 i
        rw [e]
        positivity
    · rw [hsplit fun i ↦ r i, hra, hrb, sum_congr rfl hrs, sum_add_distrib, ← sum_div,
        sum_add_distrib, hps, hqs, sum_const, nsmul_eq_mul, hscard, hc_def]
      field_simp
      ring
  refine ⟨r, hr, a, b, hpa, hra, hrb, hqb, ?_⟩
  -- the squared distances
  set W : ℝ := ∑ i ∈ s, (p i - q i) ^ 2 with hW_def
  have hW : 0 ≤ W := sum_nonneg fun i _ ↦ sq_nonneg _
  have hA : dist p r ^ 2 = p b ^ 2 + ∑ i ∈ s, (p i - r i) ^ 2 := by
    rw [dist_sq_eq_sum, hsplit fun i ↦ (p i - r i) ^ 2, hpa, hra, hrb]
    ring
  have hB : dist r q ^ 2 = q a ^ 2 + ∑ i ∈ s, (r i - q i) ^ 2 := by
    rw [dist_sq_eq_sum, hsplit fun i ↦ (r i - q i) ^ 2, hqb, hra, hrb]
    ring
  have hC : dist p q ^ 2 = p b ^ 2 + q a ^ 2 + W := by
    rw [dist_sq_eq_sum, hsplit fun i ↦ (p i - q i) ^ 2, hpa, hqb]
    ring
  have hS : ∑ i ∈ s, (p i - r i) ^ 2 + ∑ i ∈ s, (r i - q i) ^ 2 =
      W / 2 + 2 * m * ((p b + q a) / (2 * m)) ^ 2 := by
    have e : ∀ i ∈ s, (p i - r i) ^ 2 + (r i - q i) ^ 2 = (p i - q i) ^ 2 / 2 + 2 * c ^ 2 := by
      intro i hi
      rw [hrs i hi]
      ring
    rw [← sum_add_distrib, sum_congr rfl e, sum_add_distrib, ← sum_div, sum_const,
      nsmul_eq_mul, hscard, hc_def]
    ring
  have key := two_mul_le_of_eq hm hW hS
  have h2 : (dist p r + dist r q) ^ 2 ≤ (2 + 2 / m) * dist p q ^ 2 := by
    rw [hC]
    nlinarith [sq_nonneg (dist p r - dist r q)]
  rw [show √(2 + 2 / m) * dist p q = √((2 + 2 / m) * dist p q ^ 2) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq dist_nonneg]]
  exact Real.le_sqrt_of_sq_le h2

/-- A segment in the facet `{x a = 0}` of the simplex lies in the boundary. -/
private theorem lineMap_mem_boundaryE {p r : EuclideanSpace ℝ ι} {a : ι} (hp : p ∈ simplexE ι)
    (hr : r ∈ simplexE ι) (hpa : p a = 0) (hra : r a = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap p r t ∈ boundaryE ι := by
  refine ⟨convex_simplexE.lineMap_mem hp hr ht, a, ?_⟩
  simp [AffineMap.lineMap_apply_module, hpa, hra]

/-- The boundary of a simplex with `n + 1` vertices, `n ≥ 2`, is `√(2 + 2/(n - 1))`-quasiconvex
(the upper bound of Baader, Studer and Züst for the distortion of `∂Δⁿ`). -/
theorem isQuasiconvex_boundaryE {n : ℕ} (hι : Fintype.card ι = n + 1) (hn : 2 ≤ n) :
    IsQuasiconvex (√(2 + 2 / ((n : ℝ) - 1))) (boundaryE ι) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  obtain ⟨r, hr, a, b, hpa, hra, hrb, hqb, hle⟩ :=
    exists_mem_boundaryE_dist_add_dist_le hι hn hp hq
  -- the polygonal path `p, r, q`, whose segments lie in the facets `{x a = 0}`, `{x b = 0}`
  let P : ℕ → EuclideanSpace ℝ ι := fun i ↦ if i = 0 then p else if i = 1 then r else q
  obtain ⟨γ, hγc, hγ0, hγ1, hγC, hγv⟩ := exists_curve_of_polygonal
    (C := boundaryE ι) 2 P (by simpa [P] using hp) (by
      intro i hi t ht
      interval_cases i
      · simpa [P] using lineMap_mem_boundaryE hp.1 hr hpa hra ht
      · simpa [P] using lineMap_mem_boundaryE hr hq.1 hrb hqb ht)
  -- reparametrize `γ` on `ℝ` (constant outside `[0, 1]`) so that it takes values in `∂Δ`
  refine ⟨fun t ↦ ⟨γ (Set.projIcc (0 : ℝ) 1 zero_le_one t),
    hγC (Set.projIcc (0 : ℝ) 1 zero_le_one t).2⟩, ?_, ?_, ?_, ?_⟩
  · exact (Continuous.subtype_mk (hγc.comp (continuous_subtype_val.comp continuous_projIcc))
      _).continuousOn
  · ext
    simp [Set.projIcc_left, hγ0, P]
  · ext
    simp [Set.projIcc_right, hγ1, P]
  · have heq : eVariationOn (fun t ↦ (⟨γ (Set.projIcc (0 : ℝ) 1 zero_le_one t),
        hγC (Set.projIcc (0 : ℝ) 1 zero_le_one t).2⟩ : boundaryE ι)) (Icc 0 1) =
        eVariationOn γ (Icc 0 1) := by
      change eVariationOn (fun t ↦ γ (Set.projIcc (0 : ℝ) 1 zero_le_one t)) (Icc 0 1) = _
      exact eVariationOn.eq_of_eqOn fun t ht ↦ by rw [Set.projIcc_of_mem _ ht]
    rw [heq]
    refine hγv.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Subtype.dist_eq]
    simpa [Finset.sum_range_succ, P] using hle

/-- A map which is `L`-Lipschitz on every facet of a simplex with `n + 1` vertices, `n ≥ 2`, is
`√(2 + 2/(n - 1)) L`-Lipschitz on its boundary (the main step of the proof of Lemma 8.2 of
[Basso2024]). -/
theorem lipschitz_boundaryE_of_faces {Y : Type*} [PseudoMetricSpace Y] {n : ℕ}
    (hι : Fintype.card ι = n + 1) (hn : 2 ≤ n) {h : EuclideanSpace ℝ ι → Y} {L : ℝ} (hL : 0 ≤ L)
    (hface : ∀ i, ∀ x ∈ simplexE ι, x i = 0 → ∀ y ∈ simplexE ι, y i = 0 →
      dist (h x) (h y) ≤ L * dist x y) :
    ∀ x ∈ boundaryE ι, ∀ y ∈ boundaryE ι,
      dist (h x) (h y) ≤ √(2 + 2 / ((n : ℝ) - 1)) * L * dist x y := by
  intro x hx y hy
  obtain ⟨r, hr, a, b, hxa, hra, hrb, hyb, hle⟩ :=
    exists_mem_boundaryE_dist_add_dist_le hι hn hx hy
  calc dist (h x) (h y) ≤ dist (h x) (h r) + dist (h r) (h y) := dist_triangle _ _ _
    _ ≤ L * dist x r + L * dist r y :=
        add_le_add (hface a x hx.1 hxa r hr hra) (hface b r hr hrb y hy.1 hyb)
    _ = L * (dist x r + dist r y) := by ring
    _ ≤ L * (√(2 + 2 / ((n : ℝ) - 1)) * dist x y) := mul_le_mul_of_nonneg_left hle hL
    _ = √(2 + 2 / ((n : ℝ) - 1)) * L * dist x y := by ring

/-! ### Lemma 7.2 for the standard simplex -/

/-- The standard simplex is closed. -/
private theorem isClosed_simplexE : IsClosed (simplexE ι) := by
  have e : simplexE ι = (⋂ i, {v : EuclideanSpace ℝ ι | 0 ≤ v i}) ∩ {v | ∑ i, v i = 1} := by
    ext v
    simp [simplexE]
  rw [e]
  exact (isClosed_iInter fun i ↦ isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_eq (by fun_prop) continuous_const)

/-- Circumradius of the simplex: `‖y - b‖² ≤ 1 - 1/#ι` on `Δ`. -/
private theorem norm_sub_bary_sq_le {y : EuclideanSpace ℝ ι} (hy : y ∈ simplexE ι) :
    ‖y - bary ι‖ ^ 2 ≤ 1 - (Fintype.card ι : ℝ)⁻¹ := by
  obtain ⟨hy0, hy1⟩ := hy
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by
    intro h0
    rw [Nat.cast_eq_zero, Fintype.card_eq_zero_iff] at h0
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hy1
    exact zero_ne_one hy1
  have hle : ∀ i, y i ≤ 1 := fun i ↦ hy1 ▸ single_le_sum (fun j _ ↦ hy0 j) (mem_univ i)
  have e : ∀ i, ((y - bary ι) i) ^ 2 =
      y i ^ 2 + (-2 * (Fintype.card ι : ℝ)⁻¹) * y i + (Fintype.card ι : ℝ)⁻¹ ^ 2 := by
    intro i
    simp only [PiLp.sub_apply, bary_apply]
    ring
  have h2 : ∑ i, y i ^ 2 ≤ ∑ i, y i := sum_le_sum fun i _ ↦ by nlinarith [hy0 i, hle i]
  have hNc : (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)⁻¹ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    field_simp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [e, sum_add_distrib, ← mul_sum, hy1, sum_const, card_univ, nsmul_eq_mul, hNc]
  linarith

/-- Inradius of the simplex: `1/(k(k+1)) ≤ ‖y - b‖²` on `∂Δ`, `#ι = k + 1`. -/
private theorem inv_le_norm_sub_bary_sq {k : ℕ} (hι : Fintype.card ι = k + 1) (hk : 1 ≤ k)
    {y : EuclideanSpace ℝ ι} (hy : y ∈ boundaryE ι) :
    ((k : ℝ) * (k + 1))⁻¹ ≤ ‖y - bary ι‖ ^ 2 := by
  classical
  have : Nonempty ι := by
    rw [← Fintype.card_pos_iff, hι]
    omega
  obtain ⟨hyΔ, i, hyi⟩ := hy
  have hNk : (Fintype.card ι : ℝ) = k + 1 := by rw [hι]; push_cast; ring
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set x : EuclideanSpace ℝ ι := y - bary ι with hx
  have hxi : x i = -((k : ℝ) + 1)⁻¹ := by
    simp [x, hyi, hNk]
  have hsum : ∑ j, x j = 0 := sum_sub_bary hyΔ
  have hs1 := add_sum_erase univ (fun j ↦ x j) (mem_univ i)
  have hs2 := add_sum_erase univ (fun j ↦ x j ^ 2) (mem_univ i)
  have hcard : ((univ.erase i).card : ℝ) = k := by
    rw [card_erase_of_mem (mem_univ i), card_univ, hι, Nat.add_sub_cancel]
  rw [EuclideanSpace.real_norm_sq_eq, ← hs2]
  have hS : ∑ j ∈ univ.erase i, x j = ((k : ℝ) + 1)⁻¹ := by
    rw [hsum, hxi] at hs1
    linarith
  rw [hxi]
  set T := ∑ j ∈ univ.erase i, x j ^ 2
  -- `0 ≤ ∑_{j ≠ i} (x_j - d)²` with `d = (k+1)⁻¹/k` gives `T ≥ (k+1)⁻²/k`
  have hT : ((k : ℝ) + 1)⁻¹ ^ 2 / k ≤ T := by
    set d : ℝ := ((k : ℝ) + 1)⁻¹ / k with hd
    have h0 : 0 ≤ ∑ j ∈ univ.erase i, (x j - d) ^ 2 := sum_nonneg fun j _ ↦ sq_nonneg _
    have e : ∀ j, (x j - d) ^ 2 = x j ^ 2 + (-2 * d) * x j + d ^ 2 := fun j ↦ by ring
    simp only [e, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, hS, hcard] at h0
    have e2 : ((k : ℝ) + 1)⁻¹ ^ 2 / k = -((-2 * d) * ((k : ℝ) + 1)⁻¹ + k * d ^ 2) := by
      rw [hd]
      field_simp
      ring
    linarith
  calc ((k : ℝ) * (k + 1))⁻¹ = ((k : ℝ) + 1)⁻¹ ^ 2 + ((k : ℝ) + 1)⁻¹ ^ 2 / k := by
        field_simp
    _ ≤ (-((k : ℝ) + 1)⁻¹) ^ 2 + T := by rw [neg_sq]; linarith

open Filter Topology in
/-- **Lemma 7.2** of [Basso2024] for a fixed Lipschitz constant `L`, via Lemma 7.1 applied to the
convex body `K = Δ - b` in the hyperplane `H₀ = {v | ∑ v_i = 0}`. -/
private theorem exists_extension_euclid_fixed {Y : Type*} [MetricSpace Y] {k : ℕ}
    (hι : Fintype.card ι = k + 1) (hk : 1 ≤ k) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hY : LCBall (k - 1) Λ Y)
    (h' : EuclideanSpace ℝ ι → Y) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ v ∈ boundaryE ι, ∀ w ∈ boundaryE ι, dist (h' v) (h' w) ≤ L * dist v w) :
    ∃ F : EuclideanSpace ℝ ι → Y, (∀ v ∈ boundaryE ι, F v = h' v) ∧
      ∀ v ∈ simplexE ι, ∀ w ∈ simplexE ι, dist (F v) (F w) ≤ (k : ℝ) ^ 2 * Λ * L * dist v w := by
  classical
  have : Nonempty ι := by
    rw [← Fintype.card_pos_iff, hι]
    omega
  have hNk : (Fintype.card ι : ℝ) = k + 1 := by rw [hι]; push_cast; ring
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  -- the hyperplane `H₀ = {∑ v_i = 0}`
  let one : EuclideanSpace ℝ ι := WithLp.toLp 2 fun _ ↦ 1
  have hone : one ≠ 0 := by
    intro h0
    have := congrArg (fun v : EuclideanSpace ℝ ι ↦ v (Classical.arbitrary ι)) h0
    simp [one] at this
  let H₀ : Submodule ℝ (EuclideanSpace ℝ ι) := (Submodule.span ℝ {one})ᗮ
  have hmem : ∀ v, v ∈ H₀ ↔ ∑ i, v i = 0 := by
    intro v
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, PiLp.inner_apply]
    simp [one]
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ ι) = k + 1) := ⟨by simp [hι]⟩
  have hfin : Module.finrank ℝ H₀ = (k - 1) + 1 := by
    rw [Submodule.finrank_orthogonal_span_singleton (n := k) hone]
    omega
  -- the convex body `K = Δ - b ⊆ H₀`
  let K : Set H₀ := {v | bary ι + (v : EuclideanSpace ℝ ι) ∈ simplexE ι}
  have hKc : Convex ℝ K :=
    (convex_simplexE.translate_preimage_right (bary ι)).linear_preimage H₀.subtype
  have hKcl : IsClosed K :=
    isClosed_simplexE.preimage (continuous_const.add continuous_subtype_val)
  have hnormK : ∀ v ∈ K, ‖v‖ ^ 2 ≤ 1 - (Fintype.card ι : ℝ)⁻¹ := by
    intro v hv
    have := norm_sub_bary_sq_le hv
    rwa [add_sub_cancel_left] at this
  have hKK : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded hKcl (isBounded_iff_forall_norm_le.2 ⟨1, ?_⟩)
    intro v hv
    have h1 := hnormK v hv
    have h2 : 0 ≤ (Fintype.card ι : ℝ)⁻¹ := by positivity
    nlinarith [norm_nonneg v]
  -- points with positive barycentric coordinates are interior points
  have hint : ∀ v : H₀, (∀ i, 0 < (bary ι + (v : EuclideanSpace ℝ ι)) i) → v ∈ interior K := by
    intro v hv
    let U : Set H₀ := {w | ∀ i, 0 < (bary ι + (w : EuclideanSpace ℝ ι)) i}
    have hUo : IsOpen U := by
      have e : U = ⋂ i, {w : H₀ | 0 < (bary ι + (w : EuclideanSpace ℝ ι)) i} := by
        ext
        simp [U]
      rw [e]
      exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (by fun_prop)
    have hUK : U ⊆ K := by
      intro w hw
      refine ⟨fun i ↦ (hw i).le, ?_⟩
      simp only [PiLp.add_apply, sum_add_distrib, bary_apply, sum_const, card_univ, nsmul_eq_mul,
        (hmem _).1 w.2, add_zero]
      field_simp
    exact interior_maximal hUK hUo hv
  have h0 : (0 : H₀) ∈ interior K := hint 0 fun i ↦ by
    simp only [ZeroMemClass.coe_zero, add_zero, bary_apply]
    positivity
  -- the frontier of `K` is `∂Δ - b`
  have hfr : ∀ v : H₀, v ∈ frontier K ↔ bary ι + (v : EuclideanSpace ℝ ι) ∈ boundaryE ι := by
    intro v
    constructor
    · intro hv
      have hvK : v ∈ K := hKcl.frontier_subset hv
      refine ⟨hvK, ?_⟩
      by_contra hne
      exact hv.2 (hint v fun i ↦ lt_of_le_of_ne (hvK.1 i) (Ne.symm (not_exists.mp hne i)))
    · rintro ⟨hvK, i, hvi⟩
      refine ⟨subset_closure hvK, ?_⟩
      -- `t • v ∉ K` for `t > 1`
      rw [← mem_compl_iff, ← closure_compl]
      have htend : Tendsto (fun t : ℝ ↦ t • v) (𝓝[>] 1) (𝓝 v) := by
        have hc : Continuous fun t : ℝ ↦ t • v := continuous_id.smul continuous_const
        exact (hc.tendsto' 1 v (one_smul ℝ v)).mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto htend (eventually_nhdsWithin_of_forall fun t ht ↦ ?_)
      intro htK
      have h1 := htK.1 i
      have hvi' : (v : EuclideanSpace ℝ ι) i = -(Fintype.card ι : ℝ)⁻¹ := by
        simp only [PiLp.add_apply, bary_apply] at hvi
        linarith
      simp only [PiLp.add_apply, bary_apply, Submodule.coe_smul, PiLp.smul_apply, smul_eq_mul,
        hvi'] at h1
      have hc : 0 < (Fintype.card ι : ℝ)⁻¹ := by positivity
      have ht' : 1 < t := ht
      nlinarith
  -- inradius `r = 1/√(k(k+1))` and circumradius `R = k r = √(k/(k+1))`
  set r : ℝ := √(((k : ℝ) * (k + 1))⁻¹) with hr_def
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hrK : ∀ x ∈ frontier K, r ≤ ‖x‖ := by
    intro x hx
    have := inv_le_norm_sub_bary_sq hι hk ((hfr x).1 hx)
    rw [add_sub_cancel_left] at this
    exact Real.sqrt_le_iff.2 ⟨norm_nonneg _, this⟩
  have hRK : ∀ x ∈ frontier K, ‖x‖ ≤ k * r := by
    intro x hx
    have h1 := hnormK x (hKcl.frontier_subset hx)
    have h2 : (k * r) ^ 2 = 1 - (Fintype.card ι : ℝ)⁻¹ := by
      rw [mul_pow, hr_def, Real.sq_sqrt (by positivity), hNk]
      field_simp
      ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 (h2 ▸ h1)
  -- Lemma 7.1
  have hLC := LCBall.lcBody hfin hΛ hY hKc hKK h0 hr hrK hRK
  have hRr : ((k : ℝ) * r / r) ^ 2 * Λ = (k : ℝ) ^ 2 * Λ := by
    rw [mul_div_assoc, div_self hr.ne', mul_one]
  rw [hRr] at hLC
  obtain ⟨G, hGeq, hGlip⟩ := hLC L hL (fun v : H₀ ↦ h' (bary ι + (v : EuclideanSpace ℝ ι))) (by
    intro x hx y hy
    calc dist (h' (bary ι + (x : EuclideanSpace ℝ ι))) (h' (bary ι + (y : EuclideanSpace ℝ ι)))
        ≤ L * dist (bary ι + (x : EuclideanSpace ℝ ι)) (bary ι + (y : EuclideanSpace ℝ ι)) :=
          hLip _ ((hfr x).1 hx) _ ((hfr y).1 hy)
      _ = L * dist x y := by rw [dist_add_left, Subtype.dist_eq])
  refine ⟨fun x ↦ if hx : x - bary ι ∈ H₀ then G ⟨x - bary ι, hx⟩ else h' x, ?_, ?_⟩
  · intro v hv
    have hvH : v - bary ι ∈ H₀ := (hmem _).2 (sum_sub_bary hv.1)
    have hvf : (⟨v - bary ι, hvH⟩ : H₀) ∈ frontier K := (hfr _).2 (by simpa using hv)
    simp only [dite_eq_left hvH]
    rw [hGeq _ hvf]
    simp
  · intro v hv w hw
    have hvH : v - bary ι ∈ H₀ := (hmem _).2 (sum_sub_bary hv)
    have hwH : w - bary ι ∈ H₀ := (hmem _).2 (sum_sub_bary hw)
    simp only [dite_eq_left hvH, dite_eq_left hwH]
    calc _ ≤ (k : ℝ) ^ 2 * Λ * L * dist (⟨v - bary ι, hvH⟩ : H₀) ⟨w - bary ι, hwH⟩ :=
          hGlip _ (by simpa [K] using hv) _ (by simpa [K] using hw)
      _ = (k : ℝ) ^ 2 * Λ * L * dist v w := by rw [Subtype.dist_eq, dist_sub_right]

/-- **Lemma 7.2** of [Basso2024] (uniform version): if `#ι = k + 1` with `k ≥ 1`, `Λ ≥ 0` and `Y`
satisfies `LC(B^k, Λ)`, then every map `h'` agrees on `∂Δ` with a map `F` which is
`k² Λ L`-Lipschitz on `Δ` whenever `h'` is `L`-Lipschitz on `∂Δ`. -/
theorem exists_extension_euclid {Y : Type*} [MetricSpace Y] {k : ℕ}
    (hι : Fintype.card ι = k + 1) (hk : 1 ≤ k) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hY : LCBall (k - 1) Λ Y)
    (h' : EuclideanSpace ℝ ι → Y) :
    ∃ F : EuclideanSpace ℝ ι → Y, (∀ v ∈ boundaryE ι, F v = h' v) ∧
      ∀ L : ℝ, 0 ≤ L →
        (∀ v ∈ boundaryE ι, ∀ w ∈ boundaryE ι, dist (h' v) (h' w) ≤ L * dist v w) →
        ∀ v ∈ simplexE ι, ∀ w ∈ simplexE ι,
          dist (F v) (F w) ≤ (k : ℝ) ^ 2 * Λ * L * dist v w := by
  -- the set of admissible Lipschitz constants of `h'` on `∂Δ`
  set S : Set ℝ := {L | 0 ≤ L ∧ ∀ v ∈ boundaryE ι, ∀ w ∈ boundaryE ι,
    dist (h' v) (h' w) ≤ L * dist v w} with hS_def
  by_cases hS : S.Nonempty
  swap
  · exact ⟨h', fun _ _ ↦ rfl, fun L hL hLip ↦ absurd ⟨L, hL, hLip⟩ hS⟩
  -- the optimal Lipschitz constant `inf S` is admissible
  have hbdd : BddBelow S := ⟨0, fun L hL ↦ hL.1⟩
  have hL₀nn : 0 ≤ sInf S := le_csInf hS fun L hL ↦ hL.1
  have hL₀lip : ∀ v ∈ boundaryE ι, ∀ w ∈ boundaryE ι,
      dist (h' v) (h' w) ≤ sInf S * dist v w := by
    intro x hx y hy
    rcases (dist_nonneg : 0 ≤ dist x y).eq_or_lt with hd | hd
    · obtain ⟨L, hL⟩ := hS
      have := hL.2 x hx y hy
      rw [← hd, mul_zero] at this ⊢
      exact this
    · rw [← div_le_iff₀ hd]
      exact le_csInf hS fun L hL ↦ (div_le_iff₀ hd).mpr (hL.2 x hx y hy)
  obtain ⟨F, hFeq, hFlip⟩ := exists_extension_euclid_fixed hι hk hΛ hY h' hL₀nn hL₀lip
  refine ⟨F, hFeq, fun L hL hLip v hv w hw ↦ (hFlip v hv w hw).trans ?_⟩
  have hle : sInf S ≤ L := csInf_le hbdd ⟨hL, hLip⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hle (mul_nonneg (sq_nonneg _) hΛ)) dist_nonneg

end SimplexExt

/-! ### Lemmas 7.2 and 8.2 for `Δⁿ` -/

/-- `LC(B^(m+1), Λ)` for a nonempty space forces `0 ≤ Λ` (extend a constant map). -/
private theorem lcBall_nonneg {Y : Type*} [PseudoMetricSpace Y] {m : ℕ} {Λ : ℝ}
    (hY : LCBall m Λ Y) (y : Y) : 0 ≤ Λ := by
  obtain ⟨G, -, hGlip⟩ := hY 1 zero_le_one (fun _ ↦ y) fun x _ z _ ↦ by
    rw [dist_self]
    positivity
  obtain ⟨u, hu⟩ : (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).Nonempty :=
    NormedSpace.sphere_nonempty.2 zero_le_one
  have h := hGlip u (sphere_subset_closedBall hu) 0 (mem_closedBall_self zero_le_one)
  rw [dist_zero_right, mem_sphere_zero_iff_norm.1 hu, mul_one, mul_one] at h
  exact dist_nonneg.trans h

/-- **Lemma 7.2** of [Basso2024]: if `Y` satisfies `LC(n - 1, Λ)` for some `n ≥ 1`, then every
`L`-Lipschitz map on `∂Δⁿ` admits an `n² Λ L`-Lipschitz extension to `Δⁿ`. -/
theorem exists_extension_simplexE {Y : Type*} [MetricSpace Y] {n : ℕ} (hn : 1 ≤ n) {Λ : ℝ}
    (hY : LipschitzConnected (n - 1) Λ Y) {L : ℝ} (hL : 0 ≤ L)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → Y}
    (hf : ∀ x ∈ SimplexExt.boundaryE (Fin (n + 1)), ∀ y ∈ SimplexExt.boundaryE (Fin (n + 1)),
      dist (f x) (f y) ≤ L * dist x y) :
    ∃ F : EuclideanSpace ℝ (Fin (n + 1)) → Y,
      (∀ x ∈ SimplexExt.boundaryE (Fin (n + 1)), F x = f x) ∧
      ∀ x ∈ SimplexExt.simplexE (Fin (n + 1)), ∀ y ∈ SimplexExt.simplexE (Fin (n + 1)),
        dist (F x) (F y) ≤ (n : ℝ) ^ 2 * Λ * L * dist x y := by
  have hB : LCBall (n - 1) Λ Y := hY (n - 1) le_rfl
  have hΛ : 0 ≤ Λ := lcBall_nonneg hB (f 0)
  obtain ⟨F, hFeq, hFlip⟩ :=
    SimplexExt.exists_extension_euclid (Fintype.card_fin (n + 1)) hn hΛ hB f
  exact ⟨F, hFeq, hFlip L hL hf⟩

/-- **Lemma 8.2** of [Basso2024]: if `Y` satisfies `LC(n - 1, Λ)` for some `n ≥ 2`, then every map
`f : ∂Δⁿ → Y` which is `L`-Lipschitz on every `(n - 1)`-face of `Δⁿ` admits a
`√(2 + 2/(n - 1)) n² Λ L`-Lipschitz extension to `Δⁿ`. -/
theorem exists_extension_simplexE_of_faces {Y : Type*} [MetricSpace Y] {n : ℕ} (hn : 2 ≤ n)
    {Λ : ℝ} (hY : LipschitzConnected (n - 1) Λ Y) {L : ℝ} (hL : 0 ≤ L)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → Y}
    (hf : ∀ i, ∀ x ∈ SimplexExt.simplexE (Fin (n + 1)), x i = 0 →
      ∀ y ∈ SimplexExt.simplexE (Fin (n + 1)), y i = 0 → dist (f x) (f y) ≤ L * dist x y) :
    ∃ F : EuclideanSpace ℝ (Fin (n + 1)) → Y,
      (∀ x ∈ SimplexExt.boundaryE (Fin (n + 1)), F x = f x) ∧
      ∀ x ∈ SimplexExt.simplexE (Fin (n + 1)), ∀ y ∈ SimplexExt.simplexE (Fin (n + 1)),
        dist (F x) (F y) ≤ √(2 + 2 / ((n : ℝ) - 1)) * (n : ℝ) ^ 2 * Λ * L * dist x y := by
  have hbd := SimplexExt.lipschitz_boundaryE_of_faces (Fintype.card_fin (n + 1)) hn hL hf
  obtain ⟨F, hFeq, hFlip⟩ := exists_extension_simplexE (by omega : 1 ≤ n) hY
    (mul_nonneg (Real.sqrt_nonneg _) hL) hbd
  refine ⟨F, hFeq, fun x hx y hy ↦ ?_⟩
  calc dist (F x) (F y) ≤ (n : ℝ) ^ 2 * Λ * (√(2 + 2 / ((n : ℝ) - 1)) * L) * dist x y :=
        hFlip x hx y hy
    _ = √(2 + 2 / ((n : ℝ) - 1)) * (n : ℝ) ^ 2 * Λ * L * dist x y := by ring

/-! ### Simplices in `ℓ₂(I)` -/

/-- **Lemma 7.2** of [Basso2024] for the simplices `simplex σ ⊆ ℓ₂(I)`, uniformly in `L`: if `Y`
satisfies `LC(n, Λ)` with `Λ ≥ 0` and `σ` has `k + 1` elements with `1 ≤ k ≤ n + 1`, then every
map `h` agrees on `∂σ` with a map `G` which is `k² Λ L`-Lipschitz on `simplex σ` (for `l2dist`)
whenever `h` is `L`-Lipschitz on `∂σ`. -/
theorem LipschitzConnected.exists_simplex_extension {Y : Type*} [MetricSpace Y] {n : ℕ} {Λ : ℝ}
    (hY : LipschitzConnected n Λ Y) (hΛ : 0 ≤ Λ) {I : Type*} {σ : Finset I} {k : ℕ}
    (hk : 1 ≤ k) (hkn : k - 1 ≤ n) (hσ : σ.card = k + 1) (h : (I →₀ ℝ) → Y) :
    ∃ G : (I →₀ ℝ) → Y, (∀ x ∈ simplexBoundary σ, G x = h x) ∧
      ∀ L : ℝ, 0 ≤ L →
        (∀ x ∈ simplexBoundary σ, ∀ y ∈ simplexBoundary σ, dist (h x) (h y) ≤ L * l2dist x y) →
        ∀ x ∈ simplex σ, ∀ y ∈ simplex σ,
          dist (G x) (G y) ≤ (k : ℝ) ^ 2 * Λ * L * l2dist x y := by
  have hcard : Fintype.card σ = k + 1 := by rw [Fintype.card_coe]; exact hσ
  obtain ⟨F, hFb, hFlip⟩ := SimplexExt.exists_extension_euclid hcard hk hΛ (hY (k - 1) hkn)
    (fun v ↦ h (SimplexExt.liftE σ v))
  refine ⟨fun x ↦ F (SimplexExt.restr σ x), ?_, ?_⟩
  · intro x hx
    change F (SimplexExt.restr σ x) = h x
    rw [hFb _ (SimplexExt.restr_mem_boundaryE σ hx), SimplexExt.liftE_restr σ hx.1.2.1]
  · intro L hL hLip x hx y hy
    have hLip' : ∀ v ∈ SimplexExt.boundaryE σ, ∀ w ∈ SimplexExt.boundaryE σ,
        dist (h (SimplexExt.liftE σ v)) (h (SimplexExt.liftE σ w)) ≤ L * dist v w := by
      intro v hv w hw
      rw [← SimplexExt.l2dist_liftE σ v w]
      exact hLip _ (SimplexExt.liftE_mem_simplexBoundary σ hv) _
        (SimplexExt.liftE_mem_simplexBoundary σ hw)
    rw [l2dist_eq_dist_euclidean hx.2.1 hy.2.1]
    exact hFlip L hL hLip' _ (SimplexExt.restr_mem_simplexE σ hx) _
      (SimplexExt.restr_mem_simplexE σ hy)

/-- A point of `simplex σ` whose coordinate `a` vanishes lies in the facet
`simplex (σ.erase a)`. -/
private theorem mem_simplex_erase_of_eq_zero {I : Type*} [DecidableEq I] {σ : Finset I}
    {x : I →₀ ℝ} {a : I} (hx : x ∈ simplex σ) (ha : x a = 0) : x ∈ simplex (σ.erase a) := by
  obtain ⟨hx0, hxs, hx1⟩ := hx
  refine ⟨hx0, fun i hi ↦ ?_, ?_⟩
  · rw [Finset.coe_erase]
    refine ⟨hxs hi, fun hia ↦ ?_⟩
    rw [Set.mem_singleton_iff] at hia
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hia] at hi
    exact hi ha
  · rw [Finset.sum_erase σ ha]
    exact hx1

/-- The extension by zero of a point of the standard simplex `Δ ⊆ EuclideanSpace ℝ σ` lies in
`simplex σ`. -/
private theorem liftE_mem_simplex {I : Type*} (σ : Finset I) {v : EuclideanSpace ℝ σ}
    (hv : v ∈ SimplexExt.simplexE σ) : SimplexExt.liftE σ v ∈ simplex σ := by
  obtain ⟨h0, h1⟩ := hv
  refine ⟨fun j ↦ ?_, SimplexExt.support_liftE σ v, ?_⟩
  · by_cases hj : j ∈ σ
    · rw [SimplexExt.liftE_apply_of_mem σ v hj]
      exact h0 _
    · rw [SimplexExt.liftE_apply_of_notMem σ v hj]
  · rw [← Finset.sum_coe_sort σ (fun j ↦ SimplexExt.liftE σ v j), ← h1]
    exact Finset.sum_congr rfl fun j _ ↦ SimplexExt.liftE_apply_of_mem σ v j.2

/-- The main step of **Lemma 8.2** of [Basso2024] for the simplices `simplex σ ⊆ ℓ₂(I)`: a map
which is `L`-Lipschitz on every facet `simplex τ`, `τ ⊆ σ` with `#τ + 1 = #σ`, of a simplex with
`k + 1 ≥ 3` vertices is `√(2 + 2/(k - 1)) L`-Lipschitz on its boundary `∂σ`. -/
theorem lipschitz_simplexBoundary_of_faces {Y : Type*} [PseudoMetricSpace Y] {I : Type*}
    {σ : Finset I} {k : ℕ} (hk : 2 ≤ k) (hσ : σ.card = k + 1) {h : (I →₀ ℝ) → Y} {L : ℝ}
    (hL : 0 ≤ L)
    (hface : ∀ τ ⊆ σ, τ.card + 1 = σ.card →
      ∀ x ∈ simplex τ, ∀ y ∈ simplex τ, dist (h x) (h y) ≤ L * l2dist x y) :
    ∀ x ∈ simplexBoundary σ, ∀ y ∈ simplexBoundary σ,
      dist (h x) (h y) ≤ √(2 + 2 / ((k : ℝ) - 1)) * L * l2dist x y := by
  classical
  have hcard : Fintype.card σ = k + 1 := by rw [Fintype.card_coe]; exact hσ
  -- the transferred map is `L`-Lipschitz on the facets `{v i = 0}` of the standard simplex
  have hface' : ∀ i : σ, ∀ v ∈ SimplexExt.simplexE σ, v i = 0 →
      ∀ w ∈ SimplexExt.simplexE σ, w i = 0 →
        dist (h (SimplexExt.liftE σ v)) (h (SimplexExt.liftE σ w)) ≤ L * dist v w := by
    intro i v hv hvi w hw hwi
    rw [← SimplexExt.l2dist_liftE σ v w]
    have hvi' : SimplexExt.liftE σ v i = 0 := by
      rw [SimplexExt.liftE_apply_of_mem σ v i.2]
      exact hvi
    have hwi' : SimplexExt.liftE σ w i = 0 := by
      rw [SimplexExt.liftE_apply_of_mem σ w i.2]
      exact hwi
    exact hface (σ.erase i) (Finset.erase_subset _ _) (Finset.card_erase_add_one i.2) _
      (mem_simplex_erase_of_eq_zero (liftE_mem_simplex σ hv) hvi') _
      (mem_simplex_erase_of_eq_zero (liftE_mem_simplex σ hw) hwi')
  have hb := SimplexExt.lipschitz_boundaryE_of_faces hcard hk hL hface'
  intro x hx y hy
  have := hb _ (SimplexExt.restr_mem_boundaryE σ hx) _ (SimplexExt.restr_mem_boundaryE σ hy)
  rw [SimplexExt.liftE_restr σ hx.1.2.1, SimplexExt.liftE_restr σ hy.1.2.1] at this
  rw [l2dist_eq_dist_euclidean hx.1.2.1 hy.1.2.1]
  exact this

end LipschitzExtension
