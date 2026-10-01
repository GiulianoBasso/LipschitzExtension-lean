/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Geometry.CAT0.Defs
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Zorn
import LipschitzExtension.Topology.EMetricSpace.Lipschitz

/-!
# Kirszbraun's theorem for CAT(0) targets

This file proves the generalized Kirszbraun theorem of Lang and Schroeder (Theorem A of
[U. Lang and V. Schroeder, *Kirszbraun's theorem and metric spaces of bounded curvature*], in the
case of domains in a real inner product space): let `H` be a real inner product space, `Y` a
complete CAT(0) space, `A ⊆ H` and `f : A → Y` a `K`-Lipschitz map. Then `f` has a `K`-Lipschitz
extension `F : H → Y`. This is the extension theorem used in the proof of Theorem 1.3 of
[Basso2024].

## Main statements

* `IsCAT0.exists_one_point_extension`: the one-point extension property for arbitrary families.
* `LipschitzOnWith.extend_innerProductSpace_isCAT0`: Kirszbraun's theorem for CAT(0) targets.

## Proof outline

We use that `Y` is complete and satisfies the CN inequality (`IsCAT0.exists_midpoint`: every
`x, y` have a midpoint `m` with `d(z, m)² ≤ (d(z, x)² + d(z, y)²)/2 - d(x, y)²/4` for all `z`,
and its version along geodesics, `IsCAT0.dist_sq_le`).

1. **Strong convexity.** For weights `λ_i ≥ 0` and points `y_i`, the function
   `Φ(z) = ∑ λ_i d(z, y_i)²` satisfies `Φ(m) ≤ (Φ(z) + Φ(z'))/2 - (∑ λ_i) d(z, z')²/4` for the
   CN-midpoint `m` of `z, z'`; the same holds for `G(z) = max_i (d(z, y_i)² - r_i²)` (with
   coefficient `1/4`). Hence minimizing sequences are Cauchy, and minimizers exist (`Y` complete).
2. **Variance inequality.** If `b` minimizes `Φ` (with `∑ λ_i = 1`), then
   `Φ(z) ≥ Φ(b) + d(z, b)²` for all `z`: applying 1. to `b` and `z` and the minimality of `b` gives
   `Φ(z) ≥ Φ(b) + c d(z, b)²` with `c = 1/2`, and iterating (with the midpoint of `b` and `z`)
   improves `c` to `(1 + c)/2 → 1`. Taking `z = y_j` and averaging over `j`:
   `∑_{i,j} λ_i λ_j d(y_i, y_j)² ≥ 2 Φ(b)`.
3. **Finite one-point extension.** Let `x_1, …, x_k, x ∈ H` and `y_1, …, y_k ∈ Y` with
   `d(y_i, y_j) ≤ ‖x_i - x_j‖`, and put `r_i = ‖x - x_i‖`. For every `λ` in the standard simplex,
   by 2. and the Euclidean identity `∑_{i,j} λ_i λ_j ‖x_i - x_j‖² = 2 ∑ λ_i ‖x̄ - x_i‖²`
   (`x̄ = ∑ λ_i x_i`):
   `min_z ∑ λ_i (d(z, y_i)² - r_i²) ≤ ½ ∑ λ_i λ_j ‖x_i - x_j‖² - ∑ λ_i ‖x - x_i‖² ≤ 0`.
   The set `C = {v ∈ ℝ^k | ∃ z, d(z, y_i)² - r_i² < v_i ∀ i}` is open and convex (by
   `IsCAT0.dist_sq_le` along a geodesic between two witnesses). If `ε·1 ∉ C` for some
   `ε > 0`, the Hahn–Banach separation theorem (`geometric_hahn_banach_open_point`) gives a nonzero
   linear functional, which is `≤ 0` on the coordinate vectors since `C` is upward closed;
   normalizing gives `λ` in the simplex with `∑ λ_i (d(z, y_i)² - r_i²) ≥ ε` for all `z`, a
   contradiction. So `inf_z G(z) ≤ 0` with `G(z) = max_i (d(z, y_i)² - r_i²)`, and by 1. `G` attains
   its infimum: some `z` has `d(z, y_i) ≤ r_i` for all `i`.
4. **Arbitrary families.** For a family `(x_a, y_a)_{a ∈ S}` and `x ∈ H`, let `G_F` be as in 3. for
   finite `F ⊆ S` with minimizer `z_F` and minimum `m_F ≤ 0`. By 1. (as in 2.),
   `G_F(z) ≥ m_F + d(z, z_F)²`. For `F ⊆ F'`, `G_F ≤ G_F'`, so `m_F` increases to some `m ≤ 0` and
   `d(z_F', z_F)² ≤ G_F(z_F') - m_F ≤ m - m_F`: the net `(z_F)` is Cauchy and converges to some `z`
   with `d(z, y_a) ≤ ‖x - x_a‖` for all `a` (`IsCAT0.exists_one_point_extension`).
5. **Zorn's lemma.** Partial `L`-Lipschitz extensions of `f` (graphs ordered by inclusion) have a
   maximal element; by 4. (applied to the rescaled points `L x_a`, or trivially if `L = 0`) it is
   defined everywhere.

## References

* U. Lang and V. Schroeder, *Kirszbraun's theorem and metric spaces of bounded curvature*,
  Geom. Funct. Anal. 7 (1997), 535–560
* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open Set Metric Filter Topology

namespace LipschitzExtension

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {Y : Type*} [MetricSpace Y]

/-- A continuous function on a complete metric space which is bounded below and uniformly
midpoint convex (for all `z, z'` some `w` has `Φ w ≤ (Φ z + Φ z')/2 - k d(z, z')²`, `k > 0`)
attains its infimum: minimizing sequences are Cauchy. -/
private lemma exists_forall_le_of_midpoint [CompleteSpace Y] [Nonempty Y] (Φ : Y → ℝ)
    (hΦ : Continuous Φ) {c : ℝ} (hc : ∀ z, c ≤ Φ z) {k : ℝ} (hk : 0 < k)
    (hmid : ∀ z z', ∃ w, Φ w ≤ (Φ z + Φ z') / 2 - k * dist z z' ^ 2) :
    ∃ b, ∀ z, Φ b ≤ Φ z := by
  set μ := ⨅ z, Φ z
  have hbdd : BddBelow (range Φ) := ⟨c, by rintro _ ⟨z, rfl⟩; exact hc z⟩
  have hμ : ∀ z, μ ≤ Φ z := fun z ↦ ciInf_le hbdd z
  have hex : ∀ n : ℕ, ∃ z, Φ z < μ + 1 / ((n : ℝ) + 1) := fun n ↦
    exists_lt_of_ciInf_lt (lt_add_of_pos_right μ (by positivity))
  choose u hu using hex
  have hdist : ∀ n m : ℕ,
      k * dist (u n) (u m) ^ 2 ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) / 2 := by
    intro n m
    obtain ⟨w, hw⟩ := hmid (u n) (u m)
    linarith [hμ w, hu n, hu m]
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < k * ε ^ 2 by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    have h1 := hdist n N
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      gcongr
    have h3 : dist (u n) (u N) ^ 2 < ε ^ 2 := by
      by_contra hcon
      nlinarith [not_lt.1 hcon]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨b, fun z ↦ ?_⟩
  have h1 : Tendsto (fun n ↦ Φ (u n)) atTop (𝓝 (Φ b)) := (hΦ.tendsto b).comp hb
  have h2 : Tendsto (fun n : ℕ ↦ μ + 1 / ((n : ℝ) + 1)) atTop (𝓝 (μ + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at h2
  exact (le_of_tendsto_of_tendsto' h1 h2 fun n ↦ (hu n).le).trans (hμ z)

/-- An elementary inequality: if `(1 - t) K ≤ D` for all `t ∈ (0, 1]`, then `K ≤ D`. -/
private lemma le_of_forall_Ioc {D K : ℝ} (h : ∀ t ∈ Ioc (0 : ℝ) 1, (1 - t) * K ≤ D) :
    K ≤ D := by
  by_contra hlt
  have hlt := not_le.1 hlt
  have h1 := h 1 ⟨one_pos, le_rfl⟩
  rw [sub_self, zero_mul] at h1
  have hK : 0 < K := by linarith
  have ht0 : 0 < (K - D) / (2 * K) := div_pos (by linarith) (by linarith)
  have ht1 : (K - D) / (2 * K) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have h2 := h _ ⟨ht0, ht1⟩
  have e : (1 - (K - D) / (2 * K)) * K = (K + D) / 2 := by
    field_simp
    ring
  rw [e] at h2
  linarith

/-- The squared distance to a point is strongly convex along geodesics in a CAT(0) space. -/
private lemma dist_sq_geodesic_le (hY : IsCAT0 Y) {γ : ℝ → Y} {z z' : Y}
    (hγ : IsGeodesic γ z z') (p : Y) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (γ (t * dist z z')) p ^ 2 ≤
      (1 - t) * dist z p ^ 2 + t * dist z' p ^ 2 - t * (1 - t) * dist z z' ^ 2 := by
  have := hY.dist_sq_le hγ p ht
  rwa [dist_comm p, dist_comm p, dist_comm p] at this

/-- Weighted sums of squared distances are strongly convex along geodesics in a CAT(0) space. -/
private lemma sum_dist_sq_geodesic_le (hY : IsCAT0 Y) {κ : Type*} [Fintype κ] (y : κ → Y)
    (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ → Y} {z z' : Y} (hγ : IsGeodesic γ z z') {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∑ i, w i * dist (γ (t * dist z z')) (y i) ^ 2 ≤
      (1 - t) * ∑ i, w i * dist z (y i) ^ 2 + t * ∑ i, w i * dist z' (y i) ^ 2 -
        t * (1 - t) * (∑ i, w i) * dist z z' ^ 2 := by
  have h : ∀ i, w i * dist (γ (t * dist z z')) (y i) ^ 2 ≤
      (1 - t) * (w i * dist z (y i) ^ 2) + t * (w i * dist z' (y i) ^ 2) -
        t * (1 - t) * w i * dist z z' ^ 2 := by
    intro i
    calc w i * dist (γ (t * dist z z')) (y i) ^ 2 ≤
        w i * ((1 - t) * dist z (y i) ^ 2 + t * dist z' (y i) ^ 2 -
          t * (1 - t) * dist z z' ^ 2) :=
          mul_le_mul_of_nonneg_left (dist_sq_geodesic_le hY hγ (y i) ht) (hw i)
      _ = _ := by ring
  calc _ ≤ ∑ i, ((1 - t) * (w i * dist z (y i) ^ 2) + t * (w i * dist z' (y i) ^ 2) -
        t * (1 - t) * w i * dist z z' ^ 2) := Finset.sum_le_sum fun i _ ↦ h i
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.sum_mul, ← Finset.mul_sum]

/-- The Euclidean inequality `∑_{i,j} w_i w_j ‖x_i - x_j‖² ≤ 2 (∑ w) ∑_i w_i ‖x₀ - x_i‖²` in a
real inner product space (the difference is `2 ‖∑ w_i (x_i - x₀)‖²`). -/
private lemma sum_sum_norm_sub_sq_le {κ : Type*} [Fintype κ] (x : κ → H) (x₀ : H) (w : κ → ℝ) :
    ∑ i, ∑ j, w i * w j * ‖x i - x j‖ ^ 2 ≤ 2 * (∑ i, w i) * ∑ i, w i * ‖x₀ - x i‖ ^ 2 := by
  set u : κ → H := fun i ↦ x i - x₀
  have hu : ∀ i j, x i - x j = u i - u j := fun i j ↦ by simp only [u]; abel
  have hn : ∀ i, ‖x₀ - x i‖ = ‖u i‖ := fun i ↦ by simp only [u]; rw [norm_sub_rev]
  have key : ∀ i j, w i * w j * ‖x i - x j‖ ^ 2 =
      w j * (w i * ‖u i‖ ^ 2) + w i * (w j * ‖u j‖ ^ 2) - 2 * inner ℝ (w i • u i) (w j • u j) := by
    intro i j
    rw [hu, norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right]
    ring
  have hsq : 0 ≤ inner ℝ (∑ i, w i • u i) (∑ j, w j • u j) := real_inner_self_nonneg
  rw [sum_inner] at hsq
  simp_rw [inner_sum] at hsq
  simp_rw [key, hn, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul]
  rw [← Finset.mul_sum]
  linarith

/-- For weights `w i ≥ 0` there is a point `z` with `∑ w_i (d(z, y_i)² - ‖x₀ - x_i‖²) ≤ 0`: take
the barycenter `b` of the `y_i` (the minimizer of `Φ = ∑ w_i d(·, y_i)²`) and use the variance
inequality `Φ(z) ≥ Φ(b) + (∑ w) d(b, z)²` for `z = y_j`. -/
private lemma exists_sum_mul_le [CompleteSpace Y] [Nonempty Y] (hY : IsCAT0 Y) {κ : Type*}
    [Fintype κ] (x : κ → H) (y : κ → Y) (h : ∀ i j, dist (y i) (y j) ≤ dist (x i) (x j))
    (x₀ : H) (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ z, ∑ i, w i * (dist z (y i) ^ 2 - dist x₀ (x i) ^ 2) ≤ 0 := by
  set Λ := ∑ i, w i
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun i _ ↦ hw i
  rcases hΛ0.eq_or_lt with hΛ | hΛ
  · obtain ⟨z⟩ := ‹Nonempty Y›
    have hw0 : ∀ i, w i = 0 := fun i ↦
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hw i).1 hΛ.symm i (Finset.mem_univ i)
    exact ⟨z, by simp [hw0]⟩
  set Φ : Y → ℝ := fun z ↦ ∑ i, w i * dist z (y i) ^ 2
  have hΦc : Continuous Φ := by fun_prop
  have hΦ0 : ∀ z, 0 ≤ Φ z := fun z ↦
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (sq_nonneg _)
  have hgeo : ∀ {γ : ℝ → Y} {z z' : Y}, IsGeodesic γ z z' → ∀ t ∈ Icc (0 : ℝ) 1,
      Φ (γ (t * dist z z')) ≤ (1 - t) * Φ z + t * Φ z' - t * (1 - t) * Λ * dist z z' ^ 2 :=
    fun hγ _ ht ↦ sum_dist_sq_geodesic_le hY y w hw hγ ht
  obtain ⟨b, hb⟩ := exists_forall_le_of_midpoint Φ hΦc hΦ0 (k := Λ / 4) (by positivity)
    fun z z' ↦ by
      obtain ⟨γ, hγ⟩ := hY.1 z z'
      refine ⟨γ (1 / 2 * dist z z'), ?_⟩
      have := hgeo hγ (1 / 2) ⟨by norm_num, by norm_num⟩
      linarith
  -- the variance inequality, via `IsCAT0.dist_sq_le` along a geodesic from `b` to `z`:
  -- `Φ z - Φ b ≥ (1 - t) Λ d(b, z)²` for all `t ∈ (0, 1]`
  have hvar : ∀ z, Φ b + Λ * dist b z ^ 2 ≤ Φ z := by
    intro z
    obtain ⟨γ, hγ⟩ := hY.1 b z
    have : Λ * dist b z ^ 2 ≤ Φ z - Φ b := le_of_forall_Ioc fun t ht ↦ by
      have h1 := hgeo hγ t ⟨ht.1.le, ht.2⟩
      have h2 := hb (γ (t * dist b z))
      have : t * ((1 - t) * (Λ * dist b z ^ 2)) ≤ t * (Φ z - Φ b) := by linarith
      exact le_of_mul_le_mul_left this ht.1
    linarith
  -- averaging the variance inequality over `z = y j`
  have hsum1 : 2 * Λ * Φ b ≤ ∑ j, w j * Φ (y j) := by
    have e : ∑ j, w j * (Φ b + Λ * dist b (y j) ^ 2) = Λ * Φ b + Λ * Φ b := by
      have e1 : ∑ j, w j * (Φ b + Λ * dist b (y j) ^ 2) =
          ∑ j, (w j * Φ b + Λ * (w j * dist b (y j) ^ 2)) :=
        Finset.sum_congr rfl fun j _ ↦ by ring
      rw [e1, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    calc 2 * Λ * Φ b = ∑ j, w j * (Φ b + Λ * dist b (y j) ^ 2) := by rw [e]; ring
      _ ≤ ∑ j, w j * Φ (y j) :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hvar (y j)) (hw j)
  have hsum2 : ∑ j, w j * Φ (y j) ≤ ∑ j, ∑ i, w j * w i * ‖x j - x i‖ ^ 2 := by
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have h1 : dist (y j) (y i) ^ 2 ≤ ‖x j - x i‖ ^ 2 := by
      rw [← dist_eq_norm]
      exact pow_le_pow_left₀ dist_nonneg (h j i) 2
    have h2 := mul_nonneg (hw j) (hw i)
    calc w j * (w i * dist (y j) (y i) ^ 2) = w j * w i * dist (y j) (y i) ^ 2 := by ring
      _ ≤ w j * w i * ‖x j - x i‖ ^ 2 := mul_le_mul_of_nonneg_left h1 h2
  have hsum3 := sum_sum_norm_sub_sq_le x x₀ w
  refine ⟨b, ?_⟩
  have hfin : Φ b ≤ ∑ i, w i * ‖x₀ - x i‖ ^ 2 := by
    have := hsum1.trans (hsum2.trans hsum3)
    have h2Λ : 0 < 2 * Λ := by positivity
    exact le_of_mul_le_mul_left this h2Λ
  simp only [mul_sub, Finset.sum_sub_distrib, dist_eq_norm x₀]
  linarith

/-- **Separation step.** Let `a i : Y → ℝ` (`i` in a finite type) be jointly convex (for all
`z, z'` and `t ∈ [0, 1]` some `w` has `a i w ≤ (1 - t) a i z + t a i z'` for all `i`), and assume
that for all weights `c ≥ 0` some `z` has `∑ c_i a_i(z) ≤ 0`. Then for every `ε > 0` some `z` has
`a i z < ε` for all `i`. (Hahn–Banach separation of `(ε, …, ε)` from the open convex set
`{v | ∃ z, ∀ i, a i z < v i}`.) -/
private lemma exists_forall_lt_of_forall_sum_le {Z : Type*} [Nonempty Z] {κ : Type*}
    [Fintype κ] (a : κ → Z → ℝ)
    (hconv : ∀ z z' : Z, ∀ t ∈ Icc (0 : ℝ) 1, ∃ w, ∀ i, a i w ≤ (1 - t) * a i z + t * a i z')
    (hsum : ∀ c : κ → ℝ, (∀ i, 0 ≤ c i) → ∃ z, ∑ i, c i * a i z ≤ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ z, ∀ i, a i z < ε := by
  classical
  by_contra hcon
  simp only [not_exists, not_forall, not_lt] at hcon
  set C : Set (κ → ℝ) := {v | ∃ z, ∀ i, a i z < v i} with hCdef
  have hCconv : Convex ℝ C := by
    rintro v ⟨z, hz⟩ v' ⟨z', hz'⟩ s t hs ht hst
    obtain ⟨w, hw⟩ := hconv z z' t ⟨ht, by linarith⟩
    refine ⟨w, fun i ↦ ?_⟩
    have h1 := hw i
    have h2 := hz i
    have h3 := hz' i
    rw [show 1 - t = s by linarith] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hs.eq_or_lt with hs0 | hs0
    · have ht1 : t = 1 := by linarith
      rw [← hs0, ht1] at h1 ⊢
      linarith
    · have h4 := mul_lt_mul_of_pos_left h2 hs0
      have h5 := mul_le_mul_of_nonneg_left h3.le ht
      linarith
  have hCopen : IsOpen C := by
    have : C = ⋃ z, ⋂ i, {v : κ → ℝ | a i z < v i} := by
      ext v
      simp [hCdef]
    rw [this]
    exact isOpen_iUnion fun z ↦ isOpen_iInter_of_finite fun i ↦
      isOpen_lt continuous_const (continuous_apply i)
  have hnot : (fun _ ↦ ε) ∉ C := by
    rintro ⟨z, hz⟩
    obtain ⟨i, hi⟩ := hcon z
    exact (hz i).not_ge hi
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hCconv hCopen hnot
  set e : κ → κ → ℝ := fun i j ↦ if i = j then 1 else 0 with he
  have hfv : ∀ v : κ → ℝ, f v = ∑ i, v i * f (e i) := fun v ↦ by
    have := (f : (κ → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ v
    simpa [smul_eq_mul] using this
  obtain ⟨z₀⟩ := ‹Nonempty Z›
  have hneg : ∀ j, f (e j) ≤ 0 := by
    intro j
    by_contra hpos
    have hpos := not_le.1 hpos
    set v₀ : κ → ℝ := fun i ↦ a i z₀ + 1 with hv₀
    set s := (|f (fun _ ↦ ε) - f v₀| + 1) / f (e j) with hs
    have hs0 : 0 ≤ s := by positivity
    have hmem : v₀ + s • e j ∈ C := by
      refine ⟨z₀, fun i ↦ ?_⟩
      have : 0 ≤ s * e j i := mul_nonneg hs0 (by simp only [he]; split_ifs <;> norm_num)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv₀]
      linarith
    have h1 := hf _ hmem
    rw [map_add, map_smul, smul_eq_mul, hs, div_mul_cancel₀ _ hpos.ne'] at h1
    linarith [le_abs_self (f (fun _ ↦ ε) - f v₀)]
  obtain ⟨z, hz⟩ := hsum (fun i ↦ -f (e i)) fun i ↦ neg_nonneg.2 (hneg i)
  have hmem : (fun i ↦ a i z + ε) ∈ C := ⟨z, fun i ↦ by linarith⟩
  have h1 := hf _ hmem
  rw [hfv, hfv] at h1
  have e1 : ∑ i, (a i z + ε) * f (e i) = ∑ i, a i z * f (e i) + ∑ i, ε * f (e i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have e2 : ∑ i, -f (e i) * a i z = -∑ i, a i z * f (e i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  linarith

/-- **One-point extension** in complete CAT(0) spaces: if `d(y a, y b) ≤ ‖x a - x b‖` for all
`a, b`, then every `x₀ ∈ H` has a "partner" `y₀ ∈ Y` with `d(y₀, y a) ≤ ‖x₀ - x a‖` for all `a`. -/
theorem IsCAT0.exists_one_point_extension [CompleteSpace Y] [Nonempty Y] (hY : IsCAT0 Y)
    {ι : Type*} (x : ι → H) (y : ι → Y) (h : ∀ a b, dist (y a) (y b) ≤ dist (x a) (x b))
    (x₀ : H) : ∃ y₀ : Y, ∀ a, dist y₀ (y a) ≤ dist x₀ (x a) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨a₀⟩⟩
  · obtain ⟨z⟩ := ‹Nonempty Y›
    exact ⟨z, fun a ↦ isEmptyElim a⟩
  set r : ι → ℝ := fun a ↦ dist x₀ (x a)
  -- `G F z = max_{a ∈ F ∪ {a₀}} (d(z, y a)² - r a²)`
  set G : Finset ι → Y → ℝ := fun F z ↦
    (insert a₀ F).sup' (Finset.insert_nonempty a₀ F) fun a ↦ dist z (y a) ^ 2 - r a ^ 2
  have hG_le : ∀ F z, ∀ a ∈ insert a₀ F, dist z (y a) ^ 2 - r a ^ 2 ≤ G F z :=
    fun F z a ha ↦ Finset.le_sup' (fun a ↦ dist z (y a) ^ 2 - r a ^ 2) ha
  have hG_cont : ∀ F, Continuous (G F) := fun F ↦
    Continuous.finset_sup'_apply _ fun a _ ↦ by fun_prop
  have hG_geo : ∀ F {γ : ℝ → Y} {z z' : Y}, IsGeodesic γ z z' → ∀ t ∈ Icc (0 : ℝ) 1,
      G F (γ (t * dist z z')) ≤ (1 - t) * G F z + t * G F z' - t * (1 - t) * dist z z' ^ 2 := by
    intro F γ z z' hγ t ht
    refine Finset.sup'_le _ _ fun a ha ↦ ?_
    have h1 := dist_sq_geodesic_le hY hγ (y a) ht
    have h2 := mul_le_mul_of_nonneg_left (hG_le F z a ha) (sub_nonneg.2 ht.2)
    have h3 := mul_le_mul_of_nonneg_left (hG_le F z' a ha) ht.1
    linarith
  have hG_mono : ∀ F F', F ⊆ F' → ∀ z, G F z ≤ G F' z := fun F F' hFF' z ↦
    Finset.sup'_mono _ (Finset.insert_subset_insert a₀ hFF') _
  have hG_lb : ∀ F z, -r a₀ ^ 2 ≤ G F z := fun F z ↦ by
    have := hG_le F z a₀ (Finset.mem_insert_self a₀ F)
    nlinarith [sq_nonneg (dist z (y a₀))]
  -- minimizers `zF F` of `G F`; the minimal values `G F (zF F)` increase with `F`
  have hmin : ∀ F, ∃ b, ∀ z, G F b ≤ G F z := fun F ↦
    exists_forall_le_of_midpoint (G F) (hG_cont F) (hG_lb F) (k := 1 / 4) (by norm_num)
      fun z z' ↦ by
        obtain ⟨γ, hγ⟩ := hY.1 z z'
        refine ⟨γ (1 / 2 * dist z z'), ?_⟩
        have := hG_geo F hγ (1 / 2) ⟨by norm_num, by norm_num⟩
        linarith
  choose zF hzF using hmin
  -- the minimal values are `≤ 0` by the separation step (`inf G F ≤ 0`)
  have hm0 : ∀ F, G F (zF F) ≤ 0 := by
    intro F
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    obtain ⟨z, hz⟩ := exists_forall_lt_of_forall_sum_le (κ := ↥(insert a₀ F))
      (fun i z ↦ dist z (y i) ^ 2 - r i ^ 2)
      (fun z z' t ht ↦ by
        obtain ⟨γ, hγ⟩ := hY.1 z z'
        refine ⟨γ (t * dist z z'), fun i ↦ ?_⟩
        have h1 := dist_sq_geodesic_le hY hγ (y i) ht
        have h2 : 0 ≤ t * (1 - t) * dist z z' ^ 2 :=
          mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 ht.2)) (sq_nonneg _)
        linarith)
      (fun c hc ↦ exists_sum_mul_le hY (fun i : ↥(insert a₀ F) ↦ x i)
        (fun i : ↥(insert a₀ F) ↦ y i) (fun i j ↦ h i j) x₀ c hc)
      hε
    have : G F z < ε := (Finset.sup'_lt_iff _).2 fun a ha ↦ hz ⟨a, ha⟩
    linarith [hzF F z]
  -- `G F z ≥ G F (zF F) + d(zF F, z)²/2` (strong convexity at the midpoint of `zF F`, `z`)
  have hvar : ∀ F z, G F (zF F) + dist (zF F) z ^ 2 / 2 ≤ G F z := by
    intro F z
    obtain ⟨γ, hγ⟩ := hY.1 (zF F) z
    have h1 := hG_geo F hγ (1 / 2) ⟨by norm_num, by norm_num⟩
    have h2 := hzF F (γ (1 / 2 * dist (zF F) z))
    linarith
  have hbdd : BddAbove (range fun F ↦ G F (zF F)) := ⟨0, by rintro _ ⟨F, rfl⟩; exact hm0 F⟩
  set M := ⨆ F, G F (zF F)
  have hmM : ∀ F, G F (zF F) ≤ M := fun F ↦ le_ciSup hbdd F
  -- the net `zF` is Cauchy
  have hcauchy : CauchySeq zF := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨F₀, hF₀⟩ := exists_lt_of_lt_ciSup
      (show M - ε ^ 2 / 2 < M by linarith [pow_pos hε 2])
    refine ⟨F₀, fun F hF ↦ ?_⟩
    have h1 := hvar F₀ (zF F)
    have h2 := hG_mono F₀ F hF (zF F)
    have h3 := hmM F
    have h4 : dist (zF F) (zF F₀) ^ 2 < ε ^ 2 := by
      rw [dist_comm]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h4
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨z, fun a ↦ ?_⟩
  have hmem : ∀ᶠ F in atTop, zF F ∈ closedBall (y a) (r a) := by
    refine eventually_atTop.2 ⟨{a}, fun F hF ↦ ?_⟩
    have ha : a ∈ insert a₀ F :=
      Finset.mem_insert_of_mem (hF (Finset.mem_singleton_self a))
    have h1 := hG_le F (zF F) a ha
    have h2 := hm0 F
    rw [mem_closedBall]
    exact (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).1 (by linarith)
  exact mem_closedBall.1 (isClosed_closedBall.mem_of_tendsto hz hmem)

/-- Kirszbraun's theorem for CAT(0) targets, in the form proved by Zorn's lemma. -/
private theorem exists_extension_of_isCAT0 [CompleteSpace Y] [Nonempty Y] (hY : IsCAT0 Y)
    {A : Set H} {L : ℝ} (hL : 0 ≤ L) {f : H → Y}
    (hf : ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) ≤ L * dist x y) :
    ∃ F : H → Y, (∀ x ∈ A, F x = f x) ∧ ∀ x y, dist (F x) (F y) ≤ L * dist x y := by
  -- Zorn's lemma on graphs of partial `L`-Lipschitz extensions of `f|A`
  set Γ₀ : Set (H × Y) := (fun x ↦ (x, f x)) '' A
  set S : Set (Set (H × Y)) :=
    {Γ | Γ₀ ⊆ Γ ∧ ∀ p ∈ Γ, ∀ q ∈ Γ, dist p.2 q.2 ≤ L * dist p.1 q.1}
  have hΓ₀S : Γ₀ ∈ S := by
    refine ⟨subset_rfl, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    exact hf x hx x' hx'
  obtain ⟨Γ, -, hΓ⟩ := zorn_subset_nonempty S (fun c hcS hc hne ↦ by
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs ↦ subset_sUnion_of_mem hs⟩
    · obtain ⟨s, hs⟩ := hne
      exact (hcS hs).1.trans (subset_sUnion_of_mem hs)
    · rintro p ⟨s, hs, hp⟩ q ⟨s', hs', hq⟩
      rcases hc.total hs hs' with hss | hss
      · exact (hcS hs').2 p (hss hp) q hq
      · exact (hcS hs).2 p hp q (hss hq)) Γ₀ hΓ₀S
  have hdist : ∀ a b : H, dist (L • a) (L • b) = L * dist a b := fun a b ↦ by
    rw [dist_smul₀, Real.norm_of_nonneg hL]
  -- every point of `H` lies in the domain of the maximal graph `Γ`
  have hdom : ∀ x₀ : H, ∃ y₀, (x₀, y₀) ∈ Γ := by
    intro x₀
    obtain ⟨y₀, hy₀⟩ := hY.exists_one_point_extension (ι := Γ) (fun p ↦ L • p.1.1)
      (fun p ↦ p.1.2) (fun p q ↦ by rw [hdist]; exact hΓ.1.2 p.1 p.2 q.1 q.2) (L • x₀)
    refine ⟨y₀, ?_⟩
    have hy₀' : ∀ q ∈ Γ, dist y₀ q.2 ≤ L * dist x₀ q.1 := fun q hq ↦ by
      have := hy₀ ⟨q, hq⟩
      rwa [hdist] at this
    have hmem : insert (x₀, y₀) Γ ∈ S := by
      refine ⟨hΓ.1.1.trans (subset_insert _ _), ?_⟩
      rintro p (rfl | hp) q (rfl | hq)
      · simp
      · exact hy₀' q hq
      · rw [dist_comm, dist_comm p.1]
        exact hy₀' p hp
      · exact hΓ.1.2 p hp q hq
    exact hΓ.2 hmem (subset_insert _ _) (mem_insert _ _)
  choose F hF using hdom
  refine ⟨F, fun x hx ↦ ?_, fun x x' ↦ hΓ.1.2 _ (hF x) _ (hF x')⟩
  have h1 := hΓ.1.2 _ (hF x) _ (hΓ.1.1 ⟨x, hx, rfl⟩)
  rw [dist_self, mul_zero] at h1
  exact dist_le_zero.1 h1

end LipschitzExtension

open LipschitzExtension

/-- **Kirszbraun's theorem for CAT(0) targets** (Lang–Schroeder, Theorem A, for domains in a real
inner product space): a `K`-Lipschitz map from a subset `A` of a real inner product space `H` to a
complete CAT(0) space `Y` extends to a `K`-Lipschitz map on `H`. -/
theorem LipschitzOnWith.extend_innerProductSpace_isCAT0 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Y : Type*} [MetricSpace Y] [CompleteSpace Y] {K : NNReal} {A : Set H}
    {f : H → Y} (hf : LipschitzOnWith K f A) (hY : IsCAT0 Y) :
    ∃ F : H → Y, LipschitzWith K F ∧ EqOn f F A := by
  refine exists_lipschitzWith_eqOn_of_nonempty fun _ ↦ ?_
  obtain ⟨F, hFA, hF⟩ := exists_extension_of_isCAT0 hY K.coe_nonneg
    (fun x hx y hy ↦ hf.dist_le_mul x hx y hy)
  exact ⟨F, LipschitzWith.of_dist_le_mul hF, fun x hx ↦ (hFA x hx).symm⟩
