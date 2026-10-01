/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Geometry.SimplicialComplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Geometry of simplices in `ℓ₂`

This file proves Lemma 5.1 of [Basso2024] and the geometric steps of the proof of Lemma 5.2 (with
item 3) of the errata [BassoClaude2026]). Lemma 5.2 is proved in
`LipschitzExtension.Geometry.SimplicialComplex.Quasiconvex` and used for Theorem 1.3.

For a finite vertex set `V`, the simplex spanned by `σ ⊆ V` is
`face σ = {x ∈ ℓ₂(V) | x ≥ 0, ∑ x_i = 1, x_i = 0 for i ∉ σ}`; an `n`-simplex has `n + 1` vertices.
Two faces meet iff they share a vertex, and `face σ ∩ face τ = face (σ ∩ τ)`.

* **Lemma 5.1.** If `Δ, Δ'` are `n`-simplices with `Δ ∩ Δ' ≠ ∅`, then for all `x ∈ Δ`, `y ∈ Δ'`
  there is `z ∈ Δ ∩ Δ'` with `|x - z| + |z - y| ≤ 4 √n |x - y|`.
* **Vertex estimate** (proof of Lemma 5.2): if `x ∈ face σ`, `y ∈ face τ` with `σ ∩ τ = ∅`,
  `#σ, #τ ≤ n + 1` and `n ≥ 1`, then every vertex `e_w` satisfies
  `|x - e_w| + |e_w - y| ≤ 4 √n |x - y|`.
* **Chains** (proof of Lemma 5.2 with item 3 of the errata): let `σ_0, …, σ_m` be `(n+1)`-sets
  (`n ≥ 1`) such that consecutive faces meet and non-consecutive faces are disjoint, and
  `m + 1 ≤ 2^k`. Then for `x ∈ face σ_0`, `y ∈ face σ_m` there are points `x = p_0, …, p_l = y`,
  each two consecutive ones in a common face `σ_j`, with `∑ |p_i - p_(i+1)| ≤ (4√n)^k |x - y|`.

## Main definitions

* `Triangulation.face σ`: the simplex spanned by the vertices `σ ⊆ V` in `EuclideanSpace ℝ V`.

## Main statements

* `Triangulation.exists_mem_face_inter_dist_add_dist_le`: Lemma 5.1 for simplices in `ℓ₂(V)`,
  `V` finite.
* `exists_mem_simplex_inter_l2dist_le`: Lemma 5.1 in the paper's setting of simplices in `ℓ₂(I)`
  for an arbitrary index set `I` (`simplex`, `l2dist`).
* `Triangulation.dist_add_dist_single_le`: the vertex estimate.
* `Triangulation.exists_polygonal_of_chain`: polygonal paths along chains of `n`-simplices.

## Proof outline

*Lemma 5.1* (paper): choose a common vertex `0` and let `z` keep the coordinates of `x` on the
common vertices `0, …, k` and put the remaining mass `ν = ∑_{i > k} x_i` on the vertex `0`. Then
`|x - z|² = ν² + ∑_{i>k} x_i²`,
`|y - z|² ≤ 2 (x_0 - y_0)² + 2ν² + ∑_{1 ≤ i ≤ k} (x_i - y_i)² + ∑_{i>k} y_i²` and
`ν² ≤ m ∑_{i>k} x_i²` (`m = n - k ≤ n`), so `|x - z|² + |z - y|² ≤ (3n + 1) |x - y|²` and
`(|x - z| + |z - y|)² ≤ 2 (3n + 1) |x - y|² ≤ 16 n |x - y|²`.

*Vertex estimate* (paper): `⟨x - e_w, y - e_w⟩ ≤ η |x - e_w| |y - e_w|` with
`η = √(1 - 1/(n+2))` (if `w ∉ σ ∪ τ` the inner product is `1` and
`|x - e_w|², |y - e_w|² ≥ 1 + 1/(n+1)`; if `w ∈ σ` it is `1 - x_w ≤ |x - e_w|` and
`|y - e_w|² ≥ 1 + 1/(n+1)`), and then the law of cosines gives `κ (a + b) ≤ |x - y|` for
`a = |x - e_w|`, `b = |e_w - y|` and `κ² = (1 - η)/2` (since
`a² + b² - 2η ab - κ² (a + b)² = (1 + η)(a - b)²/2 ≥ 0`), and `κ⁻¹ ≤ 2 √(n + 2) ≤ 4 √n`.

*Chains*: induction on `k`. For `m = 0` take the segment; for `m = 1` use Lemma 5.1; for `m ≥ 2`
the faces `σ_0, σ_m` are disjoint: split the chain at `m' = ⌈(m+1)/2⌉`, pick a common vertex `e_w`
of `σ_(m'-1)` and `σ_m'` and apply the vertex estimate and induction to the two halves.

## Implementation notes

* Lemma 5.1: the case `n = 0`, in which `x = y`, is treated separately, and we sum the pointwise
  bound `(x_i - z_i)² + (z_i - y_i)² ≤ 2 (x_i - y_i)² + [i = a] 3ν²` (where `a` is the common
  vertex), which gives the factor `3n + 2` instead of `3n + 1`.
* Vertex estimate: we use the following shortcut instead of the angle estimate. As `x ⊥ y`,
  `|x - e_w|² + |e_w - y|² ≤ |x|² + |y|² + 2 = |x - y|² + 2`, and `|x - y|² ≥ 2/(n+1)` gives
  `|x - e_w|² + |e_w - y|² ≤ (n + 2) |x - y|²`, hence
  `(|x - e_w| + |e_w - y|)² ≤ 2 (n + 2) |x - y|² ≤ 16 n |x - y|²`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
-/

open Set Finset

namespace LipschitzExtension

namespace Triangulation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The simplex spanned by the vertices `σ ⊆ V` in `ℓ₂(V) = EuclideanSpace ℝ V`. -/
def face (σ : Finset V) : Set (EuclideanSpace ℝ V) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 ∧ ∀ i, i ∉ σ → x i = 0}

omit [DecidableEq V] in
/-- Faces are convex. -/
theorem convex_face (σ : Finset V) : Convex ℝ (face σ) := by
  rintro x ⟨hx0, hx1, hxσ⟩ y ⟨hy0, hy1, hyσ⟩ a b ha hb hab
  refine ⟨fun i ↦ ?_, ?_, fun i hi ↦ ?_⟩
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx0 i)) (mul_nonneg hb (hy0 i))
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx1, hy1, mul_one, hab]
  · simp [hxσ i hi, hyσ i hi]

omit [DecidableEq V] in
/-- Faces are closed. -/
theorem isClosed_face (σ : Finset V) : IsClosed (face σ) := by
  have hc : ∀ i, Continuous fun x : EuclideanSpace ℝ V ↦ x i := fun i ↦
    PiLp.continuous_apply 2 _ i
  have h1 : IsClosed {x : EuclideanSpace ℝ V | ∀ i, 0 ≤ x i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_le continuous_const (hc i)
  have h2 : IsClosed {x : EuclideanSpace ℝ V | ∑ i, x i = 1} :=
    isClosed_eq (continuous_finsetSum _ fun i _ ↦ hc i) continuous_const
  have h3 : IsClosed {x : EuclideanSpace ℝ V | ∀ i, i ∉ σ → x i = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦ isClosed_eq (hc i) continuous_const
  exact h1.inter (h2.inter h3)

omit [DecidableEq V] in
/-- Monotonicity: `face σ ⊆ face τ` for `σ ⊆ τ`. -/
theorem face_mono {σ τ : Finset V} (h : σ ⊆ τ) : face σ ⊆ face τ :=
  fun _ ⟨hx0, hx1, hxσ⟩ ↦ ⟨hx0, hx1, fun i hi ↦ hxσ i fun h' ↦ hi (h h')⟩

/-- Two faces intersect in the face spanned by their common vertices. -/
theorem face_inter (σ τ : Finset V) : face σ ∩ face τ = face (σ ∩ τ) := by
  ext x
  simp only [face, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_inter, not_and_or]
  constructor
  · rintro ⟨⟨hx0, hx1, hxσ⟩, -, -, hxτ⟩
    exact ⟨hx0, hx1, fun i hi ↦ hi.elim (hxσ i) (hxτ i)⟩
  · rintro ⟨hx0, hx1, hx⟩
    exact ⟨⟨hx0, hx1, fun i hi ↦ hx i (Or.inl hi)⟩, hx0, hx1, fun i hi ↦ hx i (Or.inr hi)⟩

/-- The vertex `e_w` lies in every face containing `w`. -/
theorem single_mem_face {σ : Finset V} {w : V} (hw : w ∈ σ) :
    EuclideanSpace.single w (1 : ℝ) ∈ face σ := by
  refine ⟨fun i ↦ ?_, ?_, fun i hi ↦ ?_⟩
  · rw [PiLp.single_apply]; split_ifs <;> norm_num
  · simp
  · rw [PiLp.single_apply, ite_eq_right]
    rintro rfl
    exact hi hw

omit [DecidableEq V] in
/-- A face is nonempty iff it has a vertex. -/
theorem face_nonempty_iff (σ : Finset V) : (face σ).Nonempty ↔ σ.Nonempty := by
  classical
  constructor
  · rintro ⟨x, -, hx1, hxσ⟩
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [hxσ, h] at hx1
  · rintro ⟨w, hw⟩
    exact ⟨_, single_mem_face hw⟩

/-! ### Lemma 5.1 -/

/-- The coordinates of the point `z` in the proof of Lemma 5.1: keep `x` on `τ` and put the mass
`ν = ∑_{j ∈ σ \ τ} x_j` of `x` outside `τ` on the common vertex `a`. -/
private def lem51z {ι : Type*} [DecidableEq ι] (σ τ : Finset ι) (a : ι) (x : ι → ℝ) (i : ι) : ℝ :=
  (if i ∈ τ then x i else 0) + if i = a then ∑ j ∈ σ \ τ, x j else 0

section Lemma51

variable {ι : Type*} [DecidableEq ι] {σ τ : Finset ι} {a : ι} {x : ι → ℝ}

private theorem lem51z_nonneg (hx : ∀ i, 0 ≤ x i) (i : ι) : 0 ≤ lem51z σ τ a x i := by
  unfold lem51z
  have hν : 0 ≤ ∑ j ∈ σ \ τ, x j := Finset.sum_nonneg fun j _ ↦ hx j
  split_ifs <;> linarith [hx i]

private theorem lem51z_eq_zero (haσ : a ∈ σ) (haτ : a ∈ τ) (hx : ∀ i ∉ σ, x i = 0) {i : ι}
    (hi : i ∉ σ ∩ τ) : lem51z σ τ a x i = 0 := by
  unfold lem51z
  rw [Finset.mem_inter, not_and_or] at hi
  have hia : i ≠ a := by rintro rfl; exact hi.elim (· haσ) (· haτ)
  rw [ite_eq_right hia, add_zero]
  split_ifs with h
  · exact hx i (hi.resolve_right (not_not.2 h))
  · rfl

private theorem sum_lem51z {s : Finset ι} (ha : a ∈ s) (hσs : σ ⊆ s) (hx : ∀ i ∉ σ, x i = 0) :
    ∑ i ∈ s, lem51z σ τ a x i = ∑ i ∈ s, x i := by
  unfold lem51z
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' s a, ite_eq_left ha]
  have h1 : ∑ i ∈ s, x i = ∑ i ∈ s, ((if i ∈ τ then x i else 0) + if i ∈ τ then 0 else x i) :=
    Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp
  rw [h1, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_subset (Finset.sdiff_subset.trans hσs)
    (f := fun i ↦ if i ∈ τ then 0 else x i) ?_]
  · exact Finset.sum_congr rfl fun i hi ↦ (ite_eq_right (Finset.mem_sdiff.1 hi).2).symm
  · intro i _ hi
    rw [Finset.mem_sdiff, not_and_or, not_not] at hi
    rcases hi with hi | hi
    · simp [hx i hi]
    · exact ite_eq_left hi

private theorem lem51z_ineq {s : Finset ι} {y : ι → ℝ} {n : ℕ} (ha : a ∈ s) (haτ : a ∈ τ)
    (hsub : σ \ τ ⊆ s) (hcard : (σ \ τ).card ≤ n) (hy : ∀ i ∉ τ, y i = 0) :
    ∑ i ∈ s, (x i - lem51z σ τ a x i) ^ 2 + ∑ i ∈ s, (lem51z σ τ a x i - y i) ^ 2 ≤
      (3 * n + 2) * ∑ i ∈ s, (x i - y i) ^ 2 := by
  set ν := ∑ j ∈ σ \ τ, x j
  have hpt : ∀ i, (x i - lem51z σ τ a x i) ^ 2 + (lem51z σ τ a x i - y i) ^ 2 ≤
      2 * (x i - y i) ^ 2 + if i = a then 3 * ν ^ 2 else 0 := by
    intro i
    unfold lem51z
    by_cases hia : i = a
    · subst hia
      rw [ite_eq_left haτ, ite_eq_left rfl, ite_eq_left rfl]
      nlinarith [sq_nonneg (x i - y i - ν)]
    · rw [ite_eq_right hia, ite_eq_right hia, add_zero, add_zero]
      by_cases hiτ : i ∈ τ
      · rw [ite_eq_left hiτ]; nlinarith [sq_nonneg (x i - y i)]
      · rw [ite_eq_right hiτ, hy i hiτ]; nlinarith [sq_nonneg (x i)]
  have hsum : ∑ i ∈ s, ((x i - lem51z σ τ a x i) ^ 2 + (lem51z σ τ a x i - y i) ^ 2) ≤
      2 * ∑ i ∈ s, (x i - y i) ^ 2 + 3 * ν ^ 2 := by
    calc _ ≤ ∑ i ∈ s, (2 * (x i - y i) ^ 2 + if i = a then 3 * ν ^ 2 else 0) :=
          Finset.sum_le_sum fun i _ ↦ hpt i
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' s a, ite_eq_left ha]
  have hνsq : ν ^ 2 ≤ n * ∑ i ∈ s, (x i - y i) ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (σ \ τ) x (fun _ ↦ (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hcs
    calc ν ^ 2 ≤ (σ \ τ).card * ∑ j ∈ σ \ τ, x j ^ 2 := by rw [mul_comm]; exact hcs
      _ = (σ \ τ).card * ∑ j ∈ σ \ τ, (x j - y j) ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl fun j hj ↦ by rw [hy j (Finset.mem_sdiff.1 hj).2, sub_zero]
      _ ≤ n * ∑ i ∈ s, (x i - y i) ^ 2 := by
          gcongr
  rw [← Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i ∈ s, (x i - y i) ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  nlinarith

/-- The final estimate of Lemma 5.1 (and of the vertex estimate). -/
private theorem sqrt_add_sqrt_le {n : ℕ} (hn : 1 ≤ n) {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A + B ≤ (3 * n + 2) * C) : √A + √B ≤ 4 * √(n : ℝ) * √C := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC : 0 ≤ C := by nlinarith
  refine le_of_sq_le_sq ?_ (by positivity)
  have e1 := Real.sq_sqrt hA
  have e2 := Real.sq_sqrt hB
  have e3 : (4 * √(n : ℝ) * √C) ^ 2 = 16 * n * C := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hC]; ring
  rw [e3]
  nlinarith [sq_nonneg (√A - √B)]

end Lemma51

omit [DecidableEq V] in
/-- A face with a single vertex is a point. -/
private theorem eq_of_mem_face_singleton {a : V} {x y : EuclideanSpace ℝ V} (hx : x ∈ face {a})
    (hy : y ∈ face {a}) : x = y := by
  classical
  have key : ∀ z ∈ face ({a} : Finset V), ∀ i, z i = if i = a then 1 else 0 := by
    rintro z ⟨-, hz1, hz⟩ i
    have hza : ∀ j, j ≠ a → z j = 0 := fun j hj ↦ hz j (by simpa using hj)
    split_ifs with hi
    · subst hi
      rw [← hz1, Finset.sum_eq_single i (fun j _ hj ↦ hza j hj) (by simp)]
    · exact hza i hi
  ext i
  rw [key x hx, key y hy]

omit [DecidableEq V] in
/-- **Lemma 5.1** of [Basso2024]: if two `n`-simplices `Δ = face σ` and `Δ' = face τ` meet, then
for `x ∈ Δ`, `y ∈ Δ'` there is `z ∈ Δ ∩ Δ'` with `|x - z| + |z - y| ≤ 4 √n |x - y|`. -/
theorem exists_mem_face_inter_dist_add_dist_le {n : ℕ} {σ τ : Finset V} (hσ : σ.card = n + 1)
    (hτ : τ.card = n + 1) (hστ : (face σ ∩ face τ).Nonempty) {x y : EuclideanSpace ℝ V}
    (hx : x ∈ face σ) (hy : y ∈ face τ) :
    ∃ z ∈ face σ ∩ face τ, dist x z + dist z y ≤ 4 * √(n : ℝ) * dist x y := by
  classical
  rw [face_inter, face_nonempty_iff] at hστ
  obtain ⟨a, ha⟩ := hστ
  have haσ := (Finset.mem_inter.1 ha).1
  have haτ := (Finset.mem_inter.1 ha).2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `σ = τ = {a}`, so `x = y`
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 hσ
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.1 hτ
    rw [Finset.mem_singleton] at haσ haτ
    subst haσ haτ
    obtain rfl := eq_of_mem_face_singleton hx hy
    exact ⟨x, ⟨hx, hy⟩, by simp⟩
  have hcard : (σ \ τ).card ≤ n := by
    have h1 := Finset.card_sdiff_add_card_inter σ τ
    have h2 : 0 < (σ ∩ τ).card := Finset.card_pos.2 ⟨a, ha⟩
    omega
  refine ⟨WithLp.toLp 2 (lem51z σ τ a x), ?_, ?_⟩
  · rw [face_inter]
    refine ⟨fun i ↦ lem51z_nonneg hx.1 i, ?_, fun i hi ↦ lem51z_eq_zero haσ haτ hx.2.2 hi⟩
    dsimp only
    rw [sum_lem51z (Finset.mem_univ a) (Finset.subset_univ σ) hx.2.2]
    exact hx.2.1
  · simp only [EuclideanSpace.dist_eq, Real.dist_eq, sq_abs]
    exact sqrt_add_sqrt_le hn (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      (lem51z_ineq (Finset.mem_univ a) haτ (Finset.subset_univ _) hcard hy.2.2)

/-! ### The vertex estimate -/

omit [DecidableEq V] in
/-- `1 ≤ (n + 1) ∑_{i ∈ σ} x_i²` for `x` in a face with at most `n + 1` vertices. -/
private theorem one_le_mul_sum_sq {n : ℕ} {σ : Finset V} (hσ : σ.card ≤ n + 1)
    {x : EuclideanSpace ℝ V} (hx : x ∈ face σ) : 1 ≤ (n + 1) * ∑ i ∈ σ, x i ^ 2 := by
  have hsum : ∑ i ∈ σ, x i = 1 := by
    rw [← hx.2.1]; exact Finset.sum_subset (Finset.subset_univ σ) fun i _ hi ↦ hx.2.2 i hi
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq σ (fun i ↦ x i) (fun _ ↦ (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, hsum] at hcs
  have hc : (σ.card : ℝ) ≤ n + 1 := by exact_mod_cast hσ
  have h0 : 0 ≤ ∑ i ∈ σ, x i ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  nlinarith

/-- The vertex estimate in the proof of Lemma 5.2 of [Basso2024]: if `x ∈ face σ` and
`y ∈ face τ`, where `σ` and `τ` are disjoint with at most `n + 1` elements and `n ≥ 1`, then every
vertex `e_w` satisfies `|x - e_w| + |e_w - y| ≤ 4 √n |x - y|`. -/
theorem dist_add_dist_single_le {n : ℕ} (hn : 1 ≤ n) {σ τ : Finset V} (hσ : σ.card ≤ n + 1)
    (hτ : τ.card ≤ n + 1) (hστ : Disjoint σ τ) {x y : EuclideanSpace ℝ V} (hx : x ∈ face σ)
    (hy : y ∈ face τ) (w : V) :
    dist x (EuclideanSpace.single w (1 : ℝ)) + dist (EuclideanSpace.single w (1 : ℝ)) y ≤
      4 * √(n : ℝ) * dist x y := by
  simp only [EuclideanSpace.dist_eq, Real.dist_eq, sq_abs, PiLp.single_apply]
  have hxy : ∀ i, x i * y i = 0 := by
    intro i
    by_cases hi : i ∈ σ
    · rw [hy.2.2 i (Finset.disjoint_left.1 hστ hi), mul_zero]
    · rw [hx.2.2 i hi, zero_mul]
  have hpt : ∀ i, (x i - if i = w then 1 else 0) ^ 2 + ((if i = w then 1 else 0) - y i) ^ 2 ≤
      (x i - y i) ^ 2 + if i = w then 2 else 0 := by
    intro i
    have h1 := hxy i
    have h2 := hx.1 i
    have h3 := hy.1 i
    split_ifs <;> nlinarith
  have hAB : ∑ i, (x i - if i = w then 1 else 0) ^ 2 + ∑ i, ((if i = w then 1 else 0) - y i) ^ 2 ≤
      ∑ i, (x i - y i) ^ 2 + 2 := by
    rw [← Finset.sum_add_distrib]
    calc _ ≤ ∑ i, ((x i - y i) ^ 2 + if i = w then 2 else 0) := Finset.sum_le_sum fun i _ ↦ hpt i
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq' univ w, ite_eq_left (Finset.mem_univ w)]
  have hC : ∑ i ∈ σ, x i ^ 2 + ∑ i ∈ τ, y i ^ 2 ≤ ∑ i, (x i - y i) ^ 2 := by
    have e1 : ∑ i ∈ σ, x i ^ 2 = ∑ i ∈ σ, (x i - y i) ^ 2 := Finset.sum_congr rfl fun i hi ↦ by
      rw [hy.2.2 i (Finset.disjoint_left.1 hστ hi), sub_zero]
    have e2 : ∑ i ∈ τ, y i ^ 2 = ∑ i ∈ τ, (x i - y i) ^ 2 := Finset.sum_congr rfl fun i hi ↦ by
      rw [hx.2.2 i (Finset.disjoint_right.1 hστ hi), zero_sub, neg_sq]
    rw [e1, e2, ← Finset.sum_union hστ]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
  have h1 := one_le_mul_sum_sq hσ hx
  have h2 := one_le_mul_sum_sq hτ hy
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine sqrt_add_sqrt_le hn (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) ?_
  have h0 : 0 ≤ ∑ i ∈ σ, x i ^ 2 + ∑ i ∈ τ, y i ^ 2 :=
    add_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  nlinarith

/-! ### Chains of simplices -/

omit [DecidableEq V] in
/-- A single segment in a face `σ j` is a polygonal path. -/
private theorem polygonal_segment {m : ℕ} (σ : ℕ → Finset V) {j : ℕ} (hj : j ≤ m)
    {x y : EuclideanSpace ℝ V} (hx : x ∈ face (σ j)) (hy : y ∈ face (σ j)) {c : ℝ} (hc : 1 ≤ c) :
    ∃ (l : ℕ) (p : ℕ → EuclideanSpace ℝ V), p 0 = x ∧ p l = y ∧
      (∀ i < l, ∃ j ≤ m, p i ∈ face (σ j) ∧ p (i + 1) ∈ face (σ j)) ∧
      ∑ i ∈ range l, dist (p i) (p (i + 1)) ≤ c * dist x y := by
  refine ⟨1, fun i ↦ if i = 0 then x else y, by simp, by simp, fun i hi ↦ ?_, ?_⟩
  · obtain rfl : i = 0 := by omega
    exact ⟨j, hj, by simpa using hx, by simpa using hy⟩
  · simp only [Finset.sum_range_one, ite_true, zero_add, one_ne_zero, ite_false]
    nlinarith [dist_nonneg (x := x) (y := y)]

omit [DecidableEq V] in
/-- Polygonal paths along chains of `n`-simplices (proof of Lemma 5.2 of [Basso2024], errata
item 3): let `σ 0, …, σ m` be `(n + 1)`-sets, `n ≥ 1`, such that consecutive faces meet,
non-consecutive ones are disjoint and `m + 1 ≤ 2^k`. Then any `x ∈ face (σ 0)` and
`y ∈ face (σ m)` are joined by points `x = p 0, …, p l = y`, each two consecutive ones in a common
face `face (σ j)`, with `∑ |p i - p (i + 1)| ≤ (4 √n)^k |x - y|`. -/
theorem exists_polygonal_of_chain {n : ℕ} (hn : 1 ≤ n) {m k : ℕ} (σ : ℕ → Finset V)
    (hcard : ∀ j ≤ m, (σ j).card = n + 1)
    (hmeet : ∀ j < m, (face (σ j) ∩ face (σ (j + 1))).Nonempty)
    (hdisj : ∀ i j, i + 2 ≤ j → j ≤ m → Disjoint (σ i) (σ j)) (hk : m + 1 ≤ 2 ^ k)
    {x y : EuclideanSpace ℝ V} (hx : x ∈ face (σ 0)) (hy : y ∈ face (σ m)) :
    ∃ (l : ℕ) (p : ℕ → EuclideanSpace ℝ V), p 0 = x ∧ p l = y ∧
      (∀ i < l, ∃ j ≤ m, p i ∈ face (σ j) ∧ p (i + 1) ∈ face (σ j)) ∧
      ∑ i ∈ range l, dist (p i) (p (i + 1)) ≤ (4 * √(n : ℝ)) ^ k * dist x y := by
  classical
  have hc : (1 : ℝ) ≤ 4 * √(n : ℝ) := by
    have : (1 : ℝ) ≤ √(n : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hn)
    linarith
  induction k generalizing m σ x y with
  | zero =>
    have hm : m = 0 := by simpa using hk
    subst hm
    exact polygonal_segment σ le_rfl hx hy (by simp)
  | succ k ih =>
    have hck : (1 : ℝ) ≤ (4 * √(n : ℝ)) ^ k := one_le_pow₀ hc
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · exact polygonal_segment σ le_rfl hx hy (one_le_pow₀ hc)
      · -- two faces that meet: Lemma 5.1
        obtain ⟨z, ⟨hz0, hz1⟩, hz⟩ := exists_mem_face_inter_dist_add_dist_le (hcard 0 (by omega))
          (hcard 1 le_rfl) (hmeet 0 (by omega)) hx hy
        refine ⟨2, fun i ↦ if i = 0 then x else if i = 1 then z else y, by simp, by simp,
          fun i hi ↦ ?_, ?_⟩
        · interval_cases i
          · exact ⟨0, by omega, by simpa using hx, by simpa using hz0⟩
          · exact ⟨1, le_rfl, by simpa using hz1, by simpa using hy⟩
        · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
          simp only [ite_true, one_ne_zero, ite_false]
          calc dist x z + dist z y ≤ 4 * √(n : ℝ) * dist x y := hz
            _ ≤ (4 * √(n : ℝ)) ^ k * (4 * √(n : ℝ) * dist x y) :=
                le_mul_of_one_le_left (by positivity) hck
            _ = (4 * √(n : ℝ)) ^ (k + 1) * dist x y := by ring
    · -- `σ 0` and `σ m` are disjoint: split the chain at a vertex of `σ (m / 2) ∩ σ (m / 2 + 1)`
      set m₁ := m / 2 with hm₁
      have hk' : m + 1 ≤ 2 * 2 ^ k := by rwa [pow_succ, mul_comm] at hk
      have hk₁ : m₁ + 1 ≤ 2 ^ k := by omega
      have hk₂ : m - (m₁ + 1) + 1 ≤ 2 ^ k := by omega
      obtain ⟨w, hw⟩ := (face_nonempty_iff _).1
        (face_inter (σ m₁) (σ (m₁ + 1)) ▸ hmeet m₁ (by omega))
      rw [Finset.mem_inter] at hw
      have hvert := dist_add_dist_single_le hn (hcard 0 (by omega)).le (hcard m le_rfl).le
        (hdisj 0 m (by omega) le_rfl) hx hy w
      obtain ⟨l₁, p₁, h0₁, hl₁, hseg₁, hsum₁⟩ := ih (m := m₁) σ
        (fun j hj ↦ hcard j (by omega)) (fun j hj ↦ hmeet j (by omega))
        (fun i j hij hj ↦ hdisj i j hij (by omega)) hk₁ hx (single_mem_face hw.1)
      obtain ⟨l₂, p₂, h0₂, hl₂, hseg₂, hsum₂⟩ := ih (m := m - (m₁ + 1))
        (fun j ↦ σ (m₁ + 1 + j)) (fun j hj ↦ hcard _ (by omega))
        (fun j hj ↦ hmeet (m₁ + 1 + j) (by omega))
        (fun i j hij hj ↦ hdisj _ _ (by omega) (by omega)) hk₂
        (by simpa using single_mem_face hw.2)
        (by rwa [show m₁ + 1 + (m - (m₁ + 1)) = m by omega])
      obtain ⟨p, hp⟩ : ∃ p : ℕ → EuclideanSpace ℝ V,
          ∀ i, p i = if i ≤ l₁ then p₁ i else p₂ (i - l₁) := ⟨_, fun i ↦ rfl⟩
      have hp1 : ∀ i ≤ l₁, p i = p₁ i := fun i hi ↦ by rw [hp, ite_eq_left hi]
      have hp2 : ∀ i, p (l₁ + i) = p₂ i := by
        intro i
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · rw [add_zero, hp1 l₁ le_rfl, hl₁, h0₂]
        · rw [hp, ite_eq_right (by omega), Nat.add_sub_cancel_left]
      refine ⟨l₁ + l₂, p, by rw [hp1 0 (Nat.zero_le _), h0₁], by rw [hp2, hl₂], fun i hi ↦ ?_, ?_⟩
      · by_cases hi₁ : i < l₁
        · obtain ⟨j, hj, h1, h2⟩ := hseg₁ i hi₁
          exact ⟨j, by omega, by rwa [hp1 i hi₁.le], by rwa [hp1 (i + 1) hi₁]⟩
        · obtain ⟨i', rfl⟩ : ∃ i', i = l₁ + i' := ⟨i - l₁, by omega⟩
          obtain ⟨j, hj, h1, h2⟩ := hseg₂ i' (by omega)
          refine ⟨m₁ + 1 + j, by omega, by rwa [hp2], ?_⟩
          rw [show l₁ + i' + 1 = l₁ + (i' + 1) by omega, hp2]
          exact h2
      · rw [Finset.sum_range_add]
        have e1 : ∑ i ∈ range l₁, dist (p i) (p (i + 1)) =
            ∑ i ∈ range l₁, dist (p₁ i) (p₁ (i + 1)) := Finset.sum_congr rfl fun i hi ↦ by
          rw [Finset.mem_range] at hi
          rw [hp1 i hi.le, hp1 (i + 1) hi]
        have e2 : ∑ i ∈ range l₂, dist (p (l₁ + i)) (p (l₁ + i + 1)) =
            ∑ i ∈ range l₂, dist (p₂ i) (p₂ (i + 1)) := Finset.sum_congr rfl fun i _ ↦ by
          rw [hp2, add_assoc, hp2]
        rw [e1, e2]
        calc _ ≤ (4 * √(n : ℝ)) ^ k * dist x (EuclideanSpace.single w 1) +
              (4 * √(n : ℝ)) ^ k * dist (EuclideanSpace.single w 1) y := add_le_add hsum₁ hsum₂
          _ = (4 * √(n : ℝ)) ^ k * (dist x (EuclideanSpace.single w 1) +
              dist (EuclideanSpace.single w 1) y) := by ring
          _ ≤ (4 * √(n : ℝ)) ^ k * (4 * √(n : ℝ) * dist x y) := by gcongr
          _ = (4 * √(n : ℝ)) ^ (k + 1) * dist x y := by ring

end Triangulation

/-! ### Lemma 5.1 for simplices in `ℓ₂(I)` -/

/-- A simplex with a single vertex is a point. -/
private theorem eq_of_mem_simplex_singleton {I : Type*} {a : I} {x y : I →₀ ℝ}
    (hx : x ∈ simplex {a}) (hy : y ∈ simplex {a}) : x = y := by
  obtain ⟨-, hxs, hx1⟩ := hx
  obtain ⟨-, hys, hy1⟩ := hy
  rw [Finset.sum_singleton] at hx1 hy1
  ext i
  by_cases hi : i = a
  · rw [hi, hx1, hy1]
  · have hx0 : x i = 0 := Finsupp.notMem_support_iff.1 fun h ↦ hi (by simpa using hxs h)
    have hy0 : y i = 0 := Finsupp.notMem_support_iff.1 fun h ↦ hi (by simpa using hys h)
    rw [hx0, hy0]

/-- **Lemma 5.1** of [Basso2024] in the paper's setting (simplices of `Σ(I) ⊆ ℓ₂(I)` for an
arbitrary index set `I`, with the `ℓ₂`-distance `l2dist` on finitely supported points): if two
`n`-simplices `Δ = simplex σ` and `Δ' = simplex τ` meet, then for `x ∈ Δ`, `y ∈ Δ'` there is
`z ∈ Δ ∩ Δ'` with `|x - z| + |z - y| ≤ 4 √n |x - y|`. -/
theorem exists_mem_simplex_inter_l2dist_le {I : Type*} {n : ℕ} {σ τ : Finset I}
    (hσ : σ.card = n + 1) (hτ : τ.card = n + 1) (hστ : (simplex σ ∩ simplex τ).Nonempty)
    {x y : I →₀ ℝ} (hx : x ∈ simplex σ) (hy : y ∈ simplex τ) :
    ∃ z ∈ simplex σ ∩ simplex τ, l2dist x z + l2dist z y ≤ 4 * √(n : ℝ) * l2dist x y := by
  classical
  -- a common vertex `a`
  obtain ⟨w, ⟨-, -, hw1⟩, ⟨-, hwτ, -⟩⟩ := hστ
  obtain ⟨a, haσ, hwa⟩ : ∃ a ∈ σ, w a ≠ 0 := by
    by_contra! h
    rw [Finset.sum_eq_zero h] at hw1
    exact zero_ne_one hw1
  have haτ : a ∈ τ := hwτ (Finsupp.mem_support_iff.2 hwa)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `σ = τ = {a}`, so `x = y`
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 hσ
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.1 hτ
    rw [Finset.mem_singleton] at haσ haτ
    subst haσ haτ
    obtain rfl := eq_of_mem_simplex_singleton hx hy
    exact ⟨x, ⟨hx, hy⟩, by simp [l2dist_self]⟩
  obtain ⟨hx0, hxs, hx1⟩ := hx
  obtain ⟨-, hys, -⟩ := hy
  have hxσ : ∀ i ∉ σ, x i = 0 := fun i hi ↦ Finsupp.notMem_support_iff.1 fun h ↦ hi (hxs h)
  have hyτ : ∀ i ∉ τ, y i = 0 := fun i hi ↦ Finsupp.notMem_support_iff.1 fun h ↦ hi (hys h)
  have hcard : (σ \ τ).card ≤ n := by
    have h1 := Finset.card_sdiff_add_card_inter σ τ
    have h2 : 0 < (σ ∩ τ).card := Finset.card_pos.2 ⟨a, Finset.mem_inter.2 ⟨haσ, haτ⟩⟩
    omega
  have hz0 : ∀ i, i ∉ σ ∩ τ → Triangulation.lem51z σ τ a x i = 0 := fun i hi ↦
    Triangulation.lem51z_eq_zero haσ haτ hxσ hi
  set z : I →₀ ℝ := Finsupp.onFinset (σ ∩ τ) (Triangulation.lem51z σ τ a x)
    (fun i hi ↦ by by_contra h; exact hi (hz0 i h))
  have hzs : (↑z.support : Set I) ⊆ ↑(σ ∩ τ) := fun i hi ↦ by
    by_contra h
    exact Finsupp.mem_support_iff.1 hi (hz0 i h)
  have hσs : σ ⊆ σ ∪ τ := Finset.subset_union_left
  have hxs' : (↑x.support : Set I) ⊆ ↑(σ ∪ τ) := hxs.trans (Finset.coe_subset.2 hσs)
  have hys' : (↑y.support : Set I) ⊆ ↑(σ ∪ τ) :=
    hys.trans (Finset.coe_subset.2 Finset.subset_union_right)
  have hzs' : (↑z.support : Set I) ⊆ ↑(σ ∪ τ) :=
    hzs.trans (Finset.coe_subset.2 (Finset.inter_subset_left.trans hσs))
  have hzmem : z ∈ simplex (σ ∩ τ) := by
    refine ⟨fun i ↦ Triangulation.lem51z_nonneg hx0 i, hzs, ?_⟩
    have e1 : ∑ i ∈ σ ∩ τ, z i = ∑ i ∈ σ ∪ τ, z i :=
      Finset.sum_subset (Finset.inter_subset_left.trans hσs) fun i _ hi ↦ hz0 i hi
    have e2 : ∑ i ∈ σ ∪ τ, z i = ∑ i ∈ σ ∪ τ, x i :=
      Triangulation.sum_lem51z (Finset.mem_union_left _ haσ) hσs hxσ
    have e3 : ∑ i ∈ σ, x i = ∑ i ∈ σ ∪ τ, x i :=
      Finset.sum_subset hσs fun i _ hi ↦ hxσ i hi
    rw [e1, e2, ← e3, hx1]
  refine ⟨z, ⟨simplex_mono Finset.inter_subset_left hzmem,
    simplex_mono Finset.inter_subset_right hzmem⟩, ?_⟩
  rw [l2dist_eq_sqrt_sum hxs' hzs', l2dist_eq_sqrt_sum hzs' hys', l2dist_eq_sqrt_sum hxs' hys']
  exact Triangulation.sqrt_add_sqrt_le hn (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    (Triangulation.lem51z_ineq (Finset.mem_union_left _ haσ) haτ
      (Finset.sdiff_subset.trans hσs) hcard hyτ)

end LipschitzExtension
