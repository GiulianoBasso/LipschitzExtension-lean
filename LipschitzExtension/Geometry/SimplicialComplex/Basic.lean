/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Simplicial complexes in `ℓ₂(I)` and simplicial extensors

This file sets up the simplicial complexes of Section 5 of [Basso2024] and defines simplicial
extensors (Definition 6.1 of [Basso2024]), which enter Theorem 6.1 and Proposition 8.1.

For an index set `I`, points of `Σ(I) = {x ∈ ℓ₂(I) | x ≥ 0, ∑ x_i = 1}` that lie in some simplex
have finite support, so we model them by finitely supported functions `I →₀ ℝ` with the `ℓ₂`
distance `l2dist`. For a finite set `σ ⊆ I` the simplex `simplex σ` consists of the weights
`x ≥ 0` supported in `σ` with `∑_{i ∈ σ} x i = 1`; its vertices are the `e_i = Finsupp.single i 1`,
at mutual distance `√2`. A simplicial complex of dimension `≤ n` is encoded abstractly by its set
of faces (nonempty finite subsets of `I` with at most `n + 1` elements, closed under passing to
nonempty subsets).

**Definition 6.1.** `Y` is an `(n, C)`-simplicial extensor if, whenever `Σ` is a simplicial
complex of dimension at most `n` (with the `ℓ₂`-metric) and `f : Σ⁽⁰⁾ → Y` is a map, then `f`
admits an extension `F : Σ → Y` with `Lip F|_Δ ≤ C · Lip f|_{Δ⁽⁰⁾}` for every simplex `Δ ⊆ Σ`.

## Main definitions

* `l2dist`: the `ℓ₂` distance between finitely supported functions `I →₀ ℝ`.
* `simplex σ`, `simplexBoundary σ`: the simplex spanned by the vertices `e_i`, `i ∈ σ`, and its
  boundary.
* `IsSComplex n K`: `K` is the set of faces of an abstract simplicial complex of dimension at
  most `n`.
* `SimplicialExtensor n C Y`: `Y` is an `(n, C)`-simplicial extensor (Definition 6.1).

## Main statements

* `l2dist_triangle`: the triangle inequality for `l2dist`.
* `l2dist_eq_dist_euclidean`: on points supported in `σ`, `l2dist` is the distance of
  `EuclideanSpace ℝ σ`.
* `l2dist_le_sqrt_two`: the simplices have diameter at most `√2`.

## Implementation notes

We formulate `Lip F|_Δ ≤ C · Lip f|_{Δ⁽⁰⁾}` as: for every `L ≥ 0` such that `f` is `L`-Lipschitz
on the vertices of `Δ` (i.e. `d(f e_i, f e_j) ≤ L √2`), `F` is `C L`-Lipschitz on `Δ`. The
extension `F` is a function on all of `I →₀ ℝ`; only its values on the simplices of the complex
matter. The universe of the index sets `I` is a parameter of `SimplicialExtensor`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open Set Finset

namespace LipschitzExtension

universe u v

variable {I : Type*}

/-- The `ℓ₂` distance between finitely supported functions. -/
noncomputable def l2dist (x y : I →₀ ℝ) : ℝ :=
  Real.sqrt ((x - y).sum fun _ a ↦ a ^ 2)

/-- The simplex spanned by the vertices `e_i`, `i ∈ σ`. -/
def simplex (σ : Finset I) : Set (I →₀ ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (↑x.support : Set I) ⊆ ↑σ ∧ ∑ i ∈ σ, x i = 1}

/-- The boundary `∂σ` of the simplex `σ`: the points of the simplex with a vanishing coordinate
in `σ`, i.e. the union of the proper faces. -/
def simplexBoundary (σ : Finset I) : Set (I →₀ ℝ) :=
  {x | x ∈ simplex σ ∧ ∃ i ∈ σ, x i = 0}

/-- `IsSComplex n K`: `K` is (the set of faces of) an abstract simplicial complex of dimension
at most `n` with vertices in `I`. Its geometric realization is the union of the simplices
`simplex σ`, `σ ∈ K`. -/
structure IsSComplex (n : ℕ) (K : Set (Finset I)) : Prop where
  /-- Every face is nonempty. -/
  nonempty : ∀ σ ∈ K, σ.Nonempty
  /-- Every face has at most `n + 1` vertices. -/
  card_le : ∀ σ ∈ K, σ.card ≤ n + 1
  /-- Nonempty subsets of faces are faces. -/
  down : ∀ σ ∈ K, ∀ τ ⊆ σ, τ.Nonempty → τ ∈ K

/-- **Definition 6.1** of [Basso2024]: `Y` is an `(n, C)`-simplicial extensor if every map
`g : I → Y` on the vertices of a simplicial complex `K` of dimension at most `n` extends to a map
`G` with `G e_i = g i` which is `C L`-Lipschitz (for `l2dist`) on every simplex `σ ∈ K` on whose
vertices `g` is `L`-Lipschitz, i.e. `d(g i, g j) ≤ L √2` for `i, j ∈ σ`. (The universe `u` of the
index sets is a parameter.) -/
def SimplicialExtensor (n : ℕ) (C : ℝ) (Y : Type v) [PseudoMetricSpace Y] : Prop :=
  ∀ (I : Type u) (K : Set (Finset I)), IsSComplex n K → ∀ g : I → Y,
    ∃ G : (I →₀ ℝ) → Y, (∀ i, G (Finsupp.single i 1) = g i) ∧
      ∀ σ ∈ K, ∀ L : ℝ, 0 ≤ L → (∀ i ∈ σ, ∀ j ∈ σ, dist (g i) (g j) ≤ L * Real.sqrt 2) →
        ∀ x ∈ simplex σ, ∀ y ∈ simplex σ, dist (G x) (G y) ≤ C * L * l2dist x y

/-! ### Basic properties of `l2dist` -/

theorem l2dist_nonneg (x y : I →₀ ℝ) : 0 ≤ l2dist x y := Real.sqrt_nonneg _

theorem l2dist_comm (x y : I →₀ ℝ) : l2dist x y = l2dist y x := by
  unfold l2dist
  rw [← neg_sub, Finsupp.sum_neg_index (fun _ ↦ by simp)]
  simp only [neg_sq]

theorem l2dist_self (x : I →₀ ℝ) : l2dist x x = 0 := by
  simp [l2dist]

/-- For functions supported in `s`, `l2dist` is the Euclidean distance of the restrictions. -/
theorem l2dist_eq_sqrt_sum {s : Finset I} {x y : I →₀ ℝ} (hx : (↑x.support : Set I) ⊆ ↑s)
    (hy : (↑y.support : Set I) ⊆ ↑s) : l2dist x y = Real.sqrt (∑ i ∈ s, (x i - y i) ^ 2) := by
  classical
  unfold l2dist
  have hxy : (x - y).support ⊆ s := fun i hi ↦
    Finset.mem_union.mp (Finsupp.support_sub hi) |>.elim (fun h ↦ hx h) (fun h ↦ hy h)
  rw [Finsupp.sum_of_support_subset _ hxy _ (fun _ _ ↦ by simp)]
  simp only [Finsupp.coe_sub, Pi.sub_apply]

/-- The restriction to `σ` is an isometry onto its image in `EuclideanSpace ℝ σ`. -/
theorem l2dist_eq_dist_euclidean {σ : Finset I} {x y : I →₀ ℝ} (hx : (↑x.support : Set I) ⊆ ↑σ)
    (hy : (↑y.support : Set I) ⊆ ↑σ) :
    l2dist x y = dist (WithLp.toLp 2 (fun i : σ ↦ x i) : EuclideanSpace ℝ σ)
      (WithLp.toLp 2 (fun i : σ ↦ y i)) := by
  rw [l2dist_eq_sqrt_sum hx hy, EuclideanSpace.dist_eq]
  congr 1
  simp only [Real.dist_eq, sq_abs]
  exact (Finset.sum_coe_sort σ (fun i ↦ (x i - y i) ^ 2)).symm

/-- The triangle inequality for `l2dist`. -/
theorem l2dist_triangle (x y z : I →₀ ℝ) : l2dist x z ≤ l2dist x y + l2dist y z := by
  classical
  have hx : (↑x.support : Set I) ⊆ ↑(x.support ∪ y.support ∪ z.support) := by
    intro i hi; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hi ⊢; tauto
  have hy : (↑y.support : Set I) ⊆ ↑(x.support ∪ y.support ∪ z.support) := by
    intro i hi; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hi ⊢; tauto
  have hz : (↑z.support : Set I) ⊆ ↑(x.support ∪ y.support ∪ z.support) := by
    intro i hi; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hi ⊢; tauto
  rw [l2dist_eq_dist_euclidean hx hz, l2dist_eq_dist_euclidean hx hy,
    l2dist_eq_dist_euclidean hy hz]
  exact dist_triangle _ _ _

/-- `ℓ₂ ≤ ℓ₁`: for functions supported in `s`, `l2dist x y ≤ ∑ i ∈ s, |x i - y i|`. -/
theorem l2dist_le_sum_abs {s : Finset I} {x y : I →₀ ℝ} (hx : (↑x.support : Set I) ⊆ ↑s)
    (hy : (↑y.support : Set I) ⊆ ↑s) : l2dist x y ≤ ∑ i ∈ s, |x i - y i| := by
  rw [l2dist_eq_sqrt_sum hx hy, Real.sqrt_le_left (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)]
  calc ∑ i ∈ s, (x i - y i) ^ 2 = ∑ i ∈ s, |x i - y i| ^ 2 := by simp only [sq_abs]
    _ ≤ (∑ i ∈ s, |x i - y i|) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ ↦ abs_nonneg _

/-- Distinct vertices `e_i`, `e_j` are at distance `√2`. -/
theorem l2dist_single_single {i j : I} (hij : i ≠ j) :
    l2dist (Finsupp.single i (1 : ℝ)) (Finsupp.single j 1) = Real.sqrt 2 := by
  classical
  have hi : (↑(Finsupp.single i (1 : ℝ)).support : Set I) ⊆ ↑({i, j} : Finset I) := by
    intro k hk
    have := Finsupp.support_single_subset hk
    simp only [Finset.mem_singleton] at this
    simp [this]
  have hj : (↑(Finsupp.single j (1 : ℝ)).support : Set I) ⊆ ↑({i, j} : Finset I) := by
    intro k hk
    have := Finsupp.support_single_subset hk
    simp only [Finset.mem_singleton] at this
    simp [this]
  rw [l2dist_eq_sqrt_sum hi hj, Finset.sum_pair hij]
  simp [hij, hij.symm]
  norm_num

/-- Any two points of a simplex are at distance at most `√2`. -/
theorem l2dist_le_sqrt_two {σ : Finset I} {x y : I →₀ ℝ} (hx : x ∈ simplex σ)
    (hy : y ∈ simplex σ) : l2dist x y ≤ Real.sqrt 2 := by
  obtain ⟨hx0, hxs, hx1⟩ := hx
  obtain ⟨hy0, hys, hy1⟩ := hy
  rw [l2dist_eq_sqrt_sum hxs hys]
  apply Real.sqrt_le_sqrt
  have hxle : ∀ i ∈ σ, x i ≤ 1 := fun i hi ↦
    hx1 ▸ Finset.single_le_sum (fun j _ ↦ hx0 j) hi
  have hyle : ∀ i ∈ σ, y i ≤ 1 := fun i hi ↦
    hy1 ▸ Finset.single_le_sum (fun j _ ↦ hy0 j) hi
  calc ∑ i ∈ σ, (x i - y i) ^ 2 ≤ ∑ i ∈ σ, (x i + y i) :=
        Finset.sum_le_sum fun i hi ↦ by
          nlinarith [hx0 i, hy0 i, hxle i hi, hyle i hi, mul_nonneg (hx0 i) (hy0 i),
            mul_nonneg (hx0 i) (sub_nonneg.mpr (hxle i hi)),
            mul_nonneg (hy0 i) (sub_nonneg.mpr (hyle i hi))]
    _ = 2 := by rw [Finset.sum_add_distrib, hx1, hy1]; norm_num

/-- The vertex `e_i` lies in `simplex σ` for `i ∈ σ`. -/
theorem single_mem_simplex {σ : Finset I} {i : I} (hi : i ∈ σ) :
    Finsupp.single i (1 : ℝ) ∈ simplex σ := by
  classical
  refine ⟨fun j ↦ ?_, fun j hj ↦ ?_, ?_⟩
  · rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  · have := Finsupp.support_single_subset hj
    rw [Finset.mem_singleton] at this
    rw [this]
    exact hi
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      exact Finsupp.single_eq_of_ne hb
    · intro h
      exact absurd hi h

/-- Monotonicity: `simplex σ ⊆ simplex τ` for `σ ⊆ τ`. -/
theorem simplex_mono {σ τ : Finset I} (h : σ ⊆ τ) : simplex σ ⊆ simplex τ := by
  rintro x ⟨hx0, hxs, hx1⟩
  refine ⟨hx0, hxs.trans (Finset.coe_subset.mpr h), ?_⟩
  rw [← hx1]
  symm
  apply Finset.sum_subset h
  intro i _ hi
  by_contra hne
  exact hi (hxs (Finsupp.mem_support_iff.mpr hne))

end LipschitzExtension
