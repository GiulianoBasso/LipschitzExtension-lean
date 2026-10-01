/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.Simplex

/-!
# Lipschitz connected spaces are simplicial extensors

This file proves Proposition 8.1 of [Basso2024]: if `Y` satisfies `LC(n - 1, λ)`, then every map
`f : Σ⁽⁰⁾ → Y` on the vertices of an `n`-dimensional simplicial complex `Σ` (with the `ℓ₂`-metric)
admits an extension `F : Σ → Y` with `Lip F|_Δ ≤ λⁿ (√2)ⁿ⁻¹ √n (n!)² · Lip f|_{Δ⁽⁰⁾}` for every
simplex `Δ ⊆ Σ`. In the terminology of Definition 6.1 of [Basso2024], `Y` is an
`(n, λⁿ (√2)ⁿ⁻¹ √n (n!)²)`-simplicial extensor.

## Main definitions

* `IsBoundaryExtOp n Λ E`: `E` is a choice of extensions from the boundaries of the simplices with
  `2` to `n + 1` vertices, with the constant of Lemma 7.2.
* `skel K g y₀ E k`: the `k`-th skeleton map `F_k` of the induction.

## Main statements

* `exists_isBoundaryExtOp`: boundary extension operators exist under `LC(n - 1, Λ)`, by Lemma 7.2.
* `skel_lipschitz`: the main estimate of the skeleton induction.
* `LipschitzConnected.simplicialExtensor`: Proposition 8.1 of [Basso2024] (for `λ ≥ 1`).

## Implementation notes

Simplicial complexes, the `ℓ₂`-metric and simplicial extensors are as in
`LipschitzExtension.Geometry.SimplicialComplex.Basic`. The formal statement of Proposition 8.1
assumes `λ ≥ 1`, a standing assumption of Section 8 of [Basso2024], and `Nonempty Y`, since the
skeleton maps take an arbitrary value `y₀` off the vertices. For `n = 0`, the hypothesis
`LC(n - 1, λ)` reads `LC(0, λ)` because `n - 1` is truncated subtraction.

## Proof outline

We follow the skeleton induction of the paper. Put `F_0(e_i) = g i` at the vertices (and
`F_0 = y₀` elsewhere). Given `F_(k-1)`, for each face `σ ∈ K` with `k + 1` vertices choose an
extension `E_σ` of the restriction of `F_(k-1)` to `∂σ` (Lemma 7.2,
`LipschitzConnected.exists_simplex_extension`), and put `F_k(x) = E_σ(x)` if the support of `x`
is exactly such a face `σ`, and `F_k(x) = F_(k-1)(x)` otherwise. Then `F_k = E_σ` on `simplex σ`.
With `C_j = λ^j (√2)^(j-1) √j (j!)²` we have `C_0 = 0` (a point), `C_1 = λ` (an edge, whose
boundary consists of two vertices at distance `√2`), and `C_j = j² λ √(2 + 2/(j - 1)) C_(j-1)` for
`j ≥ 2` by the main step of Lemma 8.2 (`lipschitz_simplexBoundary_of_faces`), because
`√(2 + 2/(j-1)) √(j - 1) = √2 √j`. Finally `F = F_n`, and `C_j ≤ C_n` for `j ≤ n` since `λ ≥ 1`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open Set Finset

namespace LipschitzExtension

universe u v

/-! ### The skeleton induction -/

section Skeleton

variable {I : Type*} {Y : Type*}

/-- Boundary extension operators with the constant of Lemma 7.2 of [Basso2024]: for every `σ` with
`2 ≤ #σ ≤ n + 1`, `E σ h` agrees with `h` on `∂σ` and is `(#σ - 1)² Λ L`-Lipschitz on `simplex σ`
whenever `h` is `L`-Lipschitz on `∂σ`. -/
def IsBoundaryExtOp [PseudoMetricSpace Y] (n : ℕ) (Λ : ℝ)
    (E : Finset I → ((I →₀ ℝ) → Y) → (I →₀ ℝ) → Y) : Prop :=
  ∀ (σ : Finset I) (h : (I →₀ ℝ) → Y), 2 ≤ σ.card → σ.card ≤ n + 1 →
    (∀ x ∈ simplexBoundary σ, E σ h x = h x) ∧
    ∀ L : ℝ, 0 ≤ L →
      (∀ x ∈ simplexBoundary σ, ∀ y ∈ simplexBoundary σ, dist (h x) (h y) ≤ L * l2dist x y) →
      ∀ x ∈ simplex σ, ∀ y ∈ simplex σ,
        dist (E σ h x) (E σ h y) ≤ ((σ.card : ℝ) - 1) ^ 2 * Λ * L * l2dist x y

/-- Boundary extension operators with the constant of Lemma 7.2 exist under `LC(n - 1, Λ)` with
`Λ ≥ 0` (by `LipschitzConnected.exists_simplex_extension`). -/
theorem exists_isBoundaryExtOp [MetricSpace Y] {n : ℕ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hY : LipschitzConnected (n - 1) Λ Y) :
    ∃ E : Finset I → ((I →₀ ℝ) → Y) → (I →₀ ℝ) → Y, IsBoundaryExtOp n Λ E := by
  have key : ∀ (σ : Finset I) (h : (I →₀ ℝ) → Y), ∃ G : (I →₀ ℝ) → Y,
      2 ≤ σ.card → σ.card ≤ n + 1 →
      (∀ x ∈ simplexBoundary σ, G x = h x) ∧
      ∀ L : ℝ, 0 ≤ L →
        (∀ x ∈ simplexBoundary σ, ∀ y ∈ simplexBoundary σ, dist (h x) (h y) ≤ L * l2dist x y) →
        ∀ x ∈ simplex σ, ∀ y ∈ simplex σ,
          dist (G x) (G y) ≤ ((σ.card : ℝ) - 1) ^ 2 * Λ * L * l2dist x y := by
    intro σ h
    by_cases hc : 2 ≤ σ.card ∧ σ.card ≤ n + 1
    · obtain ⟨hc1, hc2⟩ := hc
      obtain ⟨k, hk⟩ : ∃ k, σ.card = k + 1 := ⟨σ.card - 1, by omega⟩
      obtain ⟨G, hG1, hG2⟩ :=
        LipschitzConnected.exists_simplex_extension hY hΛ (k := k) (by omega) (by omega) hk h
      refine ⟨G, fun _ _ ↦ ⟨hG1, fun L hL hh x hx y hy ↦ ?_⟩⟩
      have e : ((σ.card : ℝ) - 1) ^ 2 = (k : ℝ) ^ 2 := by
        rw [hk]; push_cast; ring
      rw [e]
      exact hG2 L hL hh x hx y hy
    · exact ⟨h, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hc⟩
  choose E hE using key
  exact ⟨E, hE⟩

open Classical in
/-- The skeleton maps `F_k` of the induction: `F_0 (e_i) = g i` (and `F_0 = y₀` off the vertices);
`F_(k+1) x = E_σ F_k x` if the support `σ` of `x` is a face with `k + 2` vertices, and
`F_(k+1) x = F_k x` otherwise. -/
noncomputable def skel (K : Set (Finset I)) (g : I → Y) (y₀ : Y)
    (E : Finset I → ((I →₀ ℝ) → Y) → (I →₀ ℝ) → Y) : ℕ → (I →₀ ℝ) → Y
  | 0, x => if h : ∃ i, x = Finsupp.single i 1 then g h.choose else y₀
  | k + 1, x =>
    if x.support ∈ K ∧ x.support.card = k + 2 then E x.support (skel K g y₀ E k) x
    else skel K g y₀ E k x

variable {K : Set (Finset I)} {g : I → Y} {y₀ : Y}
  {E : Finset I → ((I →₀ ℝ) → Y) → (I →₀ ℝ) → Y}

/-- `F_0 (e_i) = g i`. -/
theorem skel_zero_single (i : I) : skel K g y₀ E 0 (Finsupp.single i 1) = g i := by
  have h : ∃ j, Finsupp.single i (1 : ℝ) = Finsupp.single j 1 := ⟨i, rfl⟩
  rw [skel, dite_eq_left h]
  congr 1
  exact (Finsupp.single_left_injective one_ne_zero h.choose_spec).symm

/-- `F_(k+1) x = F_k x` unless the support of `x` is a face with `k + 2` vertices. -/
theorem skel_succ_of_not {k : ℕ} {x : I →₀ ℝ}
    (h : ¬ (x.support ∈ K ∧ x.support.card = k + 2)) :
    skel K g y₀ E (k + 1) x = skel K g y₀ E k x := by
  rw [skel, ite_eq_right h]

/-- `F_(k+1) x = E_σ F_k x` if the support `σ` of `x` is a face with `k + 2` vertices. -/
theorem skel_succ_of_mem {k : ℕ} {x : I →₀ ℝ} (h1 : x.support ∈ K)
    (h2 : x.support.card = k + 2) :
    skel K g y₀ E (k + 1) x = E x.support (skel K g y₀ E k) x := by
  rw [skel, ite_eq_left ⟨h1, h2⟩]

/-- `F_k (e_i) = g i`. -/
theorem skel_single (k : ℕ) (i : I) : skel K g y₀ E k (Finsupp.single i 1) = g i := by
  induction k with
  | zero => exact skel_zero_single i
  | succ k ih =>
    rw [skel_succ_of_not, ih]
    rw [Finsupp.support_single i one_ne_zero, Finset.card_singleton]
    rintro ⟨-, h⟩
    omega

/-- The later skeleton maps do not change `F_j` at points with at most `j + 1` support points. -/
theorem skel_eq_of_card_le {j k : ℕ} (hjk : j ≤ k) {x : I →₀ ℝ}
    (hx : x.support.card ≤ j + 1) : skel K g y₀ E k x = skel K g y₀ E j x := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hjk ih =>
    rw [skel_succ_of_not, ih]
    rintro ⟨-, h⟩
    omega

/-- A point of `simplex σ` is supported in `σ`. -/
theorem support_subset_of_mem_simplex {σ : Finset I} {x : I →₀ ℝ} (hx : x ∈ simplex σ) :
    x.support ⊆ σ :=
  Finset.coe_subset.mp hx.2.1

/-- A point of a simplex with at most one support point is a vertex. -/
theorem eq_single_of_mem_simplex {σ : Finset I} {x : I →₀ ℝ} (hx : x ∈ simplex σ)
    (h1 : x.support.card ≤ 1) : ∃ a ∈ σ, x = Finsupp.single a 1 := by
  have hsub : x.support ⊆ σ := support_subset_of_mem_simplex hx
  obtain ⟨-, -, hx1⟩ := hx
  have hne : x.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [Finsupp.support_eq_empty] at he
    subst he
    simp at hx1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (le_antisymm h1 hne.card_pos)
  have haσ : a ∈ σ := hsub (by rw [ha]; exact Finset.mem_singleton_self a)
  have hxa : x = Finsupp.single a (x a) := Finsupp.support_subset_singleton.mp ha.le
  have hsum : ∑ i ∈ σ, x i = x a := by
    refine Finset.sum_eq_single a (fun b _ hba ↦ ?_) (fun h ↦ absurd haσ h)
    refine Finsupp.notMem_support_iff.mp ?_
    rw [ha, Finset.mem_singleton]
    exact hba
  refine ⟨a, haσ, ?_⟩
  calc x = Finsupp.single a (x a) := hxa
    _ = Finsupp.single a 1 := by rw [← hsum, hx1]

/-- A boundary point of an edge is a vertex. -/
theorem eq_single_of_mem_simplexBoundary {σ : Finset I} (hσ : σ.card = 2) {x : I →₀ ℝ}
    (hx : x ∈ simplexBoundary σ) : ∃ a ∈ σ, x = Finsupp.single a 1 := by
  classical
  obtain ⟨hx', i, hi, hxi⟩ := hx
  refine eq_single_of_mem_simplex hx' ?_
  have hsub : x.support ⊆ σ.erase i := by
    intro a ha
    refine Finset.mem_erase.mpr ⟨?_, support_subset_of_mem_simplex hx' ha⟩
    rintro rfl
    exact (Finsupp.mem_support_iff.mp ha) hxi
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hi] at this
  omega

/-- On a face with `j + 2` vertices, `F_(j+1)` is the chosen extension of `F_j|_{∂σ}`. -/
private theorem skel_succ_eq_on_simplex [PseudoMetricSpace Y] {n : ℕ} {Λ : ℝ}
    (hE : IsBoundaryExtOp n Λ E) (hK : IsSComplex n K) {j : ℕ} {σ : Finset I} (hσK : σ ∈ K)
    (hσ : σ.card = j + 2) {x : I →₀ ℝ} (hx : x ∈ simplex σ) :
    skel K g y₀ E (j + 1) x = E σ (skel K g y₀ E j) x := by
  have hsub : x.support ⊆ σ := support_subset_of_mem_simplex hx
  by_cases hs : x.support = σ
  · rw [skel_succ_of_mem (by rw [hs]; exact hσK) (by rw [hs]; exact hσ), hs]
  · have hss : x.support ⊂ σ := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hs⟩
    have hlt := Finset.card_lt_card hss
    rw [skel_succ_of_not (fun h ↦ by have := h.2; omega)]
    obtain ⟨i, hiσ, hix⟩ := Finset.exists_of_ssubset hss
    have hb : x ∈ simplexBoundary σ := ⟨hx, i, hiσ, Finsupp.notMem_support_iff.mp hix⟩
    exact ((hE σ _ (by omega) (hK.card_le σ hσK)).1 x hb).symm

/-- The recursion of the constants: `(m + 2)² λ √(2 + 2/(m + 1)) C_(m+1) = C_(m+2)`. -/
private theorem sharpConst_succ (Λ : ℝ) (m : ℕ) :
    (((m + 2 : ℕ) : ℝ) + 1 - 1) ^ 2 * Λ *
        (√(2 + 2 / (((m + 2 : ℕ) : ℝ) - 1)) *
          (Λ ^ (m + 1) * √2 ^ (m + 1 - 1) * √((m + 1 : ℕ) : ℝ) * ((m + 1).factorial : ℝ) ^ 2)) =
      Λ ^ (m + 2) * √2 ^ (m + 2 - 1) * √((m + 2 : ℕ) : ℝ) * ((m + 2).factorial : ℝ) ^ 2 := by
  have e1 : (((m + 2 : ℕ) : ℝ) - 1) = (m : ℝ) + 1 := by push_cast; ring
  have e2 : √(2 + 2 / ((m : ℝ) + 1)) * √((m : ℝ) + 1) = √2 * √((m : ℝ) + 2) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by norm_num)]
    congr 1
    field_simp
    ring
  rw [e1, show m + 1 - 1 = m by omega, show m + 2 - 1 = m + 1 by omega,
    Nat.factorial_succ (m + 1)]
  push_cast
  rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring]
  calc ((m : ℝ) + 2 + 1 - 1) ^ 2 * Λ * (√(2 + 2 / ((m : ℝ) + 1)) *
        (Λ ^ (m + 1) * √2 ^ m * √((m : ℝ) + 1) * ((m + 1).factorial : ℝ) ^ 2))
      = ((m : ℝ) + 2) ^ 2 * Λ * Λ ^ (m + 1) * √2 ^ m * ((m + 1).factorial : ℝ) ^ 2 *
          (√(2 + 2 / ((m : ℝ) + 1)) * √((m : ℝ) + 1)) := by ring
    _ = _ := by rw [e2]; ring

/-- The main estimate of the skeleton induction in the proof of Proposition 8.1 of [Basso2024]: on
a face `σ` with `j + 1` vertices on which `g` is `L`-Lipschitz (i.e. `d(g i, g i') ≤ L √2` for
`i, i' ∈ σ`), `F_j` is `Λ^j (√2)^(j-1) √j (j!)² L`-Lipschitz. -/
theorem skel_lipschitz [PseudoMetricSpace Y] {n : ℕ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hE : IsBoundaryExtOp n Λ E) (hK : IsSComplex n K) (j : ℕ) :
    ∀ σ ∈ K, σ.card = j + 1 → ∀ L : ℝ, 0 ≤ L →
      (∀ i ∈ σ, ∀ i' ∈ σ, dist (g i) (g i') ≤ L * Real.sqrt 2) →
      ∀ x ∈ simplex σ, ∀ y ∈ simplex σ,
        dist (skel K g y₀ E j x) (skel K g y₀ E j y) ≤
          Λ ^ j * √2 ^ (j - 1) * √(j : ℝ) * (j.factorial : ℝ) ^ 2 * L * l2dist x y := by
  induction j with
  | zero =>
    intro σ hσK hσ L hL hg x hx y hy
    have hxc : x.support.card ≤ 1 := by
      have := Finset.card_le_card (support_subset_of_mem_simplex hx); omega
    have hyc : y.support.card ≤ 1 := by
      have := Finset.card_le_card (support_subset_of_mem_simplex hy); omega
    obtain ⟨a, ha, rfl⟩ := eq_single_of_mem_simplex hx hxc
    obtain ⟨b, hb, rfl⟩ := eq_single_of_mem_simplex hy hyc
    have hab : a = b := Finset.card_le_one.mp (by omega) a ha b hb
    subst hab
    rw [dist_self]
    simp
  | succ j ih =>
    intro σ hσK hσ L hL hg x hx y hy
    obtain ⟨-, hE2⟩ := hE σ (skel K g y₀ E j) (by omega) (hK.card_le σ hσK)
    rw [skel_succ_eq_on_simplex hE hK hσK hσ hx, skel_succ_eq_on_simplex hE hK hσK hσ hy]
    cases j with
    | zero =>
      -- an edge: the boundary consists of the two vertices
      have hbd : ∀ x ∈ simplexBoundary σ, ∀ y ∈ simplexBoundary σ,
          dist (skel K g y₀ E 0 x) (skel K g y₀ E 0 y) ≤ L * l2dist x y := by
        intro x hx y hy
        obtain ⟨a, ha, rfl⟩ := eq_single_of_mem_simplexBoundary hσ hx
        obtain ⟨b, hb, rfl⟩ := eq_single_of_mem_simplexBoundary hσ hy
        rw [skel_zero_single, skel_zero_single]
        by_cases hab : a = b
        · subst hab
          rw [dist_self]
          exact mul_nonneg hL (l2dist_nonneg _ _)
        · rw [l2dist_single_single hab]
          exact hg a ha b hb
      have hcard : (σ.card : ℝ) = 2 := by rw [hσ]; norm_num
      calc _ ≤ ((σ.card : ℝ) - 1) ^ 2 * Λ * L * l2dist x y := hE2 L hL hbd x hx y hy
        _ = _ := by rw [hcard]; norm_num
    | succ m =>
      -- `#σ ≥ 3`: glue the facets
      set C : ℝ := Λ ^ (m + 1) * √2 ^ (m + 1 - 1) * √((m + 1 : ℕ) : ℝ) *
        ((m + 1).factorial : ℝ) ^ 2 with hC
      have hC0 : 0 ≤ C := by rw [hC]; positivity
      have hL' : 0 ≤ C * L := mul_nonneg hC0 hL
      have hbd : ∀ x ∈ simplexBoundary σ, ∀ y ∈ simplexBoundary σ,
          dist (skel K g y₀ E (m + 1) x) (skel K g y₀ E (m + 1) y) ≤
            √(2 + 2 / (((m + 2 : ℕ) : ℝ) - 1)) * (C * L) * l2dist x y := by
        refine lipschitz_simplexBoundary_of_faces (k := m + 2) (by omega) hσ hL' ?_
        intro τ hτσ hτc x hx y hy
        have hτK : τ ∈ K := hK.down σ hσK τ hτσ (Finset.card_pos.mp (by omega))
        exact ih τ hτK (by omega) L hL (fun i hi i' hi' ↦ hg i (hτσ hi) i' (hτσ hi')) x hx y hy
      have hs0 : 0 ≤ √(2 + 2 / (((m + 2 : ℕ) : ℝ) - 1)) * (C * L) :=
        mul_nonneg (Real.sqrt_nonneg _) hL'
      have hcard : (σ.card : ℝ) = ((m + 2 : ℕ) : ℝ) + 1 := by rw [hσ]; push_cast; ring
      calc _ ≤ ((σ.card : ℝ) - 1) ^ 2 * Λ *
            (√(2 + 2 / (((m + 2 : ℕ) : ℝ) - 1)) * (C * L)) * l2dist x y :=
            hE2 _ hs0 hbd x hx y hy
        _ = (((m + 2 : ℕ) : ℝ) + 1 - 1) ^ 2 * Λ *
              (√(2 + 2 / (((m + 2 : ℕ) : ℝ) - 1)) * C) * L * l2dist x y := by
            rw [hcard]; ring
        _ = _ := by rw [hC, sharpConst_succ]

end Skeleton

/-- **Proposition 8.1** of [Basso2024]: a nonempty metric space satisfying `LC(n - 1, Λ)` with
`Λ ≥ 1` is an `(n, Λⁿ (√2)ⁿ⁻¹ √n (n!)²)`-simplicial extensor (Definition 6.1 of [Basso2024]). -/
theorem LipschitzConnected.simplicialExtensor {Y : Type v} [MetricSpace Y] [Nonempty Y]
    {n : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ) (hY : LipschitzConnected (n - 1) Λ Y) :
    SimplicialExtensor.{u} n (Λ ^ n * √2 ^ (n - 1) * √(n : ℝ) * (n.factorial : ℝ) ^ 2) Y := by
  intro I K hK g
  obtain ⟨E, hE⟩ := exists_isBoundaryExtOp (I := I) (by linarith) hY
  refine ⟨skel K g (Classical.arbitrary Y) E n, fun i ↦ skel_single n i, ?_⟩
  intro σ hσK L hL hg x hx y hy
  obtain ⟨j, hj⟩ : ∃ j, σ.card = j + 1 :=
    ⟨σ.card - 1, by have := (hK.nonempty σ hσK).card_pos; omega⟩
  have hjn : j ≤ n := by have := hK.card_le σ hσK; omega
  have hxc : x.support.card ≤ j + 1 := by
    have := Finset.card_le_card (support_subset_of_mem_simplex hx); omega
  have hyc : y.support.card ≤ j + 1 := by
    have := Finset.card_le_card (support_subset_of_mem_simplex hy); omega
  rw [skel_eq_of_card_le hjn hxc, skel_eq_of_card_le hjn hyc]
  have hs : 1 ≤ √(2 : ℝ) := by
    rw [Real.one_le_sqrt]
    norm_num
  have hmono : Λ ^ j * √2 ^ (j - 1) * √(j : ℝ) * (j.factorial : ℝ) ^ 2 ≤
      Λ ^ n * √2 ^ (n - 1) * √(n : ℝ) * (n.factorial : ℝ) ^ 2 := by
    gcongr
  calc _ ≤ Λ ^ j * √2 ^ (j - 1) * √(j : ℝ) * (j.factorial : ℝ) ^ 2 * L * l2dist x y :=
        skel_lipschitz (by linarith) hE hK j σ hσK hj L hL hg x hx y hy
    _ ≤ Λ ^ n * √2 ^ (n - 1) * √(n : ℝ) * (n.factorial : ℝ) ^ 2 * L * l2dist x y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hL) (l2dist_nonneg x y)

end LipschitzExtension
