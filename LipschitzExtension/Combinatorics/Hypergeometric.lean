/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A moment estimate for the hypergeometric distribution

This file proves the combinatorial core of the proof of Proposition 6.4 of Descombes' thesis.
Consider an urn with `(k + l) n` balls, `k + l` of each of `n` colours, labelled by
`Fin (k + l) × Fin n` (the colour is the second coordinate). Draw `k n` balls without
replacement, i.e. choose a uniformly random subset `I` with `#I = k n`. The number
`Y_j = #{b ∈ I | colour b = j}` of balls of colour `j` is hypergeometric with mean `k` and
variance `k (1 - 1/n) · l n / ((k + l) n - 1) ≤ k`, so by the Cauchy–Schwarz inequality
`E|Y_j - k| ≤ √(Var Y_j) ≤ √k`. Summing over the colours gives
`∑_I ∑_j |Y_j(I) - k| ≤ C((k + l) n, k n) · n · √k`.

## Main statements

* `card_filter_mem_powersetCard`, `card_filter_mem_mem_powersetCard`: the number of `K`-element
  subsets of `S` containing one, respectively two, given elements of `S`.
* `sum_card_inter_powersetCard`, `sum_card_inter_sq_powersetCard`: the first and second moments
  of the hypergeometric distribution.
* `sum_abs_le_sqrt_card_mul_sum_sq`: the Cauchy–Schwarz inequality
  `∑_{i ∈ s} |f i| ≤ √(#s · ∑_{i ∈ s} f i²)`.
* `sum_sq_card_filter_sub_le`: the variance bound `∑_I (Y_j(I) - k)² ≤ C((k + l) n, k n) · k`
  (for `n ≥ 2` colours).
* `sum_abs_card_filter_sub_le`: the estimate `∑_I ∑_j |Y_j(I) - k| ≤ C((k + l) n, k n) · n · √k`,
  used in the proof of Proposition 6.4 of Descombes' thesis
  (`ConicalMidpointMap.dist_baryM_nsmul_le`).

## Proof outline

The first and second moments follow by double counting: for `B ⊆ S` with `#S = N`,
`∑_{I ⊆ S, #I = K} #(I ∩ B) = #B · C(N - 1, K - 1)` and
`∑_I #(I ∩ B)² = #B · C(N - 1, K - 1) + #B (#B - 1) · C(N - 2, K - 2)` (for `K ≥ 2`).

## References

* D. Descombes, *Spaces with convex geodesic bicombings*, PhD thesis, ETH Zürich, 2015
-/

open Finset

namespace LipschitzExtension

section Moments

variable {α : Type*} [DecidableEq α]

/-- The number of `K`-element subsets of `S` containing a given element `x ∈ S` is
`C(#S - 1, K - 1)`. -/
theorem card_filter_mem_powersetCard {S : Finset α} {x : α} (hx : x ∈ S) {K : ℕ}
    (hK : 1 ≤ K) : #{I ∈ S.powersetCard K | x ∈ I} = (#S - 1).choose (K - 1) := by
  have := card_filter_powersetCard_subset {x} S K (singleton_subset_iff.2 hx)
    (by rwa [card_singleton])
  simpa only [singleton_subset_iff, card_singleton] using this

/-- The number of `K`-element subsets of `S` containing two given distinct elements of `S` is
`C(#S - 2, K - 2)`. -/
theorem card_filter_mem_mem_powersetCard {S : Finset α} {x y : α} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x ≠ y) {K : ℕ} (hK : 2 ≤ K) :
    #{I ∈ S.powersetCard K | x ∈ I ∧ y ∈ I} = (#S - 2).choose (K - 2) := by
  have h2 : #({x, y} : Finset α) = 2 := card_pair hxy
  have := card_filter_powersetCard_subset {x, y} S K
    (insert_subset_iff.2 ⟨hx, singleton_subset_iff.2 hy⟩) (by rwa [h2])
  simpa only [insert_subset_iff, singleton_subset_iff, h2] using this

private theorem card_inter_eq_sum_ite (I B : Finset α) :
    #(I ∩ B) = ∑ x ∈ B, if x ∈ I then 1 else 0 := by
  rw [← card_filter, filter_mem_eq_inter, inter_comm]

/-- First moment of the hypergeometric distribution, by double counting:
`∑_{I ⊆ S, #I = K} #(I ∩ B) = #B · C(#S - 1, K - 1)` for `B ⊆ S` and `K ≥ 1`. -/
theorem sum_card_inter_powersetCard {S B : Finset α} (hB : B ⊆ S) {K : ℕ} (hK : 1 ≤ K) :
    ∑ I ∈ S.powersetCard K, #(I ∩ B) = #B * (#S - 1).choose (K - 1) := by
  simp only [card_inter_eq_sum_ite]
  rw [sum_comm]
  refine sum_const_nat fun x hx ↦ ?_
  rw [← card_filter, card_filter_mem_powersetCard (hB hx) hK]

/-- Second moment of the hypergeometric distribution, by double counting:
`∑_{I ⊆ S, #I = K} #(I ∩ B)² = #B · C(#S - 1, K - 1) + #B (#B - 1) · C(#S - 2, K - 2)`
for `B ⊆ S` and `K ≥ 2`. -/
theorem sum_card_inter_sq_powersetCard {S B : Finset α} (hB : B ⊆ S) {K : ℕ} (hK : 2 ≤ K) :
    ∑ I ∈ S.powersetCard K, #(I ∩ B) ^ 2 =
      #B * (#S - 1).choose (K - 1) + #B * (#B - 1) * (#S - 2).choose (K - 2) := by
  have hsq : ∀ I : Finset α,
      #(I ∩ B) ^ 2 = ∑ x ∈ B, ∑ y ∈ B, if x ∈ I ∧ y ∈ I then 1 else 0 := by
    intro I
    rw [sq, card_inter_eq_sum_ite, sum_mul_sum]
    simp only [ite_zero_mul_ite_zero, mul_one]
  simp only [hsq]
  rw [sum_comm]
  have hrow : ∀ x ∈ B, ∑ I ∈ S.powersetCard K, ∑ y ∈ B, (if x ∈ I ∧ y ∈ I then 1 else 0) =
      (#S - 1).choose (K - 1) + (#B - 1) * (#S - 2).choose (K - 2) := by
    intro x hx
    rw [sum_comm, ← add_sum_erase B _ hx, ← card_filter]
    simp only [and_self]
    rw [card_filter_mem_powersetCard (hB hx) (by omega), ← card_erase_of_mem hx]
    congr 1
    refine sum_const_nat fun y hy ↦ ?_
    rw [← card_filter, card_filter_mem_mem_powersetCard (hB hx) (hB (mem_of_mem_erase hy))
      (ne_of_mem_erase hy).symm hK]
  rw [sum_congr rfl hrow, sum_const, smul_eq_mul]
  ring

end Moments

private theorem sum_sub_sq_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) (a : ℝ) :
    ∑ i ∈ s, (f i - a) ^ 2 = ∑ i ∈ s, f i ^ 2 - 2 * a * ∑ i ∈ s, f i + #s * a ^ 2 := by
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_mul,
    ← mul_sum]
  ring

/-- The Cauchy–Schwarz inequality in the form `∑_{i ∈ s} |f i| ≤ √(#s · ∑_{i ∈ s} f i²)`. -/
theorem sum_abs_le_sqrt_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, |f i| ≤ √(#s * ∑ i ∈ s, f i ^ 2) := by
  have h := sum_mul_sq_le_sq_mul_sq s (fun _ ↦ (1 : ℝ)) (fun i ↦ |f i|)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, sq_abs] at h
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

/-- The algebra behind the variance bound: with `N = (k + l) n`, `K = k n`, `c = C(N, K)`,
`C1 = C(N - 1, K - 1)`, `C2 = C(N - 2, K - 2)`, first moment `E` and second moment `E2`, we get
`E2 - 2 k E + c k² ≤ c k`. -/
private theorem variance_algebra {k l n c C1 C2 E E2 : ℝ} (hk : 1 ≤ k) (hl : 0 ≤ l)
    (hn : 2 ≤ n) (hc : 0 ≤ c) (r1 : (k + l) * n * C1 = k * n * c)
    (r2 : ((k + l) * n - 1) * C2 = (k * n - 1) * C1) (hE : E = (k + l) * C1)
    (hE2 : E2 = (k + l) * C1 + (k + l) * (k + l - 1) * C2) :
    E2 - 2 * k * E + c * k ^ 2 ≤ c * k := by
  have r1' : (k + l) * C1 = k * c := by
    have hn0 : n ≠ 0 := by positivity
    apply mul_right_cancel₀ hn0
    linear_combination r1
  have key : ((k + l) * n - 1) * (k ^ 2 * c - (k + l) * (k + l - 1) * C2) =
      k * c * (k * n + l - 1) := by
    linear_combination (-(k + l) * (k + l - 1)) * r2 - ((k + l - 1) * (k * n - 1)) * r1'
  have hpos : 0 < (k + l) * n - 1 := by nlinarith
  have hD : 0 ≤ k ^ 2 * c - (k + l) * (k + l - 1) * C2 := by
    refine nonneg_of_mul_nonneg_right ?_ hpos
    rw [key]
    have : 0 ≤ k * n + l - 1 := by nlinarith
    positivity
  rw [hE2, hE, r1']
  linear_combination hD

/-- The variance bound for the number of balls of colour `j` (for `n ≥ 2` colours):
`∑_{I} (#{b ∈ I | b.2 = j} - k)² ≤ C((k + l) n, k n) · k`. -/
theorem sum_sq_card_filter_sub_le (k l n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) (j : Fin n) :
    ∑ I ∈ (univ : Finset (Fin (k + l) × Fin n)).powersetCard (k * n),
        (((I.filter fun b ↦ b.2 = j).card : ℝ) - k) ^ 2 ≤
      ((((k + l) * n).choose (k * n) : ℕ) : ℝ) * k := by
  set S := (univ : Finset (Fin (k + l) × Fin n)) with hSdef
  set B := S.filter fun b ↦ b.2 = j with hBdef
  have hBS : B ⊆ S := filter_subset _ _
  have hS : #S = (k + l) * n := by simp [S]
  have hB : #B = k + l := by
    rw [hBdef, hSdef, card_filter, Fintype.sum_prod_type]
    simp
  have hI : ∀ I : Finset (Fin (k + l) × Fin n), I.filter (fun b ↦ b.2 = j) = I ∩ B := by
    intro I
    ext b
    simp [B, S]
  simp only [hI]
  have hK1 : 1 ≤ k * n := by nlinarith
  have hK2 : 2 ≤ k * n := by nlinarith
  have hN2 : 2 ≤ (k + l) * n := by nlinarith
  have hE := sum_card_inter_powersetCard hBS hK1
  have hE2 := sum_card_inter_sq_powersetCard hBS hK2
  rw [hS, hB] at hE hE2
  -- the binomial identities `N · C(N - 1, K - 1) = K · C(N, K)` and
  -- `(N - 1) · C(N - 2, K - 2) = (K - 1) · C(N - 1, K - 1)`
  have h1 : (k + l) * n * ((k + l) * n - 1).choose (k * n - 1) =
      k * n * ((k + l) * n).choose (k * n) := by
    have := Nat.add_one_mul_choose_eq ((k + l) * n - 1) (k * n - 1)
    rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at this
    rw [this, mul_comm]
  have h2 : ((k + l) * n - 1) * ((k + l) * n - 2).choose (k * n - 2) =
      (k * n - 1) * ((k + l) * n - 1).choose (k * n - 1) := by
    have := Nat.add_one_mul_choose_eq ((k + l) * n - 2) (k * n - 2)
    rw [show (k + l) * n - 2 + 1 = (k + l) * n - 1 by omega,
      show k * n - 2 + 1 = k * n - 1 by omega] at this
    rw [this, mul_comm]
  rw [sum_sub_sq_eq, card_powersetCard, hS]
  refine variance_algebra (l := l) (n := n) (C1 := (((k + l) * n - 1).choose (k * n - 1) : ℕ))
    (C2 := (((k + l) * n - 2).choose (k * n - 2) : ℕ)) (by exact_mod_cast hk) (Nat.cast_nonneg l)
    (by exact_mod_cast hn) (Nat.cast_nonneg _) (by exact_mod_cast h1) ?_
    (by exact_mod_cast hE) ?_
  · have := congrArg (Nat.cast : ℕ → ℝ) h2
    push_cast [Nat.cast_sub (show 1 ≤ (k + l) * n by omega), Nat.cast_sub hK1] at this
    exact this
  · have := congrArg (Nat.cast : ℕ → ℝ) hE2
    push_cast [Nat.cast_sub (show 1 ≤ k + l by omega)] at this
    exact this

/-- `∑_{I} ∑_{j} |#{b ∈ I | b.2 = j} - k| ≤ C((k + l) n, k n) · n · √k`, where `I` ranges over
the subsets of `Fin (k + l) × Fin n` with `k n` elements. -/
theorem sum_abs_card_filter_sub_le (k l n : ℕ) (hk : 1 ≤ k) :
    ∑ I ∈ (univ : Finset (Fin (k + l) × Fin n)).powersetCard (k * n),
        ∑ j : Fin n, |((I.filter fun b ↦ b.2 = j).card : ℝ) - k| ≤
      ((((k + l) * n).choose (k * n) : ℕ) : ℝ) * n * Real.sqrt k := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- `n ≤ 1`: all balls have the same colour, so `#{b ∈ I | b.2 = j} = #I = k`
    have h0 : ∀ I ∈ (univ : Finset (Fin (k + l) × Fin n)).powersetCard (k * n), ∀ j : Fin n,
        |((I.filter fun b ↦ b.2 = j).card : ℝ) - k| = 0 := by
      intro I hI j
      obtain rfl : n = 1 := by have := j.isLt; omega
      rw [filter_true_of_mem fun b _ ↦ Subsingleton.elim _ _, (mem_powersetCard.1 hI).2]
      simp
    rw [sum_eq_zero fun I hI ↦ sum_eq_zero fun j _ ↦ h0 I hI j]
    positivity
  · rw [sum_comm]
    -- for each colour: Cauchy–Schwarz and the variance bound
    have hc : ∀ j : Fin n,
        ∑ I ∈ (univ : Finset (Fin (k + l) × Fin n)).powersetCard (k * n),
          |((I.filter fun b ↦ b.2 = j).card : ℝ) - k| ≤
        ((((k + l) * n).choose (k * n) : ℕ) : ℝ) * Real.sqrt k := by
      intro j
      refine (sum_abs_le_sqrt_card_mul_sum_sq _ _).trans ?_
      rw [card_powersetCard, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      calc Real.sqrt _ ≤ Real.sqrt ((((k + l) * n).choose (k * n) : ℕ) *
            ((((k + l) * n).choose (k * n) : ℕ) * k)) :=
            Real.sqrt_le_sqrt (by gcongr; exact sum_sq_card_filter_sub_le k l n hk hn j)
        _ = _ := by
          rw [← mul_assoc, Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]
    calc _ ≤ ∑ _j : Fin n, ((((k + l) * n).choose (k * n) : ℕ) : ℝ) * Real.sqrt k :=
          sum_le_sum fun j _ ↦ hc j
      _ = _ := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end LipschitzExtension
