/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

/-!
# Cutoff functions for the Lee–Naor extension theorem

This file proves Lemma 4.2 of [Basso2024], on the cutoff functions of Section 4 of [Basso2024],
in the form needed for the proof of Theorem 1.5 (the Lee–Naor extension theorem for finite sets).
In Section 4, the extension is `F(x) = (1/(N+1)) ∑_{k ∈ ℤ} ω_k(x) F_k(x)` with
`ω_k(x) = ω(2^k / (16 d(x, A)))`, where `ω` is the piecewise linear function with `ω = 1` on
`[1, 2^N]` and `ω = 0` outside `(1/2, 2^(N+1))`; explicitly,
`ω(t) = max 0 (min 1 (min (2t - 1) (2 - t/2^N)))`. We write `k` for the scale index, which is
denoted by `n` in the paper.

We study `ω_k` as a function of `s = d(x, A) > 0`, that is, the family
`k ↦ cutoff N (2^k / (16 s))`. Let `n₀` be the integer with `2^n₀ ≤ 16 s < 2^(n₀+1)`, i.e. the
largest integer with `2^n₀ / 16 ≤ s`. Then:
* the sum over `k` equals `N + 1` (identity (4.3));
* the support in `k` is contained in `[n₀, n₀ + N + 1]`, and for `s'` close to `s` the support of
  `k ↦ cutoff N (2^k / (16 s'))` is contained in `[n₀ - 1, n₀ + N + 1]`;
* the variation estimate, which replaces (4.4): for `s'` close to `s`,
  `∑_k |ω_k(s) - ω_k(s')| 2^k ≤ 128 · 2^(N+1) |s - s'|`.

## Main definitions

* `cutoff N`: the cutoff profile `ω` (for the parameter `N`).

## Main statements

* `sum_cutoff_eq`: identity (4.3) of Lemma 4.2 of [Basso2024].
* `cutoff_support`, `eventually_cutoff_support`: the support of `k ↦ ω_k` (Lemma 4.2 of
  [Basso2024]), at `s` and near `s`.
* `eventually_cutoff_eq_zero`: if `2^k < 8 s`, then `ω(2^k / (16 s')) = 0` for `s'` close to `s`.
* `eventually_sum_abs_cutoff_sub_le`: the variation estimate replacing (4.4).

## Proof outline

For (4.3), put `α = 2^n₀ / (16 s) ∈ (1/2, 1]`. The nonzero terms are the `ω(2^j α)` with
`0 ≤ j ≤ N + 1`; those with `1 ≤ j ≤ N` are equal to `1`, and
`ω(α) + ω(2^(N+1) α) = (2α - 1) + (2 - 2α) = 1`.

For the variation estimate, only `k ∈ {n₀ - 1, n₀}` and `k ∈ {n₀ + N, n₀ + N + 1}` contribute. We
use that `ω` is `2`-Lipschitz everywhere and `2^(-N)`-Lipschitz on `[1, ∞)`, and that
`2^k = 16 c_k` with `c_k = 2^k/16 ≤ s` for `k ≤ n₀` and `c_k ≤ 2^(N+1) s` for `k ≤ n₀ + N + 1`.
The formal proof gets the bound `(40 + 96 · 2^N) (s/s') |s - s'| ≤ 128 · 2^(N+1) |s - s'|` for
`3s/4 < s' < 2^(n₀+1)/16`.

## Implementation notes

All statements are about a real parameter `s > 0` in place of `d(x, A)`. In the proof of
Theorem 1.5, the bounds (4.4) on the pointwise Lipschitz constants of the individual `ω_k` are
only used to estimate `∑_k |ω_k(x) - ω_k(x')| ‖F_k(x) - f(a_x)‖`, where
`‖F_k(x) - f(a_x)‖ ≤ 2^k` by Lemma 4.1. We therefore prove the variation estimate instead. It is
applied with `s' = d(x', A)`, where `|s - s'| ≤ d(x, x')`, and yields the same term
`128 · 2^(N+1) / (N + 1)` in the final bound as in the paper.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open Filter Topology

namespace LipschitzExtension

/-- The cutoff profile `ω` of Section 4 of [Basso2024], which depends on `N`: the piecewise linear
function with `ω(t) = 0` for `t ≤ 1/2`, `ω(t) = 2t - 1` on `[1/2, 1]`, `ω(t) = 1` on `[1, 2^N]`,
`ω(t) = 2 - t/2^N` on `[2^N, 2^(N+1)]` and `ω(t) = 0` for `t ≥ 2^(N+1)`. -/
noncomputable def cutoff (N : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 (min (2 * t - 1) (2 - t / 2 ^ N)))

theorem cutoff_nonneg (N : ℕ) (t : ℝ) : 0 ≤ cutoff N t := le_max_left _ _

theorem cutoff_le_one (N : ℕ) (t : ℝ) : cutoff N t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem cutoff_eq_zero_of_le (N : ℕ) {t : ℝ} (ht : t ≤ 1 / 2) : cutoff N t = 0 := by
  unfold cutoff
  apply max_eq_left
  have : 2 * t - 1 ≤ 0 := by linarith
  exact (min_le_right _ _).trans ((min_le_left _ _).trans this)

theorem cutoff_eq_zero_of_ge (N : ℕ) {t : ℝ} (ht : 2 ^ (N + 1) ≤ t) : cutoff N t = 0 := by
  unfold cutoff
  apply max_eq_left
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have : 2 - t / 2 ^ N ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hpos]
    calc 2 * 2 ^ N = (2 : ℝ) ^ (N + 1) := by ring
      _ ≤ t := ht
  exact (min_le_right _ _).trans ((min_le_right _ _).trans this)

theorem cutoff_eq_one (N : ℕ) {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 2 ^ N) : cutoff N t = 1 := by
  unfold cutoff
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have h3 : 1 ≤ 2 - t / 2 ^ N := by
    have : t / 2 ^ N ≤ 1 := (div_le_one hpos).mpr h2
    linarith
  rw [min_eq_left (le_min (by linarith) h3), max_eq_right zero_le_one]

/-- For `s > 0` there is an integer `n₀` with `2^n₀ ≤ 16 s < 2^(n₀+1)`, namely the largest integer
with `2^n₀ / 16 ≤ s`. For `s = d(x, A)`, this is the integer `n₀` of Lemma 4.2 of [Basso2024]. -/
theorem exists_zpow_le_lt {s : ℝ} (hs : 0 < s) :
    ∃ n₀ : ℤ, (2 : ℝ) ^ n₀ ≤ 16 * s ∧ 16 * s < 2 ^ (n₀ + 1) := by
  obtain ⟨n, hn1, hn2⟩ :=
    exists_mem_Ico_zpow (by positivity : (0 : ℝ) < 16 * s) (by norm_num : (1 : ℝ) < 2)
  exact ⟨n, hn1, hn2⟩

/-! ### Auxiliary lemmas: explicit form and Lipschitz properties of `ω` -/

/-- On `[1, ∞)` the cutoff only depends on the decreasing branch. -/
private lemma cutoff_of_one_le (N : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    cutoff N t = max 0 (min 1 (2 - t / 2 ^ N)) := by
  unfold cutoff
  rw [← min_assoc, min_eq_left (by linarith : (1 : ℝ) ≤ 2 * t - 1)]

/-- `cutoff N` is `2`-Lipschitz. -/
private lemma abs_cutoff_sub_le (N : ℕ) (t t' : ℝ) :
    |cutoff N t - cutoff N t'| ≤ 2 * |t - t'| := by
  unfold cutoff
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have h0 : 0 ≤ 2 * |t - t'| := by positivity
  have h1 : |(2 * t - 1) - (2 * t' - 1)| ≤ 2 * |t - t'| := by
    rw [show (2 * t - 1) - (2 * t' - 1) = 2 * (t - t') by ring, abs_mul, abs_two]
  have h2 : |(2 - t / 2 ^ N) - (2 - t' / 2 ^ N)| ≤ 2 * |t - t'| := by
    rw [show (2 - t / 2 ^ N) - (2 - t' / 2 ^ N) = (t' - t) / 2 ^ N by ring, abs_div,
      abs_of_pos hpos, abs_sub_comm, div_le_iff₀ hpos]
    have : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    nlinarith [abs_nonneg (t - t')]
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp [h0]) ?_)
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp [h0]) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le h1 h2)

/-- `cutoff N` is `2^(-N)`-Lipschitz on `[1, ∞)`. -/
private lemma abs_cutoff_sub_le_of_one_le (N : ℕ) {t t' : ℝ} (ht : 1 ≤ t) (ht' : 1 ≤ t') :
    |cutoff N t - cutoff N t'| ≤ |t - t'| / 2 ^ N := by
  rw [cutoff_of_one_le N ht, cutoff_of_one_le N ht']
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have h0 : 0 ≤ |t - t'| / 2 ^ N := by positivity
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp [h0]) ?_)
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp [h0]) ?_)
  rw [show (2 - t / 2 ^ N) - (2 - t' / 2 ^ N) = (t' - t) / 2 ^ N by ring, abs_div,
    abs_of_pos hpos, abs_sub_comm]

/-- Support estimate for a general window: if `2^L ≤ 16 s < 2^U`, then `ω(2^k/(16 s)) ≠ 0`
implies `L ≤ k ≤ U + N`. -/
private lemma support_aux (N : ℕ) {s : ℝ} (hs : 0 < s) {L U : ℤ} (hL : (2 : ℝ) ^ L ≤ 16 * s)
    (hU : 16 * s < 2 ^ U) {k : ℤ} (hk : cutoff N (2 ^ k / (16 * s)) ≠ 0) :
    L ≤ k ∧ k ≤ U + N := by
  have h16 : (0 : ℝ) < 16 * s := by positivity
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    apply hk
    apply cutoff_eq_zero_of_le
    rw [div_le_iff₀ h16]
    have h1 : (2 : ℝ) ^ k ≤ 2 ^ (L - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (L - 1) = 2 ^ L / 2 := by rw [zpow_sub_one₀ two_ne_zero]; ring
    rw [h2] at h1
    linarith
  · by_contra hlt
    rw [not_le] at hlt
    apply hk
    apply cutoff_eq_zero_of_ge
    rw [le_div_iff₀ h16]
    have h1 : (2 : ℝ) ^ (U + ((N + 1 : ℕ) : ℤ)) ≤ 2 ^ k :=
      zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
    rw [zpow_add₀ two_ne_zero, zpow_natCast] at h1
    have h2 : (2 : ℝ) ^ (N + 1) * (16 * s) ≤ 2 ^ (N + 1) * 2 ^ U :=
      mul_le_mul_of_nonneg_left hU.le (by positivity)
    linarith

/-- The support of `k ↦ ω(2^k/(16 s))` (Lemma 4.2 of [Basso2024]): if `2^n₀ ≤ 16 s < 2^(n₀+1)`,
then `ω(2^k/(16 s)) ≠ 0` implies `n₀ ≤ k ≤ n₀ + N + 1`. -/
theorem cutoff_support (N : ℕ) {s : ℝ} (hs : 0 < s) {n₀ : ℤ} (h₁ : (2 : ℝ) ^ n₀ ≤ 16 * s)
    (h₂ : 16 * s < 2 ^ (n₀ + 1)) {k : ℤ} (hk : cutoff N (2 ^ k / (16 * s)) ≠ 0) :
    n₀ ≤ k ∧ k ≤ n₀ + N + 1 := by
  obtain ⟨hk1, hk2⟩ := support_aux N hs h₁ h₂ hk
  exact ⟨hk1, by omega⟩

/-- If `2^n₀ ≤ 16 s < 2^(n₀+1)`, then for `s'` close to `s` the support of `k ↦ ω(2^k/(16 s'))`
is contained in `[n₀ - 1, n₀ + N + 1]`. -/
theorem eventually_cutoff_support (N : ℕ) {s : ℝ} (hs : 0 < s) {n₀ : ℤ}
    (h₁ : (2 : ℝ) ^ n₀ ≤ 16 * s) (h₂ : 16 * s < 2 ^ (n₀ + 1)) :
    ∀ᶠ s' in 𝓝 s, ∀ k : ℤ, cutoff N (2 ^ k / (16 * s')) ≠ 0 → n₀ - 1 ≤ k ∧ k ≤ n₀ + N + 1 := by
  have e1 : ∀ᶠ s' in 𝓝 s, s / 2 < s' := eventually_gt_nhds (by linarith)
  have e2 : ∀ᶠ s' in 𝓝 s, s' < 2 ^ (n₀ + 1) / 16 :=
    eventually_lt_nhds (by rw [lt_div_iff₀ (by norm_num)]; linarith)
  filter_upwards [e1, e2] with s' hs'1 hs'2 k hk
  have hs' : 0 < s' := by linarith
  have hL : (2 : ℝ) ^ (n₀ - 1) ≤ 16 * s' := by
    rw [zpow_sub_one₀ two_ne_zero]
    linarith
  have hU : 16 * s' < 2 ^ (n₀ + 1) := by
    rw [lt_div_iff₀ (by norm_num)] at hs'2
    linarith
  obtain ⟨hk1, hk2⟩ := support_aux N hs' hL hU hk
  exact ⟨hk1, by omega⟩

/-- If `2^k < 8 s`, then `ω(2^k/(16 s')) = 0` for all `s'` close to `s`. In other words, `ω_k`
vanishes near every point `x` with `d(x, A) > 2^k/8`. -/
theorem eventually_cutoff_eq_zero (N : ℕ) {s : ℝ} (hs : 0 < s) {k : ℤ} (hk : (2 : ℝ) ^ k < 8 * s) :
    ∀ᶠ s' in 𝓝 s, cutoff N (2 ^ k / (16 * s')) = 0 := by
  have e : ∀ᶠ s' in 𝓝 s, (2 : ℝ) ^ k / 8 < s' :=
    eventually_gt_nhds (by rw [div_lt_iff₀ (by norm_num)]; linarith)
  filter_upwards [e, eventually_gt_nhds hs] with s' hs' hs'pos
  apply cutoff_eq_zero_of_le
  rw [div_lt_iff₀ (by norm_num)] at hs'
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- Reindexing a sum over an integer interval as a sum over `Finset.range`. -/
private lemma sum_Icc_eq_sum_range (f : ℤ → ℝ) (a : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.Icc a (a + n), f k = ∑ j ∈ Finset.range (n + 1), f (a + j) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  have : (a + n + 1 - a).toNat = n + 1 := by omega
  rw [this]
  rfl

/-- **Identity (4.3)** of Lemma 4.2 of [Basso2024]: `∑_k ω(2^k/(16 s)) = N + 1`, where the sum is
taken over any finite set of integers containing the support. -/
theorem sum_cutoff_eq (N : ℕ) {s : ℝ} (hs : 0 < s) (W : Finset ℤ)
    (hW : ∀ k : ℤ, cutoff N (2 ^ k / (16 * s)) ≠ 0 → k ∈ W) :
    ∑ k ∈ W, cutoff N (2 ^ k / (16 * s)) = N + 1 := by
  obtain ⟨n₀, h₁, h₂⟩ := exists_zpow_le_lt hs
  -- both `W` and `[n₀, n₀ + N + 1]` contain the support
  have key : ∑ k ∈ W, cutoff N (2 ^ k / (16 * s)) =
      ∑ k ∈ Finset.Icc n₀ (n₀ + ((N + 1 : ℕ) : ℤ)), cutoff N (2 ^ k / (16 * s)) := by
    have hA : ∑ k ∈ W, cutoff N (2 ^ k / (16 * s)) =
        ∑ k ∈ W ∪ Finset.Icc n₀ (n₀ + ((N + 1 : ℕ) : ℤ)), cutoff N (2 ^ k / (16 * s)) := by
      apply Finset.sum_subset Finset.subset_union_left
      intro k _ hkW
      by_contra h
      exact hkW (hW k h)
    have hB : ∑ k ∈ Finset.Icc n₀ (n₀ + ((N + 1 : ℕ) : ℤ)), cutoff N (2 ^ k / (16 * s)) =
        ∑ k ∈ W ∪ Finset.Icc n₀ (n₀ + ((N + 1 : ℕ) : ℤ)), cutoff N (2 ^ k / (16 * s)) := by
      apply Finset.sum_subset Finset.subset_union_right
      intro k _ hkI
      by_contra h
      obtain ⟨hk1, hk2⟩ := cutoff_support N hs h₁ h₂ h
      exact hkI (Finset.mem_Icc.mpr ⟨hk1, by push_cast; omega⟩)
    rw [hA, hB]
  rw [key, sum_Icc_eq_sum_range]
  -- with `α = 2^n₀/(16 s) ∈ (1/2, 1]` the terms are `ω(2^j α)`, `0 ≤ j ≤ N + 1`
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 2 ^ n₀ / (16 * s) := ⟨_, rfl⟩
  have hα1 : 1 / 2 < α := by
    rw [hα, lt_div_iff₀ (by positivity)]
    rw [zpow_add_one₀ two_ne_zero] at h₂
    linarith
  have hα2 : α ≤ 1 := by
    rw [hα, div_le_one (by positivity)]
    exact h₁
  have hterm : ∀ j : ℕ, cutoff N (2 ^ (n₀ + (j : ℤ)) / (16 * s)) = cutoff N (2 ^ j * α) := by
    intro j
    rw [zpow_add₀ two_ne_zero, zpow_natCast, hα]
    congr 1
    ring
  simp only [hterm]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  -- the middle terms `1 ≤ j ≤ N` are equal to `1`
  have hmid : ∀ i ∈ Finset.range N, cutoff N (2 ^ (i + 1) * α) = 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hP1 : (2 : ℝ) ≤ 2 ^ (i + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hP2 : (2 : ℝ) ^ (i + 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
    apply cutoff_eq_one
    · nlinarith
    · nlinarith
  rw [Finset.sum_congr rfl hmid]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, pow_zero, one_mul]
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  -- the first term is `2α - 1`
  have h0 : cutoff N α = 2 * α - 1 := by
    unfold cutoff
    have : 1 ≤ 2 - α / 2 ^ N := by
      have : α / 2 ^ N ≤ 1 := by
        rw [div_le_one hpos]
        exact hα2.trans (one_le_pow₀ (by norm_num))
      linarith
    rw [min_eq_left (show 2 * α - 1 ≤ 2 - α / 2 ^ N by linarith),
      min_eq_right (show 2 * α - 1 ≤ 1 by linarith),
      max_eq_right (show (0 : ℝ) ≤ 2 * α - 1 by linarith)]
  -- the last term is `2 - 2α`
  have hlast : cutoff N (2 ^ (N + 1) * α) = 2 - 2 * α := by
    have hge : (1 : ℝ) ≤ 2 ^ (N + 1) * α := by
      have : (2 : ℝ) ≤ 2 ^ (N + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (N + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    rw [cutoff_of_one_le N hge]
    have : 2 ^ (N + 1) * α / 2 ^ N = 2 * α := by
      rw [pow_succ]; field_simp
    rw [this, min_eq_right (show 2 - 2 * α ≤ 1 by linarith),
      max_eq_right (show (0 : ℝ) ≤ 2 - 2 * α by linarith)]
  rw [h0, hlast]
  ring

/-! ### Auxiliary lemmas for the variation estimate -/

/-- The difference of the arguments `b/(16 s)` and `b/(16 s')`. -/
private lemma abs_div_sub_div {b s s' : ℝ} (hb : 0 ≤ b) (hs : 0 < s) (hs' : 0 < s') :
    |b / (16 * s) - b / (16 * s')| = b / 16 * (|s - s'| / (s * s')) := by
  have hs0 := hs.ne'
  have hs'0 := hs'.ne'
  rw [show b / (16 * s) - b / (16 * s') = b / 16 * ((s' - s) / (s * s')) by field_simp,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ b / 16), abs_div,
    abs_of_pos (by positivity : 0 < s * s'), abs_sub_comm]

/-- One term of the variation sum, estimated with the global Lipschitz constant `2`. -/
private lemma term_le_two (N : ℕ) {s s' b C : ℝ} (hs : 0 < s) (hs' : 0 < s') (hb : 0 ≤ b)
    (hC : b ≤ C * s) :
    |cutoff N (b / (16 * s)) - cutoff N (b / (16 * s'))| * b ≤
      C ^ 2 / 8 * (s * |s - s'| / s') := by
  have h1 := abs_cutoff_sub_le N (b / (16 * s)) (b / (16 * s'))
  rw [abs_div_sub_div hb hs hs'] at h1
  have hD : 0 ≤ |s - s'| / (s * s') := by positivity
  have hb2 : b ^ 2 ≤ (C * s) ^ 2 := pow_le_pow_left₀ hb hC 2
  have hs0 := hs.ne'
  have hs'0 := hs'.ne'
  calc |cutoff N (b / (16 * s)) - cutoff N (b / (16 * s'))| * b
      ≤ 2 * (b / 16 * (|s - s'| / (s * s'))) * b := mul_le_mul_of_nonneg_right h1 hb
    _ = b ^ 2 / 8 * (|s - s'| / (s * s')) := by ring
    _ ≤ (C * s) ^ 2 / 8 * (|s - s'| / (s * s')) := by gcongr
    _ = C ^ 2 / 8 * (s * |s - s'| / s') := by field_simp

/-- One term of the variation sum, estimated with the Lipschitz constant `2^(-N)` on `[1, ∞)`. -/
private lemma term_le_pow (N : ℕ) {s s' b C : ℝ} (hs : 0 < s) (hs' : 0 < s') (hb : 0 ≤ b)
    (hC : b ≤ C * s) (h1 : 1 ≤ b / (16 * s)) (h1' : 1 ≤ b / (16 * s')) :
    |cutoff N (b / (16 * s)) - cutoff N (b / (16 * s'))| * b ≤
      C ^ 2 / (16 * 2 ^ N) * (s * |s - s'| / s') := by
  have h := abs_cutoff_sub_le_of_one_le N h1 h1'
  rw [abs_div_sub_div hb hs hs'] at h
  have hD : 0 ≤ |s - s'| / (s * s') := by positivity
  have hb2 : b ^ 2 ≤ (C * s) ^ 2 := pow_le_pow_left₀ hb hC 2
  have hs0 := hs.ne'
  have hs'0 := hs'.ne'
  calc |cutoff N (b / (16 * s)) - cutoff N (b / (16 * s'))| * b
      ≤ b / 16 * (|s - s'| / (s * s')) / 2 ^ N * b := mul_le_mul_of_nonneg_right h hb
    _ = b ^ 2 / (16 * 2 ^ N) * (|s - s'| / (s * s')) := by ring
    _ ≤ (C * s) ^ 2 / (16 * 2 ^ N) * (|s - s'| / (s * s')) := by gcongr
    _ = C ^ 2 / (16 * 2 ^ N) * (s * |s - s'| / s') := by field_simp

/-- Bookkeeping for the variation sum over the window of length `N + 4`
(the index `j` corresponds to `k = n₀ - 1 + j`). -/
private lemma sum_bound (T : ℕ → ℝ) (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hT0 : T 0 ≤ 8 * R) (hT1 : T 1 ≤ 32 * R) (hmid : ∀ j, 2 ≤ j → j ≤ N → T j = 0)
    (hTN1 : T (N + 1) ≤ 32 * 2 ^ N * R) (hTN2 : T (N + 1 + 1) ≤ 64 * 2 ^ N * R)
    (hTN3 : T (N + 1 + 1 + 1) = 0) :
    ∑ j ∈ Finset.range (N + 3 + 1), T j ≤ (40 + 96 * 2 ^ N) * R := by
  rw [show N + 3 + 1 = N + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid' : ∑ i ∈ Finset.range N, T (i + 1) ≤ 32 * R := by
    rcases N with _ | M
    · simp only [Finset.range_zero, Finset.sum_empty]
      linarith
    · rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun i hi ↦ hmid (i + 1 + 1) (by omega)
        (by rw [Finset.mem_range] at hi; omega))]
      simpa using hT1
  linarith

/-- **Variation estimate** for the cutoff functions, replacing (4.4) in the proof of Theorem 1.5
of [Basso2024]: if `2^n₀ ≤ 16 s < 2^(n₀+1)`, then for `s'` close to `s`,
`∑_k |ω_k(s) - ω_k(s')| 2^k ≤ 128 · 2^(N+1) |s - s'|`, where `ω_k(s) = ω(2^k/(16 s))` and the
sum is taken over the window `[n₀ - 1, n₀ + N + 2]` (which contains the supports for `s`
and `s'`). -/
theorem eventually_sum_abs_cutoff_sub_le (N : ℕ) {s : ℝ} (hs : 0 < s) {n₀ : ℤ}
    (h₁ : (2 : ℝ) ^ n₀ ≤ 16 * s) (h₂ : 16 * s < 2 ^ (n₀ + 1)) :
    ∀ᶠ s' in 𝓝 s, ∑ k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 2),
      |cutoff N (2 ^ k / (16 * s)) - cutoff N (2 ^ k / (16 * s'))| * (2 : ℝ) ^ k ≤
        128 * 2 ^ (N + 1) * |s - s'| := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 ^ n₀ := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have h1a : a ≤ 16 * s := by rw [ha]; exact h₁
  have h2a : 16 * s < 2 * a := by
    rw [zpow_add_one₀ two_ne_zero, ← ha] at h₂
    linarith
  -- we take `3s/4 < s' < 2^(n₀+1)/16`
  have e1 : ∀ᶠ s' in 𝓝 s, 3 * s / 4 < s' := eventually_gt_nhds (by linarith)
  have e2 : ∀ᶠ s' in 𝓝 s, s' < a / 8 := eventually_lt_nhds (by linarith)
  filter_upwards [e1, e2] with s' hs'1 hs'2
  have hs' : 0 < s' := by linarith
  have h2a' : 16 * s' < 2 * a := by linarith
  have h1a' : a ≤ 32 * s' := by linarith
  have hR0 : 0 ≤ s * |s - s'| / s' := by positivity
  have hRle : s * |s - s'| / s' ≤ 4 / 3 * |s - s'| := by
    rw [div_le_iff₀ hs']
    have : 0 ≤ |s - s'| := abs_nonneg _
    nlinarith
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  -- reindex the window as `k = n₀ - 1 + j`, `j < N + 4`; then `2^k = a 2^j / 2`
  have hIcc : n₀ + N + 2 = (n₀ - 1) + ((N + 3 : ℕ) : ℤ) := by push_cast; ring
  rw [hIcc, sum_Icc_eq_sum_range]
  have hpow : ∀ j : ℕ, (2 : ℝ) ^ (n₀ - 1 + (j : ℤ)) = a * 2 ^ j / 2 := by
    intro j
    rw [zpow_add₀ two_ne_zero, zpow_sub_one₀ two_ne_zero, zpow_natCast, ← ha]
    ring
  simp only [hpow]
  refine le_trans (sum_bound (fun j ↦ |cutoff N (a * 2 ^ j / 2 / (16 * s)) -
    cutoff N (a * 2 ^ j / 2 / (16 * s'))| * (a * 2 ^ j / 2)) N (s * |s - s'| / s') hR0
    ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · -- `k = n₀ - 1`
    refine (term_le_two N hs hs' (by positivity) (C := 8) ?_).trans (le_of_eq (by norm_num))
    simp only [pow_zero]
    linarith
  · -- `k = n₀`
    refine (term_le_two N hs hs' (by positivity) (C := 16) ?_).trans (le_of_eq (by norm_num))
    simp only [pow_one]
    linarith
  · -- `n₀ + 1 ≤ k ≤ n₀ + N - 1`: both values are `1`
    intro j hj1 hj2
    have hP1 : (4 : ℝ) ≤ 2 ^ j := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj1
    have hP2 : (2 : ℝ) ^ j ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hj2
    have hb1 : 2 * a ≤ a * 2 ^ j / 2 := by nlinarith
    have hb2 : a * 2 ^ j / 2 ≤ a * 2 ^ N / 2 := by nlinarith
    have hc : cutoff N (a * 2 ^ j / 2 / (16 * s)) = 1 := by
      apply cutoff_eq_one
      · rw [le_div_iff₀ (by positivity)]; linarith
      · rw [div_le_iff₀ (by positivity)]; nlinarith
    have hc' : cutoff N (a * 2 ^ j / 2 / (16 * s')) = 1 := by
      apply cutoff_eq_one
      · rw [le_div_iff₀ (by positivity)]; linarith
      · rw [div_le_iff₀ (by positivity)]; nlinarith
    simp only [hc, hc', sub_self, abs_zero, zero_mul]
  · -- `k = n₀ + N` (for `N = 0` this is `k = n₀`)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      refine (term_le_two 0 hs hs' (by positivity) (C := 16) ?_).trans (le_of_eq (by norm_num))
      simp only [zero_add, pow_one]
      linarith
    · have hN2 : (2 : ℝ) ≤ 2 ^ N := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
      have hb : a * 2 ^ (N + 1) / 2 = a * 2 ^ N := by rw [pow_succ]; ring
      have hb1 : 2 * a ≤ a * 2 ^ (N + 1) / 2 := by rw [hb]; nlinarith
      refine (term_le_pow N hs hs' (by positivity) (C := 16 * 2 ^ N) ?_ ?_ ?_).trans ?_
      · rw [hb]; nlinarith
      · rw [le_div_iff₀ (by positivity)]; linarith
      · rw [le_div_iff₀ (by positivity)]; linarith
      · have : (16 * (2 : ℝ) ^ N) ^ 2 / (16 * 2 ^ N) = 16 * 2 ^ N := by
          field_simp
        rw [this]
        nlinarith
  · -- `k = n₀ + N + 1`
    have hb : a * 2 ^ (N + 1 + 1) / 2 = 2 * a * 2 ^ N := by rw [pow_succ, pow_succ]; ring
    have hb1 : 2 * a ≤ a * 2 ^ (N + 1 + 1) / 2 := by rw [hb]; nlinarith
    refine (term_le_pow N hs hs' (by positivity) (C := 32 * 2 ^ N) ?_ ?_ ?_).trans ?_
    · rw [hb]; nlinarith
    · rw [le_div_iff₀ (by positivity)]; linarith
    · rw [le_div_iff₀ (by positivity)]; linarith
    · have : (32 * (2 : ℝ) ^ N) ^ 2 / (16 * 2 ^ N) = 64 * 2 ^ N := by
        field_simp
        ring
      rw [this]
  · -- `k = n₀ + N + 2`: both values are `0`
    have hb : a * 2 ^ (N + 1 + 1 + 1) / 2 = 4 * a * 2 ^ N := by
      rw [pow_succ, pow_succ, pow_succ]; ring
    have hN1 : (2 : ℝ) ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ]; ring
    have hc : cutoff N (a * 2 ^ (N + 1 + 1 + 1) / 2 / (16 * s)) = 0 := by
      apply cutoff_eq_zero_of_ge
      rw [le_div_iff₀ (by positivity), hb, hN1]
      nlinarith
    have hc' : cutoff N (a * 2 ^ (N + 1 + 1 + 1) / 2 / (16 * s')) = 0 := by
      apply cutoff_eq_zero_of_ge
      rw [le_div_iff₀ (by positivity), hb, hN1]
      nlinarith
    simp only [hc, hc', sub_self, abs_zero, zero_mul]
  · -- final numerics: `(40 + 96 · 2^N) (s/s') |s - s'| ≤ 128 · 2^(N+1) |s - s'|`
    have habs : 0 ≤ |s - s'| := abs_nonneg _
    rw [pow_succ]
    nlinarith

end LipschitzExtension
