/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Theorems.LeeNaorFinite.Scale
import LipschitzExtension.Theorems.LeeNaorFinite.Cutoff
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log

/-!
# Local construction for the Lee–Naor extension theorem

This file carries out the construction of Section 4 of [Basso2024] for the proof of Theorem 1.5
of [Basso2024], an explicit version of the extension theorem of Lee and Naor for finite sets, with
the corrections of the errata [BassoClaude2026]: by item 1), the constant is `1000` instead of
`600`, and by item 8), `N` is chosen with `N + 1 = max 1 ⌊log₂ (log n)⌋`. The result is
`exists_lipAt_extension_of_finite`: if `A` is nonempty with at most `n ≥ 3` points, then every map
`f` which is `1`-Lipschitz on `A` has an extension `F` whose pointwise Lipschitz constant is at
most `1000 log n / log log n` off `A`, and which satisfies `d(F z, f a) ≤ C d(z, a)` for all
`a ∈ A` and `z ∉ A`. Theorem 1.5 itself, `LipschitzOnWith.extend_finite_normedSpace`, is deduced
from this in `LipschitzExtension.Theorems.LeeNaorFinite` via the reduction theorem
`exists_lipschitz_extension_of_local`, which combines Lemma 2.2 of [Basso2024] with item 5) of the
errata.

Let `A ⊆ Z` be finite with `#A ≤ n`, `n ≥ 3`, and let `f : Z → Y` be `1`-Lipschitz on `A`, where
`Y` is a real normed space. Put `m = N + 1 = max 1 (Nat.log 2 ⌊log n⌋₊)`, which is
`max 1 ⌊log₂ (log n)⌋`. Let `near x` be a nearest point of `A` to `x`, let `F_k` be the maps of
Lemma 4.1 (`exists_scale_map`), and let `ω_k(x) = cutoff N (2^k / (16 d(x, A)))`. Define
`F(x) = (1/(N+1)) ∑_{k ∈ ℤ} ω_k(x) F_k(x)` for `x ∉ A` (the sum is finite: `cutoff_support`) and
`F(a) = f(a)` on `A`.

## Main definitions

* `LeeNaorLocal.leeNaorExt A f N Fk`: the extension `F` above, where `Fk k = F_k`.

## Main statements

* `exists_lipAt_extension_of_finite`: the local construction behind Theorem 1.5 of [Basso2024],
  with the constant `1000` of item 1) of the errata.
* `LeeNaorLocal.dist_leeNaorExt_le`: continuity at `A`, `d(F z, f a) ≤ (16 · 2^(N+1) + 2) d(z, a)`
  for `a ∈ A`.
* `LeeNaorLocal.lipAt_leeNaorExt`: the pointwise Lipschitz bound
  `Lip F(x) ≤ (200 (2 log n + N + 3) + 128 · 2^(N+1)) / (N + 1)` off `A`.
* `LeeNaorLocal.sum_logStar_ballCount_le`: the telescoping bound for the logarithms in
  Lemma 4.1.

## Proof outline

* Continuity at `A`: `‖F(x) - f(near x)‖ ≤ (1/(N+1)) ∑ ω_k(x) 2^k ≤ 16 · 2^(N+1) d(x, A)` and
  `‖f(near x) - f(a)‖ ≤ 2 d(x, a)`.
* Pointwise Lipschitz bound at `x ∉ A`. Let `s = d(x, A)`, let `n₀` be the integer with
  `2^n₀ ≤ 16 s < 2^(n₀+1)`, and let `W = [n₀ - 1, n₀ + N + 2]`. For `x'` close to `x`, both `F(x)`
  and `F(x')` are sums over `W` (`cutoff_support`, `eventually_cutoff_support`) with
  `∑_{k∈W} ω_k = N + 1` (`sum_cutoff_eq`), so with `v = f(near x)`,
  `‖F x - F x'‖ ≤ (1/(N+1)) ∑_{k∈W} [ω_k(x') ‖F_k x - F_k x'‖ + |ω_k x - ω_k x'| ‖F_k x - v‖]`.
  Let `L_k = logStar(#B_A(near x, 2^k) / #B_A(near x, 2^(k-2)))`, where
  `#B_A(a, r) = ballCount A a r`. For each `k ∈ W`: if `s ≤ 2^k/8`, use `Lip F_k(x) ≤ 200 L_k`
  (Lemma 4.1, in the corrected version of the errata, which is needed for `k = n₀`) and
  `ω_k ≤ 1`; otherwise `ω_k(x') = 0` for `x'` near `x` (`eventually_cutoff_eq_zero`); also
  `ω_(n₀+N+2)(x') = 0` near `x`. With `s' = d(x', A)`, the second sum is
  `≤ 128 · 2^(N+1) |s - s'| ≤ 128 · 2^(N+1) d(x, x')` (`eventually_sum_abs_cutoff_sub_le`, using
  `‖F_k x - v‖ ≤ 2^k`). Finally, `∑_{k = n₀-1}^{n₀+N+1} L_k ≤ (N + 3) + 2 log n`
  (`logStar s ≤ 1 + log s` for `s ≥ 1`, telescoping `log #B_A(a, 2^k) - log #B_A(a, 2^(k-2))`
  with `a = near x`, and `1 ≤ #B_A ≤ #A ≤ n`), which gives
  `Lip F(x) ≤ (200 (2 log n + N + 3) + 128 · 2^(N+1)) / (N + 1) ≤ 1000 log n / log log n`
  by an elementary numerical estimate, which uses the choice of `N`.

## Implementation notes

The auxiliary lemmas live in the namespace `LipschitzExtension.LeeNaorLocal`. The sum over
`k ∈ ℤ` in `LeeNaorLocal.leeNaorExt` is a `finsum`; `LeeNaorLocal.leeNaorExt_eq_sum` rewrites it
as a sum over any finite window containing the support. The constant `C` in
`exists_lipAt_extension_of_finite` is `16 · 2^(N+1) + 2`. As in `exists_scale_map`, `Z` is any
metric space in which no closed ball is the whole space (hypothesis `hZ`); the theorem is applied
in `LipschitzOnWith.extend_finite_normedSpace` to the image of `A` under an isometric embedding
into a nontrivial real normed space, which establishes `LocalExtensionProperty`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
* J. R. Lee and A. Naor, *Extending Lipschitz functions via random metric partitions*,
  Invent. Math. 160 (2005), no. 1, 59–95
-/

open Set Metric Filter Topology

namespace LipschitzExtension

/-! ### The final numerical estimate -/

/-- `log t ≤ t / e`, in the form `log t · e ≤ t`. -/
private lemma log_mul_exp_one_le {t : ℝ} (ht : 0 < t) : Real.log t * Real.exp 1 ≤ t := by
  have h := Real.log_le_sub_one_of_pos (show 0 < t / Real.exp 1 by positivity)
  rw [Real.log_div ht.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  have : Real.log t ≤ t / Real.exp 1 := by linarith
  rwa [le_div_iff₀ (Real.exp_pos 1)] at this

/-- The final numerical estimate in the proof of Theorem 1.5 (errata item 1):
`(200 (2 log n + m + 2) + 128 · 2^m) / m ≤ 1000 log n / log log n` for `n ≥ 3` and the choice
`m = N + 1 = max 1 ⌊log₂ (log n)⌋` of errata item 8. -/
private theorem leeNaor_numeric {n : ℕ} (hn : 3 ≤ n) {m : ℕ}
    (hm : m = max 1 (Nat.log 2 ⌊Real.log n⌋₊)) :
    (200 * (2 * Real.log n + m + 2) + 128 * 2 ^ m) / m ≤
      1000 * Real.log n / Real.log (Real.log n) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.log n := ⟨_, rfl⟩
  rw [← ht] at hm ⊢
  have ht1 : 1 < t := by
    rw [ht, Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hL : 0 < Real.log t := Real.log_pos ht1
  have hm1 : 1 ≤ m := by rw [hm]; exact le_max_left _ _
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  rw [div_le_div_iff₀ hm0 hL]
  have hl2 := Real.log_two_lt_d9
  have he := Real.exp_one_gt_d9
  have hLe := log_mul_exp_one_le (show 0 < t by linarith)
  rcases lt_or_ge t 2 with ht2 | ht2
  · -- `1 < t < 2`: then `m = 1` and `log t < log 2`
    have hfloor : ⌊t⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      constructor <;> push_cast <;> linarith
    have hm' : m = 1 := by rw [hm, hfloor, Nat.log_one_right]; rfl
    subst hm'
    have hlt : Real.log t < Real.log 2 := Real.log_lt_log (by linarith) ht2
    push_cast
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 400 * t + 856 by linarith)
      (show (0 : ℝ) ≤ 0.6931471808 - Real.log t by linarith)]
  · -- `t ≥ 2`: then `2^m ≤ t < 2^(m+1)`, so `log t < (m + 1) log 2`; also `e log t ≤ t`
    have hF2 : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by push_cast; linarith)
    have hlog1 : 1 ≤ Nat.log 2 ⌊t⌋₊ := Nat.log_pos (by norm_num) hF2
    have hm' : m = Nat.log 2 ⌊t⌋₊ := by rw [hm]; exact max_eq_right hlog1
    have hF0 : ⌊t⌋₊ ≠ 0 := by omega
    have hpow_le : 2 ^ m ≤ ⌊t⌋₊ := by rw [hm']; exact Nat.pow_log_le_self 2 hF0
    have hlt_pow : ⌊t⌋₊ + 1 ≤ 2 ^ (m + 1) := by
      rw [hm']; exact Nat.lt_pow_succ_log_self (by norm_num) _
    have h2m_le_t : (2 : ℝ) ^ m ≤ t := by
      calc (2 : ℝ) ^ m = ((2 ^ m : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hpow_le
        _ ≤ t := Nat.floor_le (by linarith)
    have ht_lt : t < (2 : ℝ) ^ (m + 1) := by
      calc t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
        _ = ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast hlt_pow
        _ = (2 : ℝ) ^ (m + 1) := by push_cast; ring
    have hlogt_lt : Real.log t < (m + 1) * Real.log 2 := by
      have := Real.log_lt_log (by linarith) ht_lt
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 128 by norm_num)
        (show (0 : ℝ) ≤ t - 2 ^ m by linarith)) hL.le,
      mul_nonneg (show (0 : ℝ) ≤ t by linarith)
        (show (0 : ℝ) ≤ (m + 1) * 0.6931471808 - Real.log t by nlinarith),
      mul_nonneg (show (0 : ℝ) ≤ 200 * m + 400 by positivity)
        (show (0 : ℝ) ≤ t - Real.log t * 2.7182818283 by nlinarith),
      mul_nonneg (show (0 : ℝ) ≤ t by linarith) (show (0 : ℝ) ≤ m - 1 by linarith)]


namespace LeeNaorLocal

variable {Z Y : Type*} [MetricSpace Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-! ### Auxiliary lemmas: finite sums and the telescoping bound -/

/-- Reindexing a sum over an integer interval as a sum over `Finset.range`. -/
lemma sum_Icc_eq_sum_range (g : ℤ → ℝ) (a : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.Icc a (a + n), g k = ∑ j ∈ Finset.range (n + 1), g (a + j) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  have : (a + n + 1 - a).toNat = n + 1 := by omega
  rw [this]
  rfl

/-- Telescoping with step two. -/
lemma sum_range_sub_two (h : ℕ → ℝ) (M : ℕ) :
    ∑ j ∈ Finset.range M, (h (j + 2) - h j) = h (M + 1) + h M - h 1 - h 0 := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, ih]; ring

/-- The window `[n₀ - 1, n₀ + N + 1]` consists of `N + 3` integers. -/
lemma card_Icc_window (n₀ : ℤ) (N : ℕ) :
    ((Finset.Icc (n₀ - 1) (n₀ + N + 1)).card : ℝ) = N + 3 := by
  rw [Int.card_Icc]
  have : (n₀ + N + 1 + 1 - (n₀ - 1)).toNat = N + 3 := by omega
  rw [this]
  push_cast
  ring

/-- The telescoping bound `∑_{k = lo}^{lo + M} L_k ≤ (M + 1) + 2 log n`, where
`L_k = logStar(#B_A(a, 2^k) / #B_A(a, 2^(k-2)))` for a point `a ∈ A` and `#A ≤ n`. -/
lemma sum_logStar_ballCount_le (A : Finset Z) {a : Z} (ha : a ∈ A) {n : ℕ} (hcard : A.card ≤ n)
    (lo : ℤ) (M : ℕ) :
    ∑ k ∈ Finset.Icc lo (lo + M),
        logStar ((ballCount A a (2 ^ k) : ℝ) / (ballCount A a (2 ^ (k - 2)) : ℝ)) ≤
      (M + 1) + 2 * Real.log n := by
  set b : ℤ → ℝ := fun k ↦ (ballCount A a (2 ^ k) : ℝ) with hb_def
  have hb1 : ∀ k, 1 ≤ b k := by
    intro k
    have := ScaleMap.ballCount_pos ha (r := (2 : ℝ) ^ k) (zpow_pos two_pos k).le
    exact Nat.one_le_cast.mpr this
  have hbn : ∀ k, b k ≤ n := by
    intro k
    have : ballCount A a (2 ^ k) ≤ A.card := Finset.card_filter_le _ _
    change (ballCount A a (2 ^ k) : ℝ) ≤ n
    exact_mod_cast this.trans hcard
  have hbmono : ∀ k k', k ≤ k' → b k ≤ b k' := by
    intro k k' hkk'
    have h2 : (2 : ℝ) ^ k ≤ 2 ^ k' := zpow_le_zpow_right₀ (by norm_num) hkk'
    have := ScaleMap.ballCount_le_ballCount A (x := a) (y := a) (r := 2 ^ k) (r' := 2 ^ k')
      (by rw [dist_self]; linarith)
    change (ballCount A a (2 ^ k) : ℝ) ≤ ballCount A a (2 ^ k')
    exact_mod_cast this
  set g : ℤ → ℝ := fun k ↦ Real.log (b k) with hg_def
  have hg0 : ∀ k, 0 ≤ g k := fun k ↦ Real.log_nonneg (hb1 k)
  have hgn : ∀ k, g k ≤ Real.log n := fun k ↦ Real.log_le_log (by linarith [hb1 k]) (hbn k)
  have hterm : ∀ k, logStar (b k / b (k - 2)) ≤ 1 + (g k - g (k - 2)) := by
    intro k
    have hpos : 0 < b (k - 2) := by linarith [hb1 (k - 2)]
    have h1 : 1 ≤ b k / b (k - 2) := (one_le_div hpos).2 (hbmono _ _ (by omega))
    have h2 : Real.log (b k / b (k - 2)) = g k - g (k - 2) :=
      Real.log_div (by linarith [hb1 k]) hpos.ne'
    have h3 : 0 ≤ Real.log (b k / b (k - 2)) := Real.log_nonneg h1
    change max 1 (Real.log (b k / b (k - 2))) ≤ _
    rw [h2] at h3 ⊢
    exact max_le (by linarith) (by linarith)
  set h : ℕ → ℝ := fun j ↦ g (lo - 2 + j) with hh_def
  calc ∑ k ∈ Finset.Icc lo (lo + M), logStar (b k / b (k - 2))
      ≤ ∑ k ∈ Finset.Icc lo (lo + M), (1 + (g k - g (k - 2))) :=
        Finset.sum_le_sum fun k _ ↦ hterm k
    _ = (M + 1) + ∑ j ∈ Finset.range (M + 1), (h (j + 2) - h j) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Int.card_Icc,
          sum_Icc_eq_sum_range (fun k ↦ g k - g (k - 2))]
        have : (lo + M + 1 - lo).toNat = M + 1 := by omega
        rw [this, nsmul_eq_mul, mul_one]
        push_cast
        congr 1
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [hh_def]
        congr 2 <;> push_cast <;> ring
    _ = (M + 1) + (h (M + 2) + h (M + 1) - h 1 - h 0) := by rw [sum_range_sub_two]
    _ ≤ (M + 1) + 2 * Real.log n := by
        linarith [hgn (lo - 2 + ((M + 2 : ℕ) : ℤ)), hgn (lo - 2 + ((M + 1 : ℕ) : ℤ)),
          hg0 (lo - 2 + ((1 : ℕ) : ℤ)), hg0 (lo - 2 + ((0 : ℕ) : ℤ))]

/-- `c • ∑ w_k G_k - v = c • ∑ w_k (G_k - v)` if `c ∑ w_k = 1`. -/
lemma smul_sum_sub_eq {W : Finset ℤ} {w : ℤ → ℝ} {c : ℝ} (hc : c * ∑ k ∈ W, w k = 1)
    (G : ℤ → Y) (v : Y) :
    c • ∑ k ∈ W, w k • G k - v = c • ∑ k ∈ W, w k • (G k - v) := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, smul_smul, hc, one_smul]

/-- The key estimate for the difference of two weighted sums with the same total weight: if
`c ≥ 0` and `w' ≥ 0`, then for every `v`,
`‖c • ∑ w_k G_k - c • ∑ w'_k G'_k‖ ≤ c ∑ (w'_k ‖G_k - G'_k‖ + |w_k - w'_k| ‖G_k - v‖)`. -/
lemma norm_smul_sum_sub_smul_sum_le {W : Finset ℤ} {w w' : ℤ → ℝ} (hw' : ∀ k ∈ W, 0 ≤ w' k)
    (hsum : ∑ k ∈ W, w k = ∑ k ∈ W, w' k) {c : ℝ} (hc : 0 ≤ c) (G G' : ℤ → Y) (v : Y) :
    ‖c • ∑ k ∈ W, w k • G k - c • ∑ k ∈ W, w' k • G' k‖ ≤
      c * ∑ k ∈ W, (w' k * ‖G k - G' k‖ + |w k - w' k| * ‖G k - v‖) := by
  have key : ∑ k ∈ W, w k • G k - ∑ k ∈ W, w' k • G' k =
      ∑ k ∈ W, (w' k • (G k - G' k) + (w k - w' k) • (G k - v)) := by
    have e : ∀ k, w' k • (G k - G' k) + (w k - w' k) • (G k - v) =
        (w k • G k - w' k • G' k) - (w k - w' k) • v := by
      intro k
      simp only [smul_sub, sub_smul]
      abel
    simp only [e, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, sub_self, zero_smul, sub_zero]
  rw [← smul_sub, key, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)) hc
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw' k hk)]

/-! ### The extension `F` and its estimates -/

open Classical in
/-- The extension `F` of Section 4 of [Basso2024]: `F(x) = f(x)` for `x ∈ A`, and
`F(x) = (1/(N+1)) ∑ᶠ k, ω_k(x) F_k(x)` otherwise, where `ω_k(x) = cutoff N (2^k / (16 d(x, A)))`
and `F_k = Fk k`. -/
noncomputable def leeNaorExt (A : Set Z) (f : Z → Y) (N : ℕ) (Fk : ℤ → Z → Y) (x : Z) : Y :=
  if x ∈ A then f x else
    (1 / ((N : ℝ) + 1)) • ∑ᶠ k : ℤ, cutoff N (2 ^ k / (16 * infDist x A)) • Fk k x

/-- The extension `LeeNaorLocal.leeNaorExt` agrees with `f` on `A`. -/
lemma leeNaorExt_of_mem {A : Set Z} {f : Z → Y} {N : ℕ} {Fk : ℤ → Z → Y} {x : Z} (hx : x ∈ A) :
    leeNaorExt A f N Fk x = f x := by
  unfold leeNaorExt
  exact ite_eq_left hx

/-- If `d(x, A) > 0`, the `finsum` defining `LeeNaorLocal.leeNaorExt` at `x` is a sum over any
finite set `W` of integers containing the support of `k ↦ ω_k(x)`. -/
lemma leeNaorExt_eq_sum {A : Set Z} {f : Z → Y} {N : ℕ} {Fk : ℤ → Z → Y} {x : Z}
    (hx : 0 < infDist x A) {W : Finset ℤ}
    (hW : ∀ k : ℤ, cutoff N (2 ^ k / (16 * infDist x A)) ≠ 0 → k ∈ W) :
    leeNaorExt A f N Fk x =
      (1 / ((N : ℝ) + 1)) • ∑ k ∈ W, cutoff N (2 ^ k / (16 * infDist x A)) • Fk k x := by
  have hxA : x ∉ A := fun h ↦ by
    rw [infDist_zero_of_mem h] at hx
    exact lt_irrefl _ hx
  unfold leeNaorExt
  rw [ite_eq_right hxA, finsum_eq_sum_of_support_subset _ (s := W) (fun k hk ↦ ?_)]
  rw [Function.mem_support] at hk
  exact hW k fun h0 ↦ hk (by rw [h0, zero_smul])

/-- Continuity at `A`: if `f` is `1`-Lipschitz on `A` and `‖F_k(x) - f(near x)‖ ≤ 2^k` for all `k`
and `x`, then `d(F z, f a) ≤ (16 · 2^(N+1) + 2) d(z, a)` for all `a ∈ A` and all `z` with
`d(z, A) > 0`. -/
lemma dist_leeNaorExt_le {A : Finset Z} {f : Z → Y} (hf : LipschitzOnWith 1 f (A : Set Z))
    {N : ℕ} {Fk : ℤ → Z → Y} {near : Z → Z}
    (hnear : ∀ x, near x ∈ A ∧ dist x (near x) = infDist x (A : Set Z))
    (hFk : ∀ k x, ‖Fk k x - f (near x)‖ ≤ 2 ^ k) {a : Z} (ha : a ∈ A) {z : Z}
    (hz : 0 < infDist z (A : Set Z)) :
    dist (leeNaorExt (A : Set Z) f N Fk z) (f a) ≤ (16 * 2 ^ (N + 1) + 2) * dist z a := by
  set s := infDist z (A : Set Z) with hs_def
  obtain ⟨n₀, h₁, h₂⟩ := exists_zpow_le_lt hz
  have hW : ∀ k : ℤ, cutoff N (2 ^ k / (16 * s)) ≠ 0 → k ∈ Finset.Icc n₀ (n₀ + N + 1) :=
    fun k hk ↦ Finset.mem_Icc.2 (cutoff_support N hz h₁ h₂ hk)
  have hsum := sum_cutoff_eq N hz _ hW
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hsz : s ≤ dist z a := infDist_le_dist_of_mem (Finset.mem_coe.2 ha)
  -- `‖F z - f (near z)‖ ≤ 16 · 2^(N+1) s`
  have h1 : ‖leeNaorExt (A : Set Z) f N Fk z - f (near z)‖ ≤ 16 * 2 ^ (N + 1) * s := by
    rw [leeNaorExt_eq_sum hz hW, smul_sum_sub_eq (by rw [hsum]; field_simp)]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc 1 / ((N : ℝ) + 1) *
          ‖∑ k ∈ Finset.Icc n₀ (n₀ + N + 1), cutoff N (2 ^ k / (16 * s)) • (Fk k z - f (near z))‖
        ≤ 1 / ((N : ℝ) + 1) *
          ∑ k ∈ Finset.Icc n₀ (n₀ + N + 1),
            cutoff N (2 ^ k / (16 * s)) * (16 * 2 ^ (N + 1) * s) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
          by_cases h0 : cutoff N (2 ^ k / (16 * s)) = 0
          · rw [h0, zero_mul, zero_mul]
          · refine mul_le_mul_of_nonneg_left ((hFk k z).trans ?_) (cutoff_nonneg _ _)
            by_contra hlt
            rw [not_le] at hlt
            apply h0
            apply cutoff_eq_zero_of_ge
            rw [le_div_iff₀ (by positivity)]
            linarith
      _ = 16 * 2 ^ (N + 1) * s := by
          rw [← Finset.sum_mul, hsum]
          field_simp
  -- `‖f (near z) - f a‖ ≤ 2 d(z, a)`
  have h2 : dist (f (near z)) (f a) ≤ 2 * dist z a := by
    have := hf.dist_le_mul (near z) (Finset.mem_coe.2 (hnear z).1) a (Finset.mem_coe.2 ha)
    rw [NNReal.coe_one, one_mul] at this
    have h3 : dist (near z) a ≤ dist (near z) z + dist z a := dist_triangle _ _ _
    rw [dist_comm (near z) z, (hnear z).2] at h3
    linarith
  have h4 : 16 * 2 ^ (N + 1) * s ≤ 16 * 2 ^ (N + 1) * dist z a :=
    mul_le_mul_of_nonneg_left hsz (by positivity)
  calc dist (leeNaorExt (A : Set Z) f N Fk z) (f a)
      ≤ dist (leeNaorExt (A : Set Z) f N Fk z) (f (near z)) + dist (f (near z)) (f a) :=
        dist_triangle _ _ _
    _ ≤ 16 * 2 ^ (N + 1) * s + 2 * dist z a := by
        rw [dist_eq_norm]
        linarith
    _ ≤ (16 * 2 ^ (N + 1) + 2) * dist z a := by linarith

/-- The pointwise Lipschitz bound off `A`: if the maps `F_k` satisfy the conclusions of Lemma 4.1
of [Basso2024] (`exists_scale_map`), `#A ≤ n` and `m = N + 1`, then
`Lip F(x) ≤ (200 (2 log n + m + 2) + 128 · 2^m) / m` at every `x` with `d(x, A) > 0`. -/
lemma lipAt_leeNaorExt {A : Finset Z} {f : Z → Y} {N : ℕ} {Fk : ℤ → Z → Y} {near : Z → Z}
    (hnear : ∀ x, near x ∈ A ∧ dist x (near x) = infDist x (A : Set Z))
    (hFk1 : ∀ k x, ‖Fk k x - f (near x)‖ ≤ 2 ^ k)
    (hFk2 : ∀ k x, infDist x (A : Set Z) ≤ 2 ^ k / 8 →
      LipAt (Fk k) x (200 * logStar ((ballCount A (near x) (2 ^ k) : ℝ) /
        (ballCount A (near x) (2 ^ (k - 2)) : ℝ))))
    {n : ℕ} (hcard : A.card ≤ n) {m : ℕ} (hmN : m = N + 1) {x : Z}
    (hx : 0 < infDist x (A : Set Z)) :
    LipAt (leeNaorExt (A : Set Z) f N Fk) x
      ((200 * (2 * Real.log n + m + 2) + 128 * 2 ^ m) / m) := by
  subst hmN
  set s := infDist x (A : Set Z) with hs_def
  obtain ⟨n₀, h₁, h₂⟩ := exists_zpow_le_lt hx
  set a := near x with ha_def
  set Lk : ℤ → ℝ := fun k ↦ logStar ((ballCount A a (2 ^ k) : ℝ) /
    (ballCount A a (2 ^ (k - 2)) : ℝ)) with hLk_def
  have hLk1 : ∀ k, 1 ≤ Lk k := fun k ↦ one_le_logStar _
  -- the telescoping bound
  have hLsum : ∑ k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 1), Lk k ≤ (N + 3) + 2 * Real.log n := by
    have := sum_logStar_ballCount_le A (hnear x).1 hcard (n₀ - 1) (N + 2)
    have e : n₀ - 1 + ((N + 2 : ℕ) : ℤ) = n₀ + N + 1 := by push_cast; ring
    rw [e] at this
    push_cast at this
    have e2 : ((N : ℝ) + 2 + 1) = N + 3 := by ring
    rw [e2] at this
    exact this
  set L₀ : ℝ := (200 * (2 * Real.log n + ((N + 1 : ℕ) : ℝ) + 2) + 128 * 2 ^ (N + 1)) /
    ((N + 1 : ℕ) : ℝ) with hL₀_def
  intro L' hL'
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  set η := (L' - L₀) / (N + 3) with hη_def
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  have htend : Tendsto (fun y ↦ infDist y (A : Set Z)) (𝓝 x) (𝓝 s) :=
    (continuous_infDist_pt _).tendsto x
  have E1 : ∀ᶠ y in 𝓝 x, 0 < infDist y (A : Set Z) := htend.eventually (eventually_gt_nhds hx)
  have E2 := htend.eventually (eventually_cutoff_support N hx h₁ h₂)
  have E3 := htend.eventually (eventually_sum_abs_cutoff_sub_le N hx h₁ h₂)
  have E4 : ∀ᶠ y in 𝓝 x, ∀ k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 1),
      cutoff N (2 ^ k / (16 * infDist y (A : Set Z))) * ‖Fk k x - Fk k y‖ ≤
        (200 * Lk k + η) * dist x y := by
    rw [Filter.eventually_all_finset]
    intro k _
    by_cases hks : s ≤ 2 ^ k / 8
    · filter_upwards [hFk2 k x hks (200 * Lk k + η) (by linarith)] with y hy
      rw [← dist_eq_norm]
      calc cutoff N (2 ^ k / (16 * infDist y (A : Set Z))) * dist (Fk k x) (Fk k y)
          ≤ 1 * dist (Fk k x) (Fk k y) :=
            mul_le_mul_of_nonneg_right (cutoff_le_one _ _) dist_nonneg
        _ ≤ (200 * Lk k + η) * dist x y := by rw [one_mul]; exact hy
    · have h8 : (2 : ℝ) ^ k < 8 * s := by
        rw [not_le] at hks
        linarith
      filter_upwards [htend.eventually (eventually_cutoff_eq_zero N hx h8)] with y hy
      rw [hy, zero_mul]
      exact mul_nonneg (by linarith [hLk1 k]) dist_nonneg
  filter_upwards [E1, E2, E3, E4] with y hy1 hy2 hy3 hy4
  set s' := infDist y (A : Set Z) with hs'_def
  have hWx : ∀ k : ℤ, cutoff N (2 ^ k / (16 * s)) ≠ 0 → k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 2) :=
    fun k hk ↦ by
      obtain ⟨h1, h2⟩ := cutoff_support N hx h₁ h₂ hk
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hWy : ∀ k : ℤ, cutoff N (2 ^ k / (16 * s')) ≠ 0 → k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 2) :=
    fun k hk ↦ by
      obtain ⟨h1, h2⟩ := hy2 k hk
      exact Finset.mem_Icc.2 ⟨h1, by omega⟩
  have hsx := sum_cutoff_eq N hx _ hWx
  have hsy := sum_cutoff_eq N hy1 _ hWy
  have hFx := leeNaorExt_eq_sum (f := f) (Fk := Fk) hx hWx
  have hFy := leeNaorExt_eq_sum (f := f) (Fk := Fk) hy1 hWy
  have hd : 0 ≤ dist x y := dist_nonneg
  have hss' : |s - s'| ≤ dist x y := by
    rw [abs_sub_le_iff]
    constructor
    · have := infDist_le_infDist_add_dist (x := x) (y := y) (s := (A : Set Z))
      linarith
    · have := infDist_le_infDist_add_dist (x := y) (y := x) (s := (A : Set Z))
      rw [dist_comm] at this
      linarith
  -- the first sum
  have hA1 : ∑ k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 2),
      cutoff N (2 ^ k / (16 * s')) * ‖Fk k x - Fk k y‖ ≤
        (200 * ∑ k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 1), Lk k + (N + 3) * η) * dist x y := by
    have hsub : Finset.Icc (n₀ - 1) (n₀ + N + 1) ⊆ Finset.Icc (n₀ - 1) (n₀ + N + 2) :=
      Finset.Icc_subset_Icc le_rfl (by omega)
    rw [← Finset.sum_subset hsub ?_]
    · calc ∑ k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 1),
            cutoff N (2 ^ k / (16 * s')) * ‖Fk k x - Fk k y‖
          ≤ ∑ k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 1), (200 * Lk k + η) * dist x y :=
            Finset.sum_le_sum hy4
        _ = (200 * ∑ k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 1), Lk k + (N + 3) * η) * dist x y := by
            rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
              nsmul_eq_mul, card_Icc_window]
    · intro k _ hkW'
      have : cutoff N (2 ^ k / (16 * s')) = 0 := by
        by_contra h
        exact hkW' (Finset.mem_Icc.2 (hy2 k h))
      rw [this, zero_mul]
  -- the second sum
  have hA2 : ∑ k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 2),
      |cutoff N (2 ^ k / (16 * s)) - cutoff N (2 ^ k / (16 * s'))| * ‖Fk k x - f a‖ ≤
        128 * 2 ^ (N + 1) * dist x y := by
    calc _ ≤ ∑ k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 2),
          |cutoff N (2 ^ k / (16 * s)) - cutoff N (2 ^ k / (16 * s'))| * (2 : ℝ) ^ k :=
          Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hFk1 k x) (abs_nonneg _)
      _ ≤ 128 * 2 ^ (N + 1) * |s - s'| := hy3
      _ ≤ 128 * 2 ^ (N + 1) * dist x y := mul_le_mul_of_nonneg_left hss' (by positivity)
  -- numerics
  have hL₀eq : L₀ * (N + 1) = 200 * (2 * Real.log n + (N + 1) + 2) + 128 * 2 ^ (N + 1) := by
    rw [hL₀_def]
    push_cast
    field_simp
  have hηeq : (N + 3) * η = L' - L₀ := by
    rw [hη_def]
    field_simp
  have hT : 200 * ∑ k ∈ Finset.Icc (n₀ - 1) (n₀ + N + 1), Lk k + (N + 3) * η +
      128 * 2 ^ (N + 1) ≤ L' * (N + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hL'.le) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  rw [dist_eq_norm, hFx, hFy]
  refine (norm_smul_sum_sub_smul_sum_le (fun k _ ↦ cutoff_nonneg _ _) (hsx.trans hsy.symm)
    (by positivity) (fun k ↦ Fk k x) (fun k ↦ Fk k y) (f a)).trans ?_
  rw [Finset.sum_add_distrib]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hN1]
  nlinarith [hA1, hA2, hT]

end LeeNaorLocal

/-! ### The local construction -/

open LeeNaorLocal in
/-- The local construction behind **Theorem 1.5** of [Basso2024] (Lee–Naor for finite sets, with
the constant `1000` of errata item 1): if `A` is nonempty with at most `n ≥ 3` points and `f` is
`1`-Lipschitz on `A`, then there is `F : Z → Y` with `F = f` on `A` and
`Lip F(z) ≤ 1000 log n / log log n` at every `z` with `d(z, A) > 0`, together with a constant `C`
such that `d(F z, f a) ≤ C d(z, a)` for all `a ∈ A` and all `z` with `d(z, A) > 0`. The
hypothesis `hZ` (no closed ball is the whole space) holds in every nontrivial real normed space
(`compl_closedBall_nonempty`). -/
theorem exists_lipAt_extension_of_finite {Z Y : Type*} [MetricSpace Z] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (hZ : ∀ (z : Z) (ρ : ℝ), (closedBall z ρ)ᶜ.Nonempty) {A : Set Z}
    (hA : A.Finite) (hAne : A.Nonempty) {n : ℕ} (hn : 3 ≤ n) (hcard : A.ncard ≤ n) {f : Z → Y}
    (hf : LipschitzOnWith 1 f A) :
    ∃ F : Z → Y, (∀ a ∈ A, F a = f a) ∧
      (∀ z, 0 < infDist z A → LipAt F z (1000 * Real.log n / Real.log (Real.log n))) ∧
      ∃ C : ℝ, ∀ a ∈ A, ∀ z, 0 < infDist z A → dist (F z) (f a) ≤ C * dist z a := by
  obtain ⟨A', rfl⟩ : ∃ A' : Finset Z, (A' : Set Z) = A := ⟨hA.toFinset, hA.coe_toFinset⟩
  have hA'ne : A'.Nonempty := Finset.coe_nonempty.1 hAne
  have hcard' : A'.card ≤ n := by rwa [Set.ncard_coe_finset] at hcard
  -- nearest points
  obtain ⟨near, hnear⟩ : ∃ near : Z → Z,
      ∀ x, near x ∈ A' ∧ dist x (near x) = infDist x (A' : Set Z) := by
    have : ∀ x, ∃ y, y ∈ A' ∧ dist x y = infDist x (A' : Set Z) := by
      intro x
      obtain ⟨y, hy, hyd⟩ := A'.finite_toSet.isCompact.exists_infDist_eq_dist hAne x
      exact ⟨y, hy, hyd.symm⟩
    choose near hnear using this
    exact ⟨near, hnear⟩
  -- the maps `F_k` of Lemma 4.1
  choose Fk hFk1 hFk2 using fun k ↦ exists_scale_map hZ A' hA'ne hf near hnear k
  -- `m = N + 1 = max 1 ⌊log₂ (log n)⌋` (errata item 8)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = max 1 (Nat.log 2 ⌊Real.log n⌋₊) := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by rw [hm]; exact le_max_left _ _
  obtain ⟨N, hmN⟩ : ∃ N : ℕ, m = N + 1 := ⟨m - 1, by omega⟩
  refine ⟨leeNaorExt (A' : Set Z) f N Fk, fun a ha ↦ leeNaorExt_of_mem ha, fun z hz ↦ ?_,
    16 * 2 ^ (N + 1) + 2, fun a ha z hz ↦ dist_leeNaorExt_le hf hnear hFk1 ha hz⟩
  exact (lipAt_leeNaorExt hnear hFk1 hFk2 hcard' hmN hz).mono (leeNaor_numeric hn hm)

end LipschitzExtension
