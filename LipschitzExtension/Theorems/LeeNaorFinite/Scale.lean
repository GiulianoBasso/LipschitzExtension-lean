/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.PaddedDecomposition
import LipschitzExtension.Topology.MetricSpace.PointwiseLipschitz.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Single-scale maps for the Lee–Naor extension theorem

This file proves Lemma 4.1 of [Basso2024] in the corrected form of item 1) of the errata
[BassoClaude2026]. The maps `F_k` of this lemma are the building blocks of the extension
constructed in Section 4 of [Basso2024] for the proof of Theorem 1.5 (the Lee–Naor extension
theorem for finite sets). We write `k` for the scale index, which is denoted by `n` in the paper.

**Lemma 4.1 (corrected).** Let `A` be a finite nonempty subset of a metric space `Z` in which no
closed ball is the whole space, let `Y` be a real normed space, let `f : Z → Y` be `1`-Lipschitz
on `A`, and for `x ∈ Z` let `a_x` be a nearest point of `A` to `x`. Then for every `k ∈ ℤ` there is
a map `F_k : Z → Y` such that `‖F_k(x) - f(a_x)‖ ≤ 2^k` for all `x`, and
`Lip F_k(x) ≤ 200 · log(#B_A(a_x, 2^k) / #B_A(a_x, 2^(k-2)))`
for all `x` with `d(x, A) ≤ 2^k/8`. Here `log s` stands for `max 1 (log s)` (`logStar`), and
`#B_A(x, r) = ballCount A x r` is the number of points of `A` in the closed ball `B(x, r)`.

Compared with Lemma 4.1 of the paper, the constant is `200` instead of `120`, the logarithm is
replaced by `max 1 log`, and the bound on `Lip F_k(x)` also holds if `2^k/16 < d(x, A) ≤ 2^k/8`.
As noted in item 1) of the errata, the latter is needed at the scale `k = n₀` in the proof of
Theorem 1.5.

## Main definitions

* `ScaleMap.psiI B i`, `ScaleMap.psi B`, `ScaleMap.phiI B i`: the functions
  `ψ_i = d(·, Z \ B_i)`, `ψ = ∑_i ψ_i` and `φ_i = ψ_i / ψ`, a partition of unity where `ψ > 0`.
* `ScaleMap.scaleMap A f near B ctr r`: the map `F_k`, equal to `∑_i φ_i(y) f(a_i)` where
  `d(y, A) ≤ r` and to `f(a_y)` elsewhere.

## Main statements

* `exists_scale_map`: Lemma 4.1 of [Basso2024], corrected version of item 1) of the errata.
* `ScaleMap.sum_abs_phiI_sub_le`: if `(B_i)` is the union of `K` families of pairwise disjoint
  sets and `ψ(y), ψ(y') > 0`, then `∑_i |φ_i(y) - φ_i(y')| ≤ 4K d(y, y') / ψ(y)` (as in the
  proof of Lemma 3.2 of [Basso2024], with exponent `m = 1`).
* `ScaleMap.mul_ncard_le_psi`: `ψ(y) ≥ t · #{i | B(y, t) ⊆ B_i}`.

## Proof outline

This is the proof of item 1) of the errata. Take the family `(B_i)` of the replacement of
Lemma 2.3 (`exists_padded_family`) with `D = (5/3) 2^k`: it is the union of `K` families of
pairwise disjoint sets, and `B_i ⊆ B(a_i, D/2)` for centers `a_i ∈ A`. Put
`ψ_i(x) = d(x, Z \ B_i)` (this is where the hypothesis on `Z` is used:
`Z \ B_i ⊇ Z \ B(a_i, D/2) ≠ ∅`), `ψ = ∑ ψ_i`, `φ_i = ψ_i / ψ`, and
`F_k(x) = ∑ φ_i(x) f(a_i)` if `d(x, A) ≤ 2^k/6`, `F_k(x) = f(a_x)` otherwise.
* `ψ > 0` where `d(x, A) ≤ 2^k/6` (apply the lemma with the small `t = D/(32 logStar #A)`).
* If `φ_i(x) ≠ 0` then `x ∈ B_i`, so `d(a_i, a_x) ≤ (5/6) 2^k + d(x, A)`; this gives
  `‖F_k(x) - f(a_x)‖ ≤ 2^k` when `d(x, A) ≤ 2^k/6`. For `x'` near `x`, all `i` with `φ_i(x) ≠ 0` or
  `φ_i(x') ≠ 0` satisfy `d(a_i, a_x) ≤ (5/6) 2^k + d(x, A) + d(x, x')`.
* Each point lies in at most one member of each of the `K` partitions, hence
  `∑ |ψ_i(x) - ψ_i(x')| ≤ 2K d(x, x')` and `∑ |φ_i(x) - φ_i(x')| ≤ 4K d(x, x') / ψ(x)`.
* For `d(x, A) ≤ 2^k/8` let `L = logStar(#B_A(a_x, 2^k) / #B_A(a_x, 2^(k-2)))` and
  `t = 2^k/(24 L)`. Then `B_A(x, D/2 + t) ⊆ B_A(a_x, 2^k)`, `B_A(x, D/4 - t) ⊇ B_A(a_x, 2^(k-2))`,
  `d(x, A) + t ≤ D/4` and `32 t L < D`, so `B(x, t) ⊆ B_i` for at least `K/2` indices, each
  contributing `≥ t` to `ψ(x)`. Hence `ψ(x) ≥ Kt/2` and `4K/ψ(x) ≤ 8/t = 192 · 2^(-k) L`; this
  replaces (4.9).
* `F_k(x) - F_k(x') = ∑ (φ_i(x) - φ_i(x')) (f(a_i) - f(a_x))`, so
  `Lip F_k(x) ≤ (23/24) · 192 · L < 200 L`.

## Implementation notes

In the paper, the domain `X` is a Banach space and `F_k` is only defined on
`X_k = {x | d(x, A) ≤ 2^k}`. Here `Z` is any metric space in which no closed ball is the whole
space (hypothesis `hZ`, which holds in every nontrivial real normed space by
`compl_closedBall_nonempty`), and `F_k` is defined on all of `Z`, with `F_k(x) = f(a_x)` where
`d(x, A) > 2^k/6`. As observed in the errata, this does not affect the extension of Section 4,
since `ω_k` vanishes where `d(x, A) ≥ 2^k/8`.

The auxiliary objects live in the namespace `LipschitzExtension.ScaleMap`:
`ScaleMap.psiI B i y = d(y, Z \ B i)`, `ScaleMap.psi B = ∑ i, ScaleMap.psiI B i`,
`ScaleMap.phiI B i = ScaleMap.psiI B i / ScaleMap.psi B`, and `ScaleMap.scaleMap A f near B ctr r`
is `∑ i, ScaleMap.phiI B i y • f (ctr i)` where `d(y, A) ≤ r` and `f (near y)` elsewhere. Here
`near : Z → Z` chooses the nearest points `a_x = near x`, the family `B` and the centers `ctr` come
from `exists_padded_family`, and `exists_scale_map` uses `r = 2^k / 6`. For the Lipschitz
estimate we only use `x'` with `d(x, x') < 2^k / 24`; for these
`‖F_k(x) - F_k(x')‖ ≤ 192 L d(x, x')`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
-/

open Set Metric Filter Topology

namespace LipschitzExtension

variable {Z Y : Type*} [MetricSpace Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

namespace ScaleMap

/-! ### Elementary auxiliary lemmas -/

/-- The elementary estimate `∑ |a i / σ - b i / σ'| ≤ (2 / σ) ∑ |a i - b i|` for
`σ = ∑ a i > 0`, `σ' = ∑ b i > 0` and `b ≥ 0` (as in the proof of Lemma 3.2 of [Basso2024]). -/
theorem sum_abs_div_sub_div_le {ι : Type*} {T : Finset ι} {a b : ι → ℝ}
    (hb : ∀ i ∈ T, 0 ≤ b i) (ha' : 0 < ∑ i ∈ T, a i) (hb' : 0 < ∑ i ∈ T, b i) :
    ∑ i ∈ T, |a i / (∑ k ∈ T, a k) - b i / (∑ k ∈ T, b k)| ≤
      2 / (∑ k ∈ T, a k) * ∑ i ∈ T, |a i - b i| := by
  set σ := ∑ k ∈ T, a k with hσ
  set σ' := ∑ k ∈ T, b k with hσ'
  set D := ∑ i ∈ T, |a i - b i| with hD
  have hdiff : |σ' - σ| ≤ D := by
    rw [hσ, hσ', ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ ↦ abs_sub_comm _ _
  have hterm : ∀ i ∈ T,
      |a i / σ - b i / σ'| ≤ |a i - b i| / σ + b i * (|σ' - σ| / (σ * σ')) := by
    intro i hi
    have e : a i / σ - b i / σ' = (a i - b i) / σ + b i * ((σ' - σ) / (σ * σ')) := by
      field_simp
      ring
    rw [e]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos ha', abs_mul, abs_of_nonneg (hb i hi), abs_div,
      abs_of_pos (mul_pos ha' hb')]
  calc ∑ i ∈ T, |a i / σ - b i / σ'|
      ≤ ∑ i ∈ T, (|a i - b i| / σ + b i * (|σ' - σ| / (σ * σ'))) := Finset.sum_le_sum hterm
    _ = D / σ + σ' * (|σ' - σ| / (σ * σ')) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    _ = D / σ + |σ' - σ| / σ := by
      field_simp
    _ ≤ D / σ + D / σ := by gcongr
    _ = 2 / σ * D := by ring

/-- A point lies in at most `#P` members of a family that is the union of `#P` families of
pairwise disjoint sets. -/
theorem card_filter_mem_le {X ι P : Type*} [Fintype ι] [Fintype P] (part : ι → P)
    (B : ι → Set X) (hdisj : ∀ i j, part i = part j → i ≠ j → Disjoint (B i) (B j)) (x : X)
    [DecidablePred fun i ↦ x ∈ B i] :
    (Finset.univ.filter fun i ↦ x ∈ B i).card ≤ Fintype.card P := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn part (fun _ _ ↦ Finset.mem_univ _) ?_
  intro i hi j hj hij
  by_contra hne
  exact Set.disjoint_left.1 (hdisj i j hij hne) (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
    (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).2

open Classical in
/-- If every `g i` is `1`-Lipschitz and vanishes outside `B i`, where `(B i)` is the union of
`#P` families of pairwise disjoint sets, then `∑ i |g i x - g i x'| ≤ 2 #P d(x, x')`. -/
theorem sum_abs_sub_le {X ι P : Type*} [PseudoMetricSpace X] [Fintype ι] [Fintype P]
    (part : ι → P) (B : ι → Set X)
    (hdisj : ∀ i j, part i = part j → i ≠ j → Disjoint (B i) (B j))
    (g : ι → X → ℝ) (hgB : ∀ i y, g i y ≠ 0 → y ∈ B i)
    (hgLip : ∀ i y y', |g i y - g i y'| ≤ dist y y') (x x' : X) :
    ∑ i, |g i x - g i x'| ≤ 2 * Fintype.card P * dist x x' := by
  set S := Finset.univ.filter fun i ↦ x ∈ B i with hS
  set S' := Finset.univ.filter fun i ↦ x' ∈ B i with hS'
  have h1 : ∑ i ∈ S ∪ S', |g i x - g i x'| = ∑ i, |g i x - g i x'| := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hx : g i x = 0 := by
      by_contra h
      exact hi (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hgB i x h⟩))
    have hx' : g i x' = 0 := by
      by_contra h
      exact hi (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hgB i x' h⟩))
    simp [hx, hx']
  have hcS : S.card ≤ Fintype.card P := card_filter_mem_le part B hdisj x
  have hcS' : S'.card ≤ Fintype.card P := card_filter_mem_le part B hdisj x'
  have hc : ((S ∪ S').card : ℝ) ≤ 2 * Fintype.card P := by
    have := Finset.card_union_le S S'
    exact_mod_cast (by omega : (S ∪ S').card ≤ 2 * Fintype.card P)
  rw [← h1]
  calc ∑ i ∈ S ∪ S', |g i x - g i x'| ≤ ∑ i ∈ S ∪ S', dist x x' :=
        Finset.sum_le_sum fun i _ ↦ hgLip i x x'
    _ = (S ∪ S').card * dist x x' := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * Fintype.card P * dist x x' := mul_le_mul_of_nonneg_right hc dist_nonneg

/-- `logStar` is monotone on `[0, ∞)` (note `logStar 0 = 1`). -/
theorem logStar_le_logStar {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) : logStar s ≤ logStar u := by
  rcases hs.eq_or_lt with h | h
  · rw [← h, show logStar 0 = 1 by simp [logStar]]
    exact one_le_logStar u
  · exact logStar_mono h hsu

/-- If `d(x, y) + r ≤ r'`, then `B(y, r) ⊆ B(x, r')`, so `ballCount A y r ≤ ballCount A x r'`. -/
theorem ballCount_le_ballCount (A : Finset Z) {x y : Z} {r r' : ℝ} (h : dist x y + r ≤ r') :
    ballCount A y r ≤ ballCount A x r' := by
  unfold ballCount
  apply Finset.card_le_card
  intro b hb
  rw [Finset.mem_filter] at hb ⊢
  exact ⟨hb.1, (dist_triangle x y b).trans (by linarith [hb.2])⟩

/-- A closed ball of radius `r ≥ 0` centered at a point of `A` contains a point of `A`. -/
theorem ballCount_pos {A : Finset Z} {a : Z} (ha : a ∈ A) {r : ℝ} (hr : 0 ≤ r) :
    0 < ballCount A a r := by
  unfold ballCount
  exact Finset.card_pos.2 ⟨a, Finset.mem_filter.2 ⟨ha, by rw [dist_self]; exact hr⟩⟩

/-- The quotient of two ball counts is at most `#A` (with the convention `a / 0 = 0`). -/
theorem div_ballCount_le_card (A : Finset Z) (x : Z) (r₁ r₂ : ℝ) :
    (ballCount A x r₁ : ℝ) / (ballCount A x r₂ : ℝ) ≤ A.card := by
  have h1 : (ballCount A x r₁ : ℝ) ≤ A.card := by
    exact_mod_cast Finset.card_filter_le _ _
  rcases Nat.eq_zero_or_pos (ballCount A x r₂) with h | h
  · rw [h, Nat.cast_zero, div_zero]
    exact Nat.cast_nonneg _
  · have : (1 : ℝ) ≤ ballCount A x r₂ := by exact_mod_cast h
    exact (div_le_self (Nat.cast_nonneg _) this).trans h1

/-! ### The partition of unity `φ i = ψ i / ψ` -/

variable {ι : Type*}

/-- The function `ψ_i(y) = d(y, Z \ B_i)`, the distance from `y` to the complement of `B i`. -/
noncomputable def psiI (B : ι → Set Z) (i : ι) (y : Z) : ℝ := infDist y (B i)ᶜ

theorem psiI_nonneg (B : ι → Set Z) (i : ι) (y : Z) : 0 ≤ psiI B i y := infDist_nonneg

theorem mem_of_psiI_ne_zero {B : ι → Set Z} {i : ι} {y : Z} (h : psiI B i y ≠ 0) : y ∈ B i := by
  by_contra hy
  exact h (infDist_zero_of_mem hy)

theorem abs_psiI_sub_le (B : ι → Set Z) (i : ι) (y y' : Z) :
    |psiI B i y - psiI B i y'| ≤ dist y y' := by
  rw [abs_sub_le_iff]
  constructor
  · have := infDist_le_infDist_add_dist (x := y) (y := y') (s := (B i)ᶜ)
    unfold psiI
    linarith
  · have := infDist_le_infDist_add_dist (x := y') (y := y) (s := (B i)ᶜ)
    rw [dist_comm] at this
    unfold psiI
    linarith

theorem le_psiI {B : ι → Set Z} {i : ι} (hne : (B i)ᶜ.Nonempty) {y : Z} {t : ℝ}
    (h : closedBall y t ⊆ B i) : t ≤ psiI B i y := by
  rw [psiI, le_infDist hne]
  intro z hz
  by_contra hlt
  exact hz (h (mem_closedBall'.2 (not_le.1 hlt).le))

variable [Fintype ι]

/-- The sum `ψ(y) = ∑ i, ψ_i(y)`. -/
noncomputable def psi (B : ι → Set Z) (y : Z) : ℝ := ∑ i, psiI B i y

/-- The function `φ_i(y) = ψ_i(y) / ψ(y)`. The `φ_i` form a partition of unity on the set where
`ψ > 0` (`ScaleMap.sum_phiI`). -/
noncomputable def phiI (B : ι → Set Z) (i : ι) (y : Z) : ℝ := psiI B i y / psi B y

theorem psi_nonneg (B : ι → Set Z) (y : Z) : 0 ≤ psi B y :=
  Finset.sum_nonneg fun i _ ↦ psiI_nonneg B i y

theorem phiI_nonneg (B : ι → Set Z) (i : ι) (y : Z) : 0 ≤ phiI B i y :=
  div_nonneg (psiI_nonneg B i y) (psi_nonneg B y)

theorem mem_of_phiI_ne_zero {B : ι → Set Z} {i : ι} {y : Z} (h : phiI B i y ≠ 0) : y ∈ B i :=
  mem_of_psiI_ne_zero fun h0 ↦ h (by simp [phiI, h0])

theorem sum_phiI {B : ι → Set Z} {y : Z} (h : 0 < psi B y) : ∑ i, phiI B i y = 1 := by
  simp only [phiI]
  rw [← Finset.sum_div]
  exact div_self h.ne'

/-- If the complements of all `B i` are nonempty and the closed ball `B(y, t)` is contained in
`B i` for `N` indices `i`, then `ψ(y) ≥ N t`. -/
theorem mul_ncard_le_psi {B : ι → Set Z} (hne : ∀ i, (B i)ᶜ.Nonempty) (y : Z) (t : ℝ) :
    t * ({i | closedBall y t ⊆ B i}.ncard : ℝ) ≤ psi B y := by
  classical
  have hset : {i | closedBall y t ⊆ B i} =
      ↑(Finset.univ.filter fun i ↦ closedBall y t ⊆ B i) := by
    ext i
    simp
  rw [hset, Set.ncard_coe_finset]
  calc t * ((Finset.univ.filter fun i ↦ closedBall y t ⊆ B i).card : ℝ)
      = ∑ i ∈ Finset.univ.filter (fun i ↦ closedBall y t ⊆ B i), t := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ closedBall y t ⊆ B i), psiI B i y :=
        Finset.sum_le_sum fun i hi ↦ le_psiI (hne i) (Finset.mem_filter.1 hi).2
    _ ≤ ∑ i, psiI B i y := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ ↦ psiI_nonneg B i y)
    _ = psi B y := rfl

/-- The Lipschitz estimate for the partition of unity: if `(B i)` is the union of `#P` families of
pairwise disjoint sets and `ψ(y), ψ(y') > 0`, then
`∑ i |φ_i(y) - φ_i(y')| ≤ (2 / ψ(y)) · 2 #P d(y, y')`. -/
theorem sum_abs_phiI_sub_le {P : Type*} [Fintype P] (part : ι → P) {B : ι → Set Z}
    (hdisj : ∀ i j, part i = part j → i ≠ j → Disjoint (B i) (B j)) {y y' : Z}
    (hy : 0 < psi B y) (hy' : 0 < psi B y') :
    ∑ i, |phiI B i y - phiI B i y'| ≤ 2 / psi B y * (2 * Fintype.card P * dist y y') := by
  have h := sum_abs_div_sub_div_le (T := Finset.univ) (a := fun i ↦ psiI B i y)
    (b := fun i ↦ psiI B i y') (fun i _ ↦ psiI_nonneg B i y') hy hy'
  have h2 := sum_abs_sub_le part B hdisj (fun i w ↦ psiI B i w)
    (fun i w hw ↦ mem_of_psiI_ne_zero hw) (abs_psiI_sub_le B) y y'
  calc ∑ i, |phiI B i y - phiI B i y'| ≤ 2 / psi B y * ∑ i, |psiI B i y - psiI B i y'| := h
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (div_nonneg zero_le_two hy.le)

/-! ### The single-scale maps `F_k` -/

/-- The map `F_k` of Lemma 4.1 of [Basso2024] (corrected version of errata item 1): its value at
`y` is `∑ i, φ_i(y) f(ctr i)` if `d(y, A) ≤ r`, and `f (near y)` otherwise. -/
noncomputable def scaleMap (A : Finset Z) (f : Z → Y) (near : Z → Z) (B : ι → Set Z)
    (ctr : ι → Z) (r : ℝ) (y : Z) : Y :=
  if infDist y (A : Set Z) ≤ r then ∑ i, phiI B i y • f (ctr i) else f (near y)

theorem scaleMap_of_le {A : Finset Z} {f : Z → Y} {near : Z → Z} {B : ι → Set Z} {ctr : ι → Z}
    {r : ℝ} {y : Z} (h : infDist y (A : Set Z) ≤ r) :
    scaleMap A f near B ctr r y = ∑ i, phiI B i y • f (ctr i) := ite_eq_left h

theorem scaleMap_of_not_le {A : Finset Z} {f : Z → Y} {near : Z → Z} {B : ι → Set Z}
    {ctr : ι → Z} {r : ℝ} {y : Z} (h : ¬ infDist y (A : Set Z) ≤ r) :
    scaleMap A f near B ctr r y = f (near y) := ite_eq_right h

/-- If `d(y, A) ≤ r` and `ψ(y) > 0`, then `F_k(y) - v = ∑ i, φ_i(y) (f(ctr i) - v)` for every
`v`. -/
theorem scaleMap_sub {A : Finset Z} {f : Z → Y} {near : Z → Z} {B : ι → Set Z} {ctr : ι → Z}
    {r : ℝ} {y : Z} (h : infDist y (A : Set Z) ≤ r) (hpos : 0 < psi B y) (v : Y) :
    scaleMap A f near B ctr r y - v = ∑ i, phiI B i y • (f (ctr i) - v) := by
  rw [scaleMap_of_le h]
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sum_phiI hpos, one_smul]

end ScaleMap

open ScaleMap in
/-- **Lemma 4.1** of [Basso2024], corrected version of errata item 1: for every `k ∈ ℤ` there is
`F : Z → Y` with `‖F x - f (near x)‖ ≤ 2^k` for all `x`, and
`Lip F(x) ≤ 200 logStar(ballCount A (near x) (2^k) / ballCount A (near x) (2^(k-2)))` for all `x`
with `d(x, A) ≤ 2^k/8`. Here `near x` is a nearest point of `A` to `x`, and the hypothesis `hZ`
(no closed ball is the whole space) holds in every nontrivial real normed space. -/
theorem exists_scale_map (hZ : ∀ (z : Z) (ρ : ℝ), (closedBall z ρ)ᶜ.Nonempty)
    (A : Finset Z) (hA : A.Nonempty) {f : Z → Y} (hf : LipschitzOnWith 1 f (A : Set Z))
    (near : Z → Z) (hnear : ∀ x, near x ∈ A ∧ dist x (near x) = infDist x (A : Set Z)) (k : ℤ) :
    ∃ F : Z → Y, (∀ x, ‖F x - f (near x)‖ ≤ 2 ^ k) ∧
      ∀ x, infDist x (A : Set Z) ≤ 2 ^ k / 8 →
        LipAt F x (200 * logStar ((ballCount A (near x) (2 ^ k) : ℝ) /
          (ballCount A (near x) (2 ^ (k - 2)) : ℝ))) := by
  classical
  -- the scale `s = 2 ^ k` and the parameter `D = (5/3) s` of Lemma 2.3
  have hs : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  have hk2 : (2 : ℝ) ^ (k - 2) = 2 ^ k / 4 := by
    rw [zpow_sub₀ two_ne_zero]
    norm_num
  rw [hk2]
  generalize (2 : ℝ) ^ k = s at hs ⊢
  set D : ℝ := 5 / 3 * s with hD_def
  have hD : 0 < D := by rw [hD_def]; positivity
  obtain ⟨ι, P, _, _, part, B, ctr, hKpos, hctrA, hBsub, hdisj, hpad⟩ :=
    exists_padded_family A hA hD
  -- the complements of the `B i` are nonempty (this is where `hZ` is used)
  have hne : ∀ i, (B i)ᶜ.Nonempty := by
    intro i
    obtain ⟨z, hz⟩ := hZ (ctr i) (D / 2)
    exact ⟨z, fun hzB ↦ hz (hBsub i hzB)⟩
  have hK : (0 : ℝ) < Fintype.card P := by exact_mod_cast hKpos
  -- `ψ > 0` on `{d(·, A) ≤ s/6}` (Lemma 2.3 with a small `t > 0`)
  have hpsi_pos : ∀ y, infDist y (A : Set Z) ≤ s / 6 → 0 < psi B y := by
    intro y hy
    have hΛ : 1 ≤ logStar (A.card : ℝ) := one_le_logStar _
    set t := D / (32 * logStar (A.card : ℝ)) with ht_def
    have ht : 0 < t := div_pos hD (by linarith)
    have ht' : t ≤ D / 32 := div_le_div_of_nonneg_left hD.le (by norm_num) (by linarith)
    have h1 : infDist y (A : Set Z) + t ≤ D / 4 := by linarith
    have h2 : 32 * t * logStar ((ballCount A y (D / 2 + t) : ℝ) /
        (ballCount A y (D / 4 - t) : ℝ)) ≤ D := by
      have hρ := logStar_le_logStar (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (div_ballCount_le_card A y (D / 2 + t) (D / 4 - t))
      calc 32 * t * logStar _ ≤ 32 * t * logStar (A.card : ℝ) :=
            mul_le_mul_of_nonneg_left hρ (by linarith)
        _ = D := by
            rw [ht_def]
            field_simp
    have h3 := hpad y t ht.le h1 h2
    have h4 := mul_ncard_le_psi hne y t
    have h5 : t * ((Fintype.card P : ℝ) / 2) ≤ t * ({i | closedBall y t ⊆ B i}.ncard : ℝ) :=
      mul_le_mul_of_nonneg_left h3 ht.le
    have h6 : 0 < t * ((Fintype.card P : ℝ) / 2) := mul_pos ht (by linarith)
    linarith
  -- distances from the centers
  have hctr_dist : ∀ i y, y ∈ B i → dist (ctr i) (near y) ≤ D / 2 + infDist y (A : Set Z) := by
    intro i y hy
    have h1 : dist y (ctr i) ≤ D / 2 := mem_closedBall.1 (hBsub i hy)
    calc dist (ctr i) (near y) ≤ dist (ctr i) y + dist y (near y) := dist_triangle _ _ _
      _ ≤ D / 2 + infDist y (A : Set Z) := by
          rw [dist_comm, (hnear y).2]
          linarith
  have hfA : ∀ i y, ‖f (ctr i) - f (near y)‖ ≤ dist (ctr i) (near y) := by
    intro i y
    rw [← dist_eq_norm]
    have := hf.dist_le_mul (ctr i) (hctrA i) (near y) (hnear y).1
    simpa using this
  refine ⟨scaleMap A f near B ctr (s / 6), ?_, ?_⟩
  · -- `‖F y - f (near y)‖ ≤ s`
    intro y
    by_cases hy : infDist y (A : Set Z) ≤ s / 6
    · rw [scaleMap_sub hy (hpsi_pos y hy)]
      calc ‖∑ i, phiI B i y • (f (ctr i) - f (near y))‖
          ≤ ∑ i, ‖phiI B i y • (f (ctr i) - f (near y))‖ := norm_sum_le _ _
        _ = ∑ i, phiI B i y * ‖f (ctr i) - f (near y)‖ := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (phiI_nonneg B i y)]
        _ ≤ ∑ i, phiI B i y * s := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            by_cases hi : y ∈ B i
            · refine mul_le_mul_of_nonneg_left ?_ (phiI_nonneg B i y)
              have := hctr_dist i y hi
              linarith [hfA i y]
            · have : phiI B i y = 0 := by
                by_contra h
                exact hi (mem_of_phiI_ne_zero h)
              simp [this]
        _ = s := by rw [← Finset.sum_mul, sum_phiI (hpsi_pos y hy), one_mul]
    · rw [scaleMap_of_not_le hy, sub_self, norm_zero]
      exact hs.le
  · -- the pointwise Lipschitz bound
    intro x hx
    have hxa : dist x (near x) = infDist x (A : Set Z) := (hnear x).2
    set a := near x with ha_def
    set L := logStar ((ballCount A a s : ℝ) / (ballCount A a (s / 4) : ℝ)) with hL_def
    have hL : 1 ≤ L := one_le_logStar _
    have hLpos : 0 < L := by linarith
    set t := s / (24 * L) with ht_def
    have ht : 0 < t := div_pos hs (by linarith)
    have ht' : t ≤ s / 24 := div_le_div_of_nonneg_left hs.le (by norm_num) (by linarith)
    -- the padding estimate `ψ x ≥ K t / 2`
    have hpsi_x : t * (Fintype.card P : ℝ) / 2 ≤ psi B x := by
      have h1 : infDist x (A : Set Z) + t ≤ D / 4 := by linarith
      have hN : ballCount A x (D / 2 + t) ≤ ballCount A a s :=
        ballCount_le_ballCount A (by rw [dist_comm, hxa]; linarith)
      have hD' : ballCount A a (s / 4) ≤ ballCount A x (D / 4 - t) :=
        ballCount_le_ballCount A (by rw [hxa]; linarith)
      have hpos : 0 < ballCount A a (s / 4) := ballCount_pos (hnear x).1 (by linarith)
      have hρ : (ballCount A x (D / 2 + t) : ℝ) / (ballCount A x (D / 4 - t) : ℝ) ≤
          (ballCount A a s : ℝ) / (ballCount A a (s / 4) : ℝ) :=
        div_le_div₀ (Nat.cast_nonneg _) (by exact_mod_cast hN) (Nat.cast_pos.2 hpos)
          (by exact_mod_cast hD')
      have h2 : 32 * t * logStar ((ballCount A x (D / 2 + t) : ℝ) /
          (ballCount A x (D / 4 - t) : ℝ)) ≤ D := by
        calc 32 * t * logStar _ ≤ 32 * t * L :=
              mul_le_mul_of_nonneg_left
                (logStar_le_logStar (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hρ)
                (by linarith)
          _ = 4 / 3 * s := by
              rw [ht_def]
              field_simp
              ring
          _ ≤ D := by linarith
      have h3 := hpad x t ht.le h1 h2
      have h4 := mul_ncard_le_psi hne x t
      have h5 : t * ((Fintype.card P : ℝ) / 2) ≤ t * ({i | closedBall x t ⊆ B i}.ncard : ℝ) :=
        mul_le_mul_of_nonneg_left h3 ht.le
      linarith
    apply lipAt_of_eventually_le
    filter_upwards [ball_mem_nhds x (show 0 < s / 24 by linarith)] with x' hx'
    have hxx' : dist x x' < s / 24 := mem_ball'.1 hx'
    have hx'A : infDist x' (A : Set Z) ≤ s / 6 := by
      have := infDist_le_infDist_add_dist (x := x') (y := x) (s := (A : Set Z))
      rw [dist_comm] at this
      linarith
    have hxA : infDist x (A : Set Z) ≤ s / 6 := by linarith
    have hψx := hpsi_pos x hxA
    have hψx' := hpsi_pos x' hx'A
    set d := dist x x' with hd_def
    have hd : 0 ≤ d := dist_nonneg
    -- the key identity
    have hdiff : scaleMap A f near B ctr (s / 6) x - scaleMap A f near B ctr (s / 6) x' =
        ∑ i, (phiI B i x - phiI B i x') • (f (ctr i) - f a) := by
      have e : scaleMap A f near B ctr (s / 6) x - scaleMap A f near B ctr (s / 6) x' =
          (scaleMap A f near B ctr (s / 6) x - f a) -
            (scaleMap A f near B ctr (s / 6) x' - f a) := by abel
      rw [e, scaleMap_sub hxA hψx, scaleMap_sub hx'A hψx', ← Finset.sum_sub_distrib]
      simp only [sub_smul]
    -- the relevant centers are close to `a`
    have hw : ∀ i, x ∈ B i ∨ x' ∈ B i →
        ‖f (ctr i) - f a‖ ≤ D / 2 + infDist x (A : Set Z) + d := by
      intro i hi
      refine (hfA i x).trans ?_
      rcases hi with hi | hi
      · have := hctr_dist i x hi
        linarith
      · have h1 : dist x' (ctr i) ≤ D / 2 := mem_closedBall.1 (hBsub i hi)
        calc dist (ctr i) a ≤ dist (ctr i) x' + dist x' a := dist_triangle _ _ _
          _ ≤ dist (ctr i) x' + (dist x' x + dist x a) := by
              gcongr
              exact dist_triangle _ _ _
          _ ≤ D / 2 + infDist x (A : Set Z) + d := by
              rw [dist_comm (ctr i), dist_comm x' x, hxa]
              linarith
    have hsum := sum_abs_phiI_sub_le part hdisj hψx hψx' (B := B)
    have hkey : 2 / psi B x * (2 * Fintype.card P * d) ≤ 192 * L / s * d := by
      have htK : 0 < t * (Fintype.card P : ℝ) / 2 := by positivity
      calc 2 / psi B x * (2 * Fintype.card P * d) = (4 * Fintype.card P * d) / psi B x := by
            ring
        _ ≤ (4 * Fintype.card P * d) / (t * (Fintype.card P : ℝ) / 2) :=
            div_le_div_of_nonneg_left (by positivity) htK hpsi_x
        _ = 192 * L / s * d := by
            rw [ht_def]
            field_simp
            ring
    have hR : D / 2 + infDist x (A : Set Z) + d ≤ s := by linarith
    have hR0 : 0 ≤ D / 2 + infDist x (A : Set Z) + d := by
      have := infDist_nonneg (x := x) (s := (A : Set Z))
      linarith
    calc dist (scaleMap A f near B ctr (s / 6) x) (scaleMap A f near B ctr (s / 6) x')
        = ‖scaleMap A f near B ctr (s / 6) x - scaleMap A f near B ctr (s / 6) x'‖ :=
          dist_eq_norm _ _
      _ = ‖∑ i, (phiI B i x - phiI B i x') • (f (ctr i) - f a)‖ := by rw [hdiff]
      _ ≤ ∑ i, ‖(phiI B i x - phiI B i x') • (f (ctr i) - f a)‖ := norm_sum_le _ _
      _ = ∑ i, |phiI B i x - phiI B i x'| * ‖f (ctr i) - f a‖ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i, |phiI B i x - phiI B i x'| * (D / 2 + infDist x (A : Set Z) + d) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          by_cases hi : x ∈ B i ∨ x' ∈ B i
          · exact mul_le_mul_of_nonneg_left (hw i hi) (abs_nonneg _)
          · rw [not_or] at hi
            have h1 : phiI B i x = 0 := by
              by_contra h
              exact hi.1 (mem_of_phiI_ne_zero h)
            have h2 : phiI B i x' = 0 := by
              by_contra h
              exact hi.2 (mem_of_phiI_ne_zero h)
            simp [h1, h2]
      _ = (∑ i, |phiI B i x - phiI B i x'|) * (D / 2 + infDist x (A : Set Z) + d) := by
          rw [Finset.sum_mul]
      _ ≤ (192 * L / s * d) * s :=
          mul_le_mul (hsum.trans hkey) hR hR0 (by positivity)
      _ = 192 * L * d := by
          field_simp
      _ ≤ 200 * L * d := by nlinarith

end LipschitzExtension
