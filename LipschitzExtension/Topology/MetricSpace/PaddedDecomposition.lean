/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Set.Card

/-!
# Padded decompositions with random radii

This file proves the replacement of Lemma 2.3 of [Basso2024] given in item 1 of the errata
[BassoClaude2026], which is needed for the corrected Lemma 4.1 and hence for Theorem 1.5 of
[Basso2024]. It is a de-randomized version of the partitions with random radii of
Calinescu–Karloff–Rabani (see also Fakcharoenphol–Rao–Talwar).

**Lemma 2.3 (replacement).** Let `A` be a finite subset of a metric space `X`, and let `D > 0`.
Then there are an integer `K ≥ 1` and a finite family `(B i)_{i ∈ I}` of subsets of `X` with the
following properties. The family is the union of `K` families of pairwise disjoint sets, and every
`B i` is contained in `B(a i, D/2)` for some `a i ∈ A`. Moreover, if `x ∈ X` and `t ≥ 0` satisfy
`d(x, A) + t ≤ D/4` and `32 · t · log(#B_A(x, D/2 + t) / #B_A(x, D/4 - t)) ≤ D`, then
`B(x, t) ⊆ B i` for at least `K/2` indices `i`. Here `log s` stands for `max 1 (log s)`
(`logStar`) and `B_A(x, r) = A ∩ B(x, r)` for the closed ball `B(x, r)`, so that
`#B_A(x, r) = ballCount A x r`.

## Main definitions

* `logStar s = max 1 (log s)`: the convention of the errata for Lemmas 2.3 and 4.1.
* `ballCount A x r`: the number of points of `A` in the closed ball `B(x, r)`.
* `PaddedFamily.cluster f π r a`: the cluster of `a` in the partition defined by the enumeration
  `π` and the radius `r`.

## Main statements

* `exists_padded_family`: Lemma 2.3 of [Basso2024], replacement version of errata item 1.
* `PaddedFamily.card_bad_le`: the counting estimate at the heart of the proof.

## Proof outline

This is the proof of the errata. Let `n = #A`, `M = ⌈4 log n⌉` (with `log = logStar`, so
`M ≥ 4`), `K = M · n!` and `R_l = D/4 + (l - 1) D/(4M)` for `l = 1, …, M` (note `R_l < D/2`).
Every enumeration `π` of `A` and every `l` define a partition of `{y ∈ X : d(y, A) ≤ R_l}`: the
point `y` belongs to the cluster of the first `a ∈ A`, with respect to `π`, such that
`d(y, a) ≤ R_l`. The family consists of all these clusters (indexed by `(π, l, a)`; the `K`
"parts" are indexed by `(π, l)`).

Let `x, t` be as above and let `ρ` be the quotient in the logarithm. For every pair `(π, l)` the
point `x` lies in exactly one cluster (as `d(x, A) ≤ R_l - t`). If `B(x, t)` is not contained in
this cluster, then the first `a ∈ A` with `d(x, a) ≤ R_l + t` satisfies `R_l - t < d(x, a)` and
precedes all other points of `A` at distance at most `d(x, a)` from `x`
(`PaddedFamily.exists_bad_witness`). [If `d(x, a) ≤ R_l - t` then every `y ∈ B(x, t)` has
`d(y, a) ≤ R_l` while every earlier `b` has `d(y, b) > R_l`.] For fixed `a`, the first condition
holds for at most `8tM/D + 1` values of `l` (`PaddedFamily.card_radii_le`: the `R_l` are
`D/(4M)`-spaced and lie in `[d(x,a) - t, d(x,a) + t)`), and the second one for at most
`n!/#S_a` enumerations, where `S_a = {b ∈ A : d(x, b) ≤ d(x, a)}`
(`PaddedFamily.card_first_mul_card_le`, by symmetry: for `a, a' ∈ S`, `π ↦ π ∘ swap a a'`
exchanges "`a` is first in `S`" and "`a'` is first in `S`"). Only `a` with
`D/4 - t < d(x, a) ≤ D/2 + t` contribute, and for those
`∑ 1/#S_a ≤ log(#B_A(x, D/2 + t) / #B_A(x, D/4 - t))` (`PaddedFamily.sum_inv_card_le_log`: group
the points by distance and use `c/(P + c) ≤ log((P + c)/P)`; note `#B_A(x, D/4 - t) ≥ 1`).
Hence `B(x, t)` fails to be contained in the cluster of `x` for at most
`(8tM/D + 1) · n! · log ρ` pairs `(π, l)`. Since `32 t log ρ ≤ D` and `log ρ ≤ log n ≤ M/4`,
this is at most `K/4 + K/4`.

## Implementation notes

The family is indexed by `((A ≃ Fin n) × Fin M) × A` (enumeration, radius, center), and its
`K = n! M` parts by `(A ≃ Fin n) × Fin M`. The radii are
`PaddedFamily.radius D M l = D/4 + l D/(4M)` for `l = 0, …, M - 1`, i.e. the radius `R_{l+1}`
above.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
* G. Calinescu, H. Karloff and Y. Rabani, *Approximation algorithms for the 0-extension problem*,
  SIAM J. Comput. 34 (2004), no. 2, 358–372
-/

open Set Metric

open scoped Nat

namespace LipschitzExtension

/-- `logStar s = max 1 (log s)`: the convention of the errata for Lemmas 2.3 and 4.1. -/
noncomputable def logStar (s : ℝ) : ℝ := max 1 (Real.log s)

theorem one_le_logStar (s : ℝ) : 1 ≤ logStar s := le_max_left _ _

theorem log_le_logStar (s : ℝ) : Real.log s ≤ logStar s := le_max_right _ _

theorem logStar_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : logStar s ≤ logStar t :=
  max_le_max le_rfl (Real.log_le_log hs hst)

variable {X : Type*} [MetricSpace X]

/-- The number `ballCount A x r = #(A ∩ B(x, r))` of points of `A` in the closed ball
`B(x, r)`. -/
noncomputable def ballCount (A : Finset X) (x : X) (r : ℝ) : ℕ :=
  (A.filter fun a ↦ dist x a ≤ r).card

namespace PaddedFamily

/-! ### Auxiliary lemmas for Lemma 2.3 -/

/-- Harmonic-type bound: for weights `w` and `P > 0`,
`∑_{a ∈ T} 1/(P + #{b ∈ T | w b ≤ w a}) ≤ log((P + #T)/P)`. The proof removes a point of maximal
weight and uses `1/(P' + 1) ≤ log((P' + 1)/P')`. -/
theorem harmonic_bound {β : Type*} (w : β → ℝ) {P : ℝ} (hP : 0 < P)
    (T : Finset β) :
    ∑ a ∈ T, 1 / (P + ((T.filter fun b ↦ w b ≤ w a).card : ℝ)) ≤
      Real.log ((P + T.card) / P) := by
  classical
  induction T using Finset.induction_on_max_value w with
  | empty => simp
  | insert a s ha hmax ih =>
    rw [Finset.sum_insert ha]
    have h1 : (insert a s).filter (fun b ↦ w b ≤ w a) = insert a s := by
      apply Finset.filter_true_of_mem
      intro b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact le_rfl
      · exact hmax b hb
    have h2 : ∑ b ∈ s, 1 / (P + (((insert a s).filter fun c ↦ w c ≤ w b).card : ℝ))
        ≤ ∑ b ∈ s, 1 / (P + ((s.filter fun c ↦ w c ≤ w b).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro b _
      apply one_div_le_one_div_of_le
      · positivity
      · have : (s.filter fun c ↦ w c ≤ w b).card ≤
            ((insert a s).filter fun c ↦ w c ≤ w b).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
        have : ((s.filter fun c ↦ w c ≤ w b).card : ℝ) ≤
            (((insert a s).filter fun c ↦ w c ≤ w b).card : ℝ) := by exact_mod_cast this
        linarith
    rw [h1, Finset.card_insert_of_notMem ha]
    have hpos : 0 < P + (s.card : ℝ) := by positivity
    have key : 1 / (P + ((s.card + 1 : ℕ) : ℝ)) ≤
        Real.log ((P + ((s.card + 1 : ℕ) : ℝ)) / (P + s.card)) := by
      have := Real.one_sub_inv_le_log_of_pos
        (x := (P + ((s.card + 1 : ℕ) : ℝ)) / (P + s.card)) (by positivity)
      convert this using 1
      push_cast
      field_simp
      ring
    have hlog : Real.log ((P + ((s.card + 1 : ℕ) : ℝ)) / P) =
        Real.log ((P + ((s.card + 1 : ℕ) : ℝ)) / (P + s.card)) +
          Real.log ((P + s.card) / P) := by
      rw [← Real.log_mul]
      · congr 1; field_simp
      · positivity
      · positivity
    linarith

/-- The harmonic bound in the form used for Lemma 2.3: for weights `w` (the distances to `x`),
`∑_{u < w a ≤ v} 1/#{b | w b ≤ w a} ≤ log(#{b | w b ≤ v} / #{b | w b ≤ u})`. -/
theorem sum_inv_card_le_log {α : Type*} [Fintype α] (w : α → ℝ) {u v : ℝ}
    (huv : u ≤ v) (hpos : 0 < (Finset.univ.filter fun b ↦ w b ≤ u).card) :
    ∑ a ∈ Finset.univ.filter (fun a ↦ u < w a ∧ w a ≤ v),
        1 / ((Finset.univ.filter fun b ↦ w b ≤ w a).card : ℝ) ≤
      Real.log (((Finset.univ.filter fun b ↦ w b ≤ v).card : ℝ) /
        ((Finset.univ.filter fun b ↦ w b ≤ u).card : ℝ)) := by
  have h1 : ∀ a ∈ Finset.univ.filter (fun a ↦ u < w a ∧ w a ≤ v),
      (Finset.univ.filter fun b ↦ w b ≤ w a).card =
        (Finset.univ.filter fun b ↦ w b ≤ u).card +
          ((Finset.univ.filter (fun a ↦ u < w a ∧ w a ≤ v)).filter fun b ↦ w b ≤ w a).card := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun b ↦ w b ≤ w a)
      (fun b ↦ w b ≤ u)]
    congr 1
    · congr 1
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨by linarith [ha.2.1], h⟩
    · congr 1
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
      constructor
      · exact fun h ↦ ⟨⟨h.2, by linarith [ha.2.2]⟩, h.1⟩
      · exact fun h ↦ ⟨h.2, h.1.1⟩
  have h2 : (Finset.univ.filter fun b ↦ w b ≤ v).card =
      (Finset.univ.filter fun b ↦ w b ≤ u).card +
        (Finset.univ.filter (fun a ↦ u < w a ∧ w a ≤ v)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun b ↦ w b ≤ v)
      (fun b ↦ w b ≤ u)]
    congr 1
    · congr 1
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨by linarith, h⟩
    · congr 1
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
      constructor
      · exact fun h ↦ ⟨h.2, h.1⟩
      · exact fun h ↦ ⟨h.2, h.1⟩
  have hP : (0 : ℝ) < (Finset.univ.filter fun b ↦ w b ≤ u).card := by exact_mod_cast hpos
  calc ∑ a ∈ Finset.univ.filter (fun a ↦ u < w a ∧ w a ≤ v),
        1 / ((Finset.univ.filter fun b ↦ w b ≤ w a).card : ℝ)
      = ∑ a ∈ Finset.univ.filter (fun a ↦ u < w a ∧ w a ≤ v),
          1 / (((Finset.univ.filter fun b ↦ w b ≤ u).card : ℝ) +
            (((Finset.univ.filter (fun a ↦ u < w a ∧ w a ≤ v)).filter
              fun b ↦ w b ≤ w a).card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [h1 a ha]
        push_cast
        rfl
    _ ≤ Real.log ((((Finset.univ.filter fun b ↦ w b ≤ u).card : ℝ) +
          (Finset.univ.filter (fun a ↦ u < w a ∧ w a ≤ v)).card) /
          ((Finset.univ.filter fun b ↦ w b ≤ u).card : ℝ)) := harmonic_bound w hP _
    _ = _ := by rw [h2]; push_cast; rfl

/-- The transposition `Equiv.swap a a'` of two elements of `S` maps `S` to itself. -/
theorem swap_mem_of_mem {α : Type*} [DecidableEq α] {S : Finset α} {a a' b : α} (ha : a ∈ S)
    (ha' : a' ∈ S) (hb : b ∈ S) : Equiv.swap a a' b ∈ S := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

/-- Symmetry: the number of enumerations `π : α ≃ Fin n` for which `a` is the `π`-first element
of `S` is at most `n!/#S` (more precisely, at most the number of all enumerations divided by
`#S`). -/
theorem card_first_mul_card_le {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (S : Finset α) {a : α} (ha : a ∈ S) :
    (Finset.univ.filter (fun π : α ≃ Fin n ↦ ∀ b ∈ S, π a ≤ π b)).card * S.card ≤
      Fintype.card (α ≃ Fin n) := by
  set E : α → Finset (α ≃ Fin n) :=
    fun a' ↦ Finset.univ.filter (fun π : α ≃ Fin n ↦ ∀ b ∈ S, π a' ≤ π b) with hE
  have hcard : ∀ a' ∈ S, (E a').card = (E a).card := by
    intro a' ha'
    refine Finset.card_nbij' (fun π ↦ (Equiv.swap a a').trans π)
      (fun π ↦ (Equiv.swap a a').trans π) ?_ ?_ ?_ ?_
    · intro π hπ
      simp only [hE, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
      intro b hb
      simp only [Equiv.trans_apply, Equiv.swap_apply_left]
      exact hπ _ (swap_mem_of_mem ha ha' hb)
    · intro π hπ
      simp only [hE, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
      intro b hb
      simp only [Equiv.trans_apply, Equiv.swap_apply_right]
      exact hπ _ (swap_mem_of_mem ha ha' hb)
    · intro π _
      ext b
      simp [Equiv.swap_apply_self]
    · intro π _
      ext b
      simp [Equiv.swap_apply_self]
  have hdisj : (S : Set α).PairwiseDisjoint E := by
    intro a₁ ha₁ a₂ ha₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro π h1 h2
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hne (π.injective (le_antisymm (h1 a₂ ha₂) (h2 a₁ ha₁)))
  calc (E a).card * S.card = ∑ a' ∈ S, (E a').card := by
        rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]
    _ = (S.biUnion E).card := (Finset.card_biUnion hdisj).symm
    _ ≤ Fintype.card (α ≃ Fin n) := Finset.card_le_univ _

/-- The `l`-th radius `R l = D/4 + l · D/(4M)` of the construction (used for
`l = 0, …, M - 1`). -/
noncomputable def radius (D : ℝ) (M : ℕ) (l : ℕ) : ℝ := D / 4 + l * (D / (4 * M))

/-- All radii are at least `D/4`. -/
theorem le_radius {D : ℝ} (hD : 0 < D) (M l : ℕ) : D / 4 ≤ radius D M l := by
  unfold radius
  have : (0 : ℝ) ≤ l * (D / (4 * M)) := by positivity
  linarith

/-- The radii `R l` with `l < M` are at most `D/2`. -/
theorem radius_le {D : ℝ} (hD : 0 < D) {M l : ℕ} (hl : l < M) : radius D M l ≤ D / 2 := by
  unfold radius
  have hM : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hl)
  have hl' : (l : ℝ) ≤ M := by exact_mod_cast hl.le
  have h1 : (l : ℝ) * (D / (4 * M)) ≤ M * (D / (4 * M)) :=
    mul_le_mul_of_nonneg_right hl' (by positivity)
  have h2 : (M : ℝ) * (D / (4 * M)) = D / 4 := by field_simp
  linarith

/-- For fixed `d`, the condition `R l - t < d ≤ R l + t` holds for at most `8tM/D + 1`
values of `l`. -/
theorem card_radii_le {M : ℕ} (hM : 0 < M) {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) (d : ℝ) :
    ((Finset.univ.filter (fun l : Fin M ↦
        radius D M l - t < d ∧ d ≤ radius D M l + t)).card : ℝ) ≤ 8 * t * M / D + 1 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set h : ℝ := D / (4 * M) with hh
  have hpos : 0 < h := by positivity
  set F := Finset.univ.filter (fun l : Fin M ↦
        radius D M l - t < d ∧ d ≤ radius D M l + t) with hF
  set α₀ : ℝ := (d - t - D / 4) / h with hα₀
  set β₀ : ℝ := (d + t - D / 4) / h with hβ₀
  have hsub : F.map Fin.valEmbedding ⊆ Finset.Ico ⌈α₀⌉₊ ⌈β₀⌉₊ := by
    intro k hk
    simp only [Finset.mem_map, hF, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨l, ⟨h1, h2⟩, rfl⟩ := hk
    unfold radius at h1 h2
    rw [Finset.mem_Ico]
    constructor
    · rw [Nat.ceil_le, hα₀, div_le_iff₀ hpos]
      simp only [Fin.valEmbedding_apply]
      linarith
    · rw [Nat.lt_ceil, hβ₀, lt_div_iff₀ hpos]
      simp only [Fin.valEmbedding_apply]
      linarith
  have hcard : F.card ≤ ⌈β₀⌉₊ - ⌈α₀⌉₊ := by
    rw [← Finset.card_map Fin.valEmbedding, ← Nat.card_Ico]
    exact Finset.card_le_card hsub
  have hβα : β₀ - α₀ = 8 * t * M / D := by
    rw [hβ₀, hα₀, hh]
    field_simp
    ring
  have h8 : 0 ≤ 8 * t * M / D := div_nonneg (by positivity) hD.le
  rcases le_or_gt ⌈β₀⌉₊ ⌈α₀⌉₊ with hle | hlt
  · have : F.card = 0 := by omega
    rw [this]
    simp only [Nat.cast_zero]
    linarith
  · have hβpos : 0 < β₀ := Nat.ceil_pos.1 (lt_of_le_of_lt (Nat.zero_le _) hlt)
    have h1 : (⌈β₀⌉₊ : ℝ) < β₀ + 1 := Nat.ceil_lt_add_one hβpos.le
    have h2 : α₀ ≤ (⌈α₀⌉₊ : ℝ) := Nat.le_ceil _
    have : (F.card : ℝ) ≤ ((⌈β₀⌉₊ - ⌈α₀⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
    rw [Nat.cast_sub hlt.le] at this
    linarith

/-- The cluster of `a` in the partition defined by the enumeration `π` and the radius `r`:
the points `y` with `d(y, a) ≤ r` such that `a` is the `π`-first point with this property. -/
def cluster {α : Type*} {n : ℕ} (f : α → X) (π : α ≃ Fin n) (r : ℝ) (a : α) : Set X :=
  {y | dist y (f a) ≤ r ∧ ∀ b, dist y (f b) ≤ r → π a ≤ π b}

/-- The cluster of `a` is contained in the closed ball `B(f a, r)`. -/
theorem cluster_subset {α : Type*} {n : ℕ} (f : α → X) (π : α ≃ Fin n) (r : ℝ) (a : α) :
    cluster f π r a ⊆ closedBall (f a) r := fun _ hy ↦ hy.1

/-- For fixed `π` and `r`, the clusters of distinct points are disjoint. -/
theorem disjoint_cluster {α : Type*} {n : ℕ} (f : α → X) (π : α ≃ Fin n) (r : ℝ) {a a' : α}
    (h : a ≠ a') : Disjoint (cluster f π r a) (cluster f π r a') := by
  rw [Set.disjoint_left]
  intro y hy hy'
  exact h (π.injective (le_antisymm (hy.2 a' hy'.1) (hy'.2 a hy.1)))

/-- If `B(x, t)` is contained in no cluster of the partition `(π, r)`, then the `π`-first `a`
with `d(x, a) ≤ r + t` satisfies `r - t < d(x, a)` and precedes all points `b` with
`d(x, b) ≤ d(x, a)`. -/
theorem exists_bad_witness {α : Type*} {n : ℕ} (f : α → X) (π : α ≃ Fin n)
    {r t : ℝ} {x : X} (h₀ : ∃ a₀, dist x (f a₀) ≤ r + t)
    (hbad : ¬ ∃ a, closedBall x t ⊆ cluster f π r a) :
    ∃ a, r - t < dist x (f a) ∧ dist x (f a) ≤ r + t ∧
      ∀ b, dist x (f b) ≤ dist x (f a) → π a ≤ π b := by
  classical
  have : Fintype α := Fintype.ofEquiv (Fin n) π.symm
  obtain ⟨a₀, ha₀⟩ := h₀
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun b ↦ dist x (f b) ≤ r + t) π
    ⟨a₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha₀⟩⟩
  have ha' : dist x (f a) ≤ r + t := (Finset.mem_filter.1 ha).2
  have hmin' : ∀ b, dist x (f b) ≤ r + t → π a ≤ π b :=
    fun b hb ↦ hmin b (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)
  refine ⟨a, ?_, ha', fun b hb ↦ hmin' b (hb.trans ha')⟩
  by_contra hcon
  push Not at hcon
  apply hbad
  refine ⟨a, fun y hy ↦ ⟨?_, fun b hb ↦ hmin' b ?_⟩⟩
  · rw [mem_closedBall] at hy
    calc dist y (f a) ≤ dist y x + dist x (f a) := dist_triangle _ _ _
      _ ≤ t + (r - t) := add_le_add hy hcon
      _ = r := by ring
  · rw [mem_closedBall] at hy
    calc dist x (f b) ≤ dist x y + dist y (f b) := dist_triangle _ _ _
      _ ≤ t + r := add_le_add (by rwa [dist_comm]) hb
      _ = r + t := by ring

open Classical in
/-- The main counting estimate: under the assumptions of Lemma 2.3 (replacement version) and if
`log n ≤ M/4`, the ball `B(x, t)` fails to be contained in a cluster for at most `K/2 = n! M / 2`
of the partitions `(π, l)`. -/
theorem card_bad_le {α : Type*} [Fintype α] [DecidableEq α] (f : α → X) {n M : ℕ} (hM : 0 < M)
    (hn : Fintype.card α = n) {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) {x : X}
    (h₀ : ∃ a₀, dist x (f a₀) ≤ D / 4 - t)
    (hlog : 32 * t * logStar (((Finset.univ.filter fun b ↦ dist x (f b) ≤ D / 2 + t).card : ℝ) /
      ((Finset.univ.filter fun b ↦ dist x (f b) ≤ D / 4 - t).card : ℝ)) ≤ D)
    (hMn : logStar n ≤ M / 4) :
    ((Finset.univ.filter (fun p : (α ≃ Fin n) × Fin M ↦
        ¬ ∃ a, closedBall x t ⊆ cluster f p.1 (radius D M p.2) a)).card : ℝ) ≤
      (n ! * M : ℝ) / 2 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  -- the set of bad parts is covered by the sets of pairs `(π, l)` attached to points `a ∈ T`
  have hsub : Finset.univ.filter (fun p : (α ≃ Fin n) × Fin M ↦
        ¬ ∃ a, closedBall x t ⊆ cluster f p.1 (radius D M p.2) a) ⊆
      (Finset.univ.filter
          (fun a : α ↦ D / 4 - t < dist x (f a) ∧ dist x (f a) ≤ D / 2 + t)).biUnion
        (fun a ↦ (Finset.univ.filter (fun π : α ≃ Fin n ↦
            ∀ b ∈ Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a)), π a ≤ π b)) ×ˢ
          (Finset.univ.filter (fun l : Fin M ↦
            radius D M l - t < dist x (f a) ∧ dist x (f a) ≤ radius D M l + t))) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨a₀, ha₀⟩ := h₀
    have hR1 := le_radius hD M p.2
    have hR2 := radius_le hD p.2.2
    obtain ⟨a, h1, h2, h3⟩ := exists_bad_witness f p.1 (r := radius D M p.2)
      ⟨a₀, by linarith⟩ hp.2
    rw [Finset.mem_biUnion]
    refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by linarith, by linarith⟩
    · rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, fun b hb ↦ h3 b (Finset.mem_filter.1 hb).2⟩,
        Finset.mem_univ _, h1, h2⟩
  have hfact : Fintype.card (α ≃ Fin n) = n ! := by
    rw [Fintype.card_equiv (Fintype.equivFinOfCardEq hn), hn]
  -- bound for each term
  have hterm : ∀ a ∈ Finset.univ.filter
      (fun a : α ↦ D / 4 - t < dist x (f a) ∧ dist x (f a) ≤ D / 2 + t),
      (((Finset.univ.filter (fun π : α ≃ Fin n ↦
            ∀ b ∈ Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a)), π a ≤ π b)) ×ˢ
          (Finset.univ.filter (fun l : Fin M ↦
            radius D M l - t < dist x (f a) ∧ dist x (f a) ≤ radius D M l + t))).card : ℝ) ≤
        (n ! : ℝ) * (8 * t * M / D + 1) *
          (1 / ((Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a))).card : ℝ)) := by
    intro a _
    rw [Finset.card_product, Nat.cast_mul]
    have haS : a ∈ Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a)) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩
    have hSpos : (0 : ℝ) < (Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a))).card := by
      exact_mod_cast Finset.card_pos.2 ⟨a, haS⟩
    have h1 := card_first_mul_card_le (n := n) _ haS
    rw [hfact] at h1
    have h1' : ((Finset.univ.filter (fun π : α ≃ Fin n ↦
          ∀ b ∈ Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a)), π a ≤ π b)).card : ℝ)
        ≤ (n ! : ℝ) *
          (1 / ((Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a))).card : ℝ)) := by
      rw [mul_one_div, le_div_iff₀ hSpos]
      exact_mod_cast h1
    have h2 := card_radii_le hM hD ht (dist x (f a))
    have h8 : 0 ≤ 8 * t * M / D + 1 := by
      have : 0 ≤ 8 * t * M / D := div_nonneg (by positivity) hD.le
      linarith
    calc _ ≤ ((n ! : ℝ) *
          (1 / ((Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a))).card : ℝ))) *
            (8 * t * M / D + 1) := mul_le_mul h1' h2 (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  -- the harmonic bound
  obtain ⟨a₀, ha₀⟩ := h₀
  have hpos : 0 < (Finset.univ.filter fun b ↦ dist x (f b) ≤ D / 4 - t).card :=
    Finset.card_pos.2 ⟨a₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha₀⟩⟩
  have hharm := sum_inv_card_le_log (fun a ↦ dist x (f a)) (u := D / 4 - t) (v := D / 2 + t)
    (by linarith) hpos
  -- the quotient `ρ`
  set ρ : ℝ := ((Finset.univ.filter fun b ↦ dist x (f b) ≤ D / 2 + t).card : ℝ) /
      ((Finset.univ.filter fun b ↦ dist x (f b) ≤ D / 4 - t).card : ℝ) with hρ
  have hρn : logStar ρ ≤ logStar n := by
    have hle : (Finset.univ.filter fun b ↦ dist x (f b) ≤ D / 4 - t).card ≤
        (Finset.univ.filter fun b ↦ dist x (f b) ≤ D / 2 + t).card :=
      Finset.card_le_card (Finset.monotone_filter_right _ fun b _ hb ↦ by linarith)
    have hden : (1 : ℝ) ≤ (Finset.univ.filter fun b ↦ dist x (f b) ≤ D / 4 - t).card := by
      exact_mod_cast hpos
    have hnum : ((Finset.univ.filter fun b ↦ dist x (f b) ≤ D / 2 + t).card : ℝ) ≤ n := by
      rw [← hn]; exact_mod_cast Finset.card_le_univ _
    have hnum' : (1 : ℝ) ≤ (Finset.univ.filter fun b ↦ dist x (f b) ≤ D / 2 + t).card := by
      exact_mod_cast hpos.trans_le hle
    apply logStar_mono
    · rw [hρ]; positivity
    · rw [hρ]
      calc _ ≤ ((Finset.univ.filter fun b ↦ dist x (f b) ≤ D / 2 + t).card : ℝ) :=
            div_le_self (by positivity) hden
        _ ≤ n := hnum
  -- combine
  have hL : 8 * t * M / D * logStar ρ ≤ M / 4 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    nlinarith
  have hsum : ∑ a ∈ Finset.univ.filter
      (fun a : α ↦ D / 4 - t < dist x (f a) ∧ dist x (f a) ≤ D / 2 + t),
      1 / ((Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a))).card : ℝ) ≤ logStar ρ :=
    hharm.trans (log_le_logStar _)
  have h8 : 0 ≤ 8 * t * M / D + 1 := by
    have : 0 ≤ 8 * t * M / D := div_nonneg (by positivity) hD.le
    linarith
  calc _ ≤ (((Finset.univ.filter (fun a : α ↦ D / 4 - t < dist x (f a) ∧
          dist x (f a) ≤ D / 2 + t)).biUnion
        (fun a ↦ (Finset.univ.filter (fun π : α ≃ Fin n ↦
            ∀ b ∈ Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a)), π a ≤ π b)) ×ˢ
          (Finset.univ.filter (fun l : Fin M ↦
            radius D M l - t < dist x (f a) ∧ dist x (f a) ≤ radius D M l + t)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ a ∈ Finset.univ.filter
          (fun a : α ↦ D / 4 - t < dist x (f a) ∧ dist x (f a) ≤ D / 2 + t),
          (((Finset.univ.filter (fun π : α ≃ Fin n ↦
            ∀ b ∈ Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a)), π a ≤ π b)) ×ˢ
          (Finset.univ.filter (fun l : Fin M ↦
            radius D M l - t < dist x (f a) ∧ dist x (f a) ≤ radius D M l + t))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ a ∈ Finset.univ.filter
          (fun a : α ↦ D / 4 - t < dist x (f a) ∧ dist x (f a) ≤ D / 2 + t),
          (n ! : ℝ) * (8 * t * M / D + 1) *
            (1 / ((Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a))).card : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (n ! : ℝ) * (8 * t * M / D + 1) * ∑ a ∈ Finset.univ.filter
          (fun a : α ↦ D / 4 - t < dist x (f a) ∧ dist x (f a) ≤ D / 2 + t),
            (1 / ((Finset.univ.filter (fun b ↦ dist x (f b) ≤ dist x (f a))).card : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (n ! : ℝ) * (8 * t * M / D + 1) * logStar ρ :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg _) h8)
    _ = (n ! : ℝ) * (8 * t * M / D * logStar ρ + logStar ρ) := by ring
    _ ≤ (n ! : ℝ) * (M / 4 + M / 4) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have : logStar ρ ≤ M / 4 := hρn.trans hMn
        linarith
    _ = (n ! * M : ℝ) / 2 := by ring

end PaddedFamily

universe u

open PaddedFamily in
/-- **Lemma 2.3** of [Basso2024], replacement version of errata item 1. The index type `ι` of the
family is finite; `part : ι → P` assigns to each member one of the `K = #P ≥ 1` partitions ("the
family is the union of `K` families of pairwise disjoint sets"); `ctr i ∈ A` is the center with
`B i ⊆ B(ctr i, D/2)`. If `t ≥ 0`, `d(x, A) + t ≤ D/4` and
`32 t logStar(ballCount A x (D/2 + t) / ballCount A x (D/4 - t)) ≤ D`, then `B(x, t) ⊆ B i` for
at least `K/2` indices `i`. -/
theorem exists_padded_family {X : Type u} [MetricSpace X] (A : Finset X) (hA : A.Nonempty)
    {D : ℝ} (hD : 0 < D) :
    ∃ (ι P : Type u) (_ : Fintype ι) (_ : Fintype P) (part : ι → P) (B : ι → Set X)
      (ctr : ι → X),
      0 < Fintype.card P ∧
      (∀ i, ctr i ∈ A) ∧
      (∀ i, B i ⊆ closedBall (ctr i) (D / 2)) ∧
      (∀ i j, part i = part j → i ≠ j → Disjoint (B i) (B j)) ∧
      ∀ (x : X) (t : ℝ), 0 ≤ t → infDist x (A : Set X) + t ≤ D / 4 →
        32 * t * logStar ((ballCount A x (D / 2 + t) : ℝ) / (ballCount A x (D / 4 - t) : ℝ))
          ≤ D →
        (Fintype.card P : ℝ) / 2 ≤ ({i | closedBall x t ⊆ B i}.ncard : ℝ) := by
  classical
  -- parameters: `n = #A`, `M = ⌈4 log n⌉`
  set n : ℕ := A.card with hn
  set M : ℕ := ⌈4 * logStar n⌉₊ with hM
  have hM4 : (4 : ℝ) ≤ M := le_trans (by linarith [one_le_logStar (n : ℝ)]) (Nat.le_ceil _)
  have hMpos : 0 < M := by exact_mod_cast (show (0 : ℝ) < M by linarith)
  have hMn : logStar n ≤ M / 4 := by
    have := Nat.le_ceil (4 * logStar n)
    rw [← hM] at this
    linarith
  have hcardα : Fintype.card {x // x ∈ A} = n := Fintype.card_coe A
  refine ⟨(({x // x ∈ A} ≃ Fin n) × Fin M) × {x // x ∈ A}, ({x // x ∈ A} ≃ Fin n) × Fin M,
    inferInstance, inferInstance, Prod.fst,
    fun i ↦ cluster (Subtype.val : {x // x ∈ A} → X) i.1.1 (radius D M i.1.2) i.2,
    fun i ↦ (i.2 : X), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_prod, Fintype.card_equiv (Fintype.equivFinOfCardEq hcardα),
      Fintype.card_fin, hcardα]
    exact Nat.mul_pos (Nat.factorial_pos _) hMpos
  · intro i
    exact i.2.2
  · intro i
    exact (cluster_subset _ _ _ _).trans
      (closedBall_subset_closedBall (radius_le hD i.1.2.2))
  · rintro ⟨p, a⟩ ⟨q, b⟩ hpq hne
    simp only at hpq
    subst hpq
    apply disjoint_cluster
    intro hab
    exact hne (Prod.ext rfl hab)
  · intro x t ht hxt hlog
    -- a point of `A` close to `x`
    obtain ⟨a₀, ha₀A, ha₀⟩ :=
      (A.finite_toSet.isCompact).exists_infDist_eq_dist (Finset.coe_nonempty.2 hA) x
    have h₀ : ∃ a₀ : {x // x ∈ A}, dist x (a₀ : X) ≤ D / 4 - t :=
      ⟨⟨a₀, ha₀A⟩, by simp only; linarith⟩
    -- `ballCount` in terms of the subtype
    have hball : ∀ r, ballCount A x r =
        (Finset.univ.filter fun b : {x // x ∈ A} ↦ dist x (b : X) ≤ r).card := by
      intro r
      rw [ballCount, ← Finset.card_map (Function.Embedding.subtype (· ∈ A))]
      congr 1
      ext y
      simp [and_comm]
    rw [hball, hball] at hlog
    have hbad := card_bad_le (Subtype.val : {x // x ∈ A} → X) hMpos hcardα hD ht h₀ hlog hMn
    -- good parts
    have hGB : (Finset.univ.filter (fun p : ({x // x ∈ A} ≃ Fin n) × Fin M ↦
          ∃ a, closedBall x t ⊆ cluster Subtype.val p.1 (radius D M p.2) a)).card +
        (Finset.univ.filter (fun p : ({x // x ∈ A} ≃ Fin n) × Fin M ↦
          ¬ ∃ a, closedBall x t ⊆ cluster Subtype.val p.1 (radius D M p.2) a)).card =
        Fintype.card (({x // x ∈ A} ≃ Fin n) × Fin M) :=
      Finset.card_filter_add_card_filter_not _
    have hK : Fintype.card (({x // x ∈ A} ≃ Fin n) × Fin M) = n ! * M := by
      rw [Fintype.card_prod, Fintype.card_equiv (Fintype.equivFinOfCardEq hcardα),
        Fintype.card_fin, hcardα]
    have hset : {i : (({x // x ∈ A} ≃ Fin n) × Fin M) × {x // x ∈ A} |
        closedBall x t ⊆ cluster Subtype.val i.1.1 (radius D M i.1.2) i.2} =
        ↑(Finset.univ.filter fun i : (({x // x ∈ A} ≃ Fin n) × Fin M) × {x // x ∈ A} ↦
          closedBall x t ⊆ cluster Subtype.val i.1.1 (radius D M i.1.2) i.2) := by
      ext i
      simp
    have hGle : (Finset.univ.filter (fun p : ({x // x ∈ A} ≃ Fin n) × Fin M ↦
          ∃ a, closedBall x t ⊆ cluster Subtype.val p.1 (radius D M p.2) a)).card ≤
        (Finset.univ.filter fun i : (({x // x ∈ A} ≃ Fin n) × Fin M) × {x // x ∈ A} ↦
          closedBall x t ⊆ cluster Subtype.val i.1.1 (radius D M i.1.2) i.2).card := by
      calc _ ≤ ((Finset.univ.filter fun i : (({x // x ∈ A} ≃ Fin n) × Fin M) × {x // x ∈ A} ↦
            closedBall x t ⊆ cluster Subtype.val i.1.1 (radius D M i.1.2) i.2).image
              Prod.fst).card := by
            apply Finset.card_le_card
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨a, ha⟩ := hp.2
            rw [Finset.mem_image]
            exact ⟨(p, a), Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩, rfl⟩
        _ ≤ _ := Finset.card_image_le
    change (Fintype.card (({x // x ∈ A} ≃ Fin n) × Fin M) : ℝ) / 2 ≤
      ({i : (({x // x ∈ A} ≃ Fin n) × Fin M) × {x // x ∈ A} |
        closedBall x t ⊆ cluster Subtype.val i.1.1 (radius D M i.1.2) i.2}.ncard : ℝ)
    rw [hset, Set.ncard_coe_finset]
    have hGB' : ((Finset.univ.filter (fun p : ({x // x ∈ A} ≃ Fin n) × Fin M ↦
          ∃ a, closedBall x t ⊆ cluster Subtype.val p.1 (radius D M p.2) a)).card : ℝ) +
        ((Finset.univ.filter (fun p : ({x // x ∈ A} ≃ Fin n) × Fin M ↦
          ¬ ∃ a, closedBall x t ⊆ cluster Subtype.val p.1 (radius D M p.2) a)).card : ℝ) =
        (n ! * M : ℝ) := by
      rw [hK] at hGB; exact_mod_cast hGB
    have hGle' : ((Finset.univ.filter (fun p : ({x // x ∈ A} ≃ Fin n) × Fin M ↦
          ∃ a, closedBall x t ⊆ cluster Subtype.val p.1 (radius D M p.2) a)).card : ℝ) ≤
        ((Finset.univ.filter fun i : (({x // x ∈ A} ≃ Fin n) × Fin M) × {x // x ∈ A} ↦
          closedBall x t ⊆ cluster Subtype.val i.1.1 (radius D M i.1.2) i.2).card : ℝ) := by
      exact_mod_cast hGle
    rw [hK]
    push_cast
    linarith

end LipschitzExtension
