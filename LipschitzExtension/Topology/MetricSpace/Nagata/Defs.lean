/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Data.Set.Card

/-!
# The condition `Nagata(n, c)`

This file defines the condition `Nagata(n, c)` of Definition 1.1 of [Basso2024]: a metric space
satisfies `Nagata(n, c)` if for every `s > 0` there is a covering whose members have diameter at
most `c s` and which has `s`-multiplicity at most `n + 1`, i.e. every subset of diameter `< s`
meets at most `n + 1` members of the covering.

## Main definitions

* `Nagata n c A`: the subset `A` (with the induced metric) satisfies `Nagata(n, c)`.

## Main statements

* `Nagata.nonneg`: a nonempty set satisfying `Nagata(n, c)` has `c ≥ 0`.
* `Nagata.mono`: `Nagata(n, c)` is monotone in `n` and `c`.
* `Nagata.image_isometry`: `Nagata(n, c)` is invariant under isometric embeddings.
* `ediam_lt_ofReal_of_finite`: a finite set whose pairwise distances are `< s` has diameter
  `< s` (used to construct test sets for the multiplicity condition).

## Implementation notes

We formulate the condition for a subset `A` of a pseudometric space `X` (with the induced
metric), and represent coverings as sets of subsets of `A`. Diameters of the "test sets" `E` are
measured with `Metric.ediam`, so that unbounded sets are not accidentally allowed (`Metric.diam`
of an unbounded set is `0`). Definition 1.1 of [Basso2024] assumes `c > 0`; we allow every real
`c` (a nonempty set can only satisfy `Nagata(n, c)` if `c ≥ 0`).

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open Set Metric

namespace LipschitzExtension

variable {X : Type*} [PseudoMetricSpace X]

/-- `Nagata n c A`: the subset `A` (with the induced metric) satisfies the condition
`Nagata(n, c)` of Definition 1.1 of [Basso2024]: for every `s > 0` there is a covering `𝓑` of `A`
by subsets of `A`, each of diameter at most `c * s`, such that every `E ⊆ A` of diameter `< s`
meets at most `n + 1` members of `𝓑`. -/
def Nagata (n : ℕ) (c : ℝ) (A : Set X) : Prop :=
  ∀ s : ℝ, 0 < s → ∃ 𝓑 : Set (Set X), (∀ B ∈ 𝓑, B ⊆ A) ∧ A ⊆ ⋃₀ 𝓑 ∧
    (∀ B ∈ 𝓑, ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ c * s) ∧
    ∀ E ⊆ A, Metric.ediam E < ENNReal.ofReal s → {B ∈ 𝓑 | (B ∩ E).Nonempty}.encard ≤ n + 1

/-- A finite set all of whose pairwise distances are `< s` has (extended) diameter `< s`. -/
theorem ediam_lt_ofReal_of_finite {E : Set X} (hE : E.Finite) {s : ℝ} (hs : 0 < s)
    (h : ∀ x ∈ E, ∀ y ∈ E, dist x y < s) : Metric.ediam E < ENNReal.ofReal s := by
  rcases E.eq_empty_or_nonempty with rfl | hne
  · simpa using hs
  obtain ⟨p, hp, hmax⟩ := (E ×ˢ E).exists_max_image (fun q : X × X ↦ dist q.1 q.2)
    (hE.prod hE) (hne.prod hne)
  calc Metric.ediam E ≤ ENNReal.ofReal (dist p.1 p.2) :=
        Metric.ediam_le_of_forall_dist_le fun x hx y hy ↦ hmax (x, y) ⟨hx, hy⟩
    _ < ENNReal.ofReal s := (ENNReal.ofReal_lt_ofReal_iff hs).2 (h _ hp.1 _ hp.2)

/-- A nonempty set satisfying `Nagata(n, c)` forces `c ≥ 0`. -/
theorem Nagata.nonneg {n : ℕ} {c : ℝ} {A : Set X} (h : Nagata n c A) (hA : A.Nonempty) :
    0 ≤ c := by
  obtain ⟨𝓑, -, hcov, hdiam, -⟩ := h 1 one_pos
  obtain ⟨a, ha⟩ := hA
  obtain ⟨B, hB, haB⟩ := hcov ha
  simpa using hdiam B hB a haB a haB

/-- Monotonicity of `Nagata(n, c)` in `n` and `c`. -/
theorem Nagata.mono {n n' : ℕ} {c c' : ℝ} {A : Set X} (h : Nagata n c A) (hn : n ≤ n')
    (hc : c ≤ c') : Nagata n' c' A := by
  intro s hs
  obtain ⟨𝓑, hsub, hcov, hdiam, hmult⟩ := h s hs
  refine ⟨𝓑, hsub, hcov, fun B hB x hx y hy ↦ ?_, fun E hE hEs ↦ ?_⟩
  · exact (hdiam B hB x hx y hy).trans (mul_le_mul_of_nonneg_right hc hs.le)
  · refine (hmult E hE hEs).trans ?_
    gcongr

/-- `Nagata(n, c)` is invariant under isometric embeddings. -/
theorem Nagata.image_isometry {Y : Type*} [PseudoMetricSpace Y] {n : ℕ} {c : ℝ} {A : Set X}
    (h : Nagata n c A) {ι : X → Y} (hι : Isometry ι) : Nagata n c (ι '' A) := by
  intro s hs
  obtain ⟨𝓑, hsub, hcov, hdiam, hmult⟩ := h s hs
  refine ⟨Set.image ι '' 𝓑, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨B, hB, rfl⟩
    exact Set.image_mono (hsub B hB)
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨B, hB, haB⟩ := hcov ha
    exact ⟨ι '' B, ⟨B, hB, rfl⟩, a, haB, rfl⟩
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hι.dist_eq]
    exact hdiam B hB x hx y hy
  · intro E hE hEs
    -- the test set `E ⊆ ι '' A` is the image of `E' = ι ⁻¹' E ∩ A`, of the same diameter
    set E' : Set X := ι ⁻¹' E ∩ A with hE'
    have himE' : ι '' E' = E := by
      apply Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hx.1
      · intro y hy
        obtain ⟨a, ha, rfl⟩ := hE hy
        exact ⟨a, ⟨hy, ha⟩, rfl⟩
    have hE's : Metric.ediam E' < ENNReal.ofReal s := by
      rw [← hι.ediam_image, himE']
      exact hEs
    have key := hmult E' inter_subset_right hE's
    -- every member `ι '' B` met by `E` comes from a member `B` met by `E'`
    refine le_trans (Set.encard_le_encard ?_) ((Set.encard_image_le (Set.image ι) _).trans key)
    rintro _ ⟨⟨B, hB, rfl⟩, y, hyB, hyE⟩
    obtain ⟨b, hb, rfl⟩ := hyB
    exact ⟨B, ⟨hB, b, hb, hyE, hsub B hB hb⟩, rfl⟩

end LipschitzExtension
