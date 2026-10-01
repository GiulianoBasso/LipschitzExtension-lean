/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Data.Set.Card
import Mathlib.Order.Bounds.Basic

/-!
# Whitney families

A *Whitney family* for a subset `A` of a metric space `Z` is a covering `(B i)` of
`{z | 0 < infDist z A}` (which is `Z \ closure A` when `A` is nonempty) by nonempty sets with
scales `r i = d(B i, A) > 0` satisfying the three conditions of Definition 6.2 of [Basso2024]:
*controlled diameter*, *bounded multiplicity* and *controlled distance to `A`*. Whitney families
are used in the proofs of Theorems 1.1, 1.2 and 6.1 of [Basso2024]. They are obtained from the
Nagata condition in Proposition 3.1 (`Nagata.exists_isWhitneyFamily`) and Proposition 8.4
(`Nagata.exists_isWhitneyFamily_refined`).

## Main definitions

* `IsWhitneyFamily A B r m α δ γ`: the sets `B i` form a Whitney family for `A` with scales `r i`,
  multiplicity at most `m` and constants `α`, `δ`, `γ`.

## Main statements

* `IsWhitneyFamily.one_sub_mul_le_infDist`: every point of the neighbourhood
  `N_{δ r i}(B i) = {z | infDist z (B i) < δ r i}` is at distance at least `(1 - δ) r i` from `A`.

## Implementation notes

We record the multiplicity bound as a natural number `m`: the condition `Whitney(n, α, δ, γ)` of
the paper corresponds to `m = n + 1`. The scale `r i` is characterized as the greatest lower bound
of `d(·, A)` on `B i`, and `A` need not be closed.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open Set Metric

namespace LipschitzExtension

variable {Z : Type*} [PseudoMetricSpace Z]

/-- `IsWhitneyFamily A B r m α δ γ` states that the sets `B i` form a Whitney family for `A`
(Definition 6.2 of [Basso2024]) with scales `r i = d(B i, A)`, multiplicity at most `m` and
constants `α`, `δ`, `γ`: the `B i` are nonempty and cover `{z | 0 < infDist z A}`,
`diam (B i) ≤ α r i`, every `z` with `0 < infDist z A` lies in the open neighbourhood
`N_{δ r i}(B i)` for at most `m` indices `i`, and `hd⁺(B i, A) ≤ γ r i`. The condition
`Whitney(n, α, δ, γ)` of the paper corresponds to `m = n + 1`. -/
structure IsWhitneyFamily {ι : Type*} (A : Set Z) (B : ι → Set Z) (r : ι → ℝ) (m : ℕ)
    (α δ γ : ℝ) : Prop where
  /-- Every member `B i` is nonempty. -/
  nonempty : ∀ i, (B i).Nonempty
  /-- The scales are positive. -/
  r_pos : ∀ i, 0 < r i
  /-- The scale `r i = d(B i, A)` is the infimum of `d(x, A)` over `x ∈ B i`. -/
  isGLB : ∀ i, IsGLB ((fun z ↦ infDist z A) '' B i) (r i)
  /-- The `B i` cover `{z | 0 < infDist z A}`. -/
  cover : ∀ z, 0 < infDist z A → ∃ i, z ∈ B i
  /-- Controlled diameter: `diam (B i) ≤ α r i`. -/
  diam_le : ∀ i, ∀ x ∈ B i, ∀ y ∈ B i, dist x y ≤ α * r i
  /-- Bounded multiplicity: every `z` with `0 < infDist z A` lies in the open neighbourhood
  `N_{δ r i}(B i) = {x | infDist x (B i) < δ r i}` for at most `m` indices `i`. -/
  mult_le : ∀ z, 0 < infDist z A → {i | infDist z (B i) < δ * r i}.encard ≤ m
  /-- Controlled distance to `A`: `hd⁺(B i, A) = sup_{x ∈ B i} d(x, A) ≤ γ r i`. -/
  hd_le : ∀ i, ∀ x ∈ B i, infDist x A ≤ γ * r i

namespace IsWhitneyFamily

variable {ι : Type*} {A : Set Z} {B : ι → Set Z} {r : ι → ℝ} {m : ℕ} {α δ γ : ℝ}

/-- The scale `r i` is at most the distance to `A` of every point of `B i`. -/
theorem r_le_infDist (hW : IsWhitneyFamily A B r m α δ γ) {i : ι} {x : Z} (hx : x ∈ B i) :
    r i ≤ infDist x A :=
  (hW.isGLB i).1 ⟨x, hx, rfl⟩

/-- For every `η > 0`, some point of `B i` is at distance less than `r i + η` from `A`. -/
theorem exists_infDist_lt (hW : IsWhitneyFamily A B r m α δ γ) (i : ι) {η : ℝ} (hη : 0 < η) :
    ∃ x ∈ B i, infDist x A < r i + η := by
  obtain ⟨_, ⟨x, hx, rfl⟩, -, hlt⟩ := (hW.isGLB i).exists_between (lt_add_of_pos_right _ hη)
  exact ⟨x, hx, hlt⟩

/-- If `infDist z (B i) < δ r i`, i.e. `z ∈ N_{δ r i}(B i)`, then `(1 - δ) r i ≤ infDist z A`. -/
theorem one_sub_mul_le_infDist (hW : IsWhitneyFamily A B r m α δ γ) {i : ι} {z : Z}
    (hz : infDist z (B i) < δ * r i) : (1 - δ) * r i ≤ infDist z A := by
  obtain ⟨y, hy, hzy⟩ := (infDist_lt_iff (hW.nonempty i)).1 hz
  have h1 := hW.r_le_infDist hy
  have h2 : infDist y A ≤ infDist z A + dist y z := infDist_le_infDist_add_dist
  rw [dist_comm] at h2
  nlinarith

end IsWhitneyFamily

end LipschitzExtension
