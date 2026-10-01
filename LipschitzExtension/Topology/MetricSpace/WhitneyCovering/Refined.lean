/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Nagata.Colored
import LipschitzExtension.Topology.MetricSpace.WhitneyCovering.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Refined Whitney coverings

This file proves Proposition 8.4 of [Basso2024]: let `A ⊆ X` be closed and satisfy
`Nagata(n - 1, c)` for some `n ≥ 1` and `c ≥ 0`. Then for every `ρ > 2 (c + 1) 4^(n+1)` there is a
covering `𝓑` of `X \ A` such that
1. every `B ∈ 𝓑` satisfies `diam B ≤ α d(B, A)`, where `α = 40 ρ³ (c + 1)(n + 1)`;
2. every `E ⊆ X \ A` with `diam E ≤ ρ^(1/(2n)) d(E, A)` meets at most `n + 1` members of `𝓑`;
3. every `B ∈ 𝓑` satisfies `hd⁺(B, A) ≤ ρ² d(B, A)`.

The paragraph after the proof in the paper deduces that `𝓑` is a Whitney family with
multiplicity `n + 1`, `α` as above, `δ = 1/(8ρ²)` and `γ = ρ²` (in the paper's notation:
`Whitney(n, α, δ, γ)`, Definition 6.2). Of Proposition 8.4, only this Whitney family is used in
the proof of Theorem 1.1. In the formalization its multiplicity bound is proved directly, not
deduced from property 2 (see the implementation notes).

In the formalization `A` is an arbitrary nonempty subset of a metric space `Z`, and `X \ A` is
replaced by `{z | 0 < d(z, A)}` (which is `Z \ A` for closed `A`). We write
`d(B, A) = inf_{b ∈ B} d(b, A)`, so that `diam B ≤ α d(B, A)` means `d(x, y) ≤ α d(b, A)` for all
`x, y, b ∈ B`, and similarly for 2. and 3.

## Main definitions

* `RefinedWhitney.Data`: the data of the construction (the scale `ρ`, its `n`-th root `t`, a
  choice of nearby points `p x` and colored coverings `𝓒 i` at the scales `4 ρ^(i+1)`).
* `RefinedWhitney.Data.ann`, `RefinedWhitney.Data.piece`, `RefinedWhitney.Data.star`: the annuli
  `R_k^i`, the pieces `p⁻¹(C) ∩ R_k^i` and the stars of the construction.
* `RefinedWhitney.Data.memb`: the members of the families `𝓑_k^i`.

## Main statements

* `RefinedWhitney.Data.isWhitneyFamily`: the members of all the `𝓑_k^i` form a Whitney family.
* `Nagata.exists_isWhitneyFamily_refined`: the Whitney family of Proposition 8.4 (the paragraph
  after its proof); this is the form used in the proof of Theorem 1.1.
* `Nagata.exists_refinedCover`: Proposition 8.4 with all three properties.

## Proof outline

We follow the proof of the paper. For `k ∈ {0, …, n-1}` and `i ∈ ℤ` let
`R_k^i = {x | ρ^(i-1) ρ^(k/n) ≤ d(x, A) < ρ^i ρ^(k/n)}` (real powers). For each `k`, `(R_k^i)_i`
partitions `{d(·,A) > 0}` and `R_k^i ⊆ R_0^i ∪ R_0^(i+1)`.

**Claim.** If families `𝓑_k^i` satisfy (a) members of `𝓑_k^i` lie in `R_k^i`, (b) `𝓑_k^i` has
`ρ^(i+1)`-multiplicity one, (c) `⋃ 𝓑_k^i` covers, then 2. holds. Indeed, with `t = ρ^(1/n)`
the annuli are `R_k^i = {x | t^(n(i-1)+k) ≤ d(x, A) < t^(ni+k)}`. Since `ρ > φ^(2n)` (`φ` the
golden ratio) we have `1 + ρ^(1/(2n)) < t`, so all `d(e, A)`, `e ∈ E`, lie in `[t^ℓ, t^(ℓ+2))`
for some `ℓ ∈ ℤ`. For every color `k` with `k ≢ ℓ + 1 (mod n)` the set `E` lies in a single
`R_k^i`, and since `diam E < ρ^(i+1)` it meets at most one member of color `k`; for the remaining
color it meets at most two members (one in each of two consecutive levels). Hence `E` meets at
most `(n - 1) + 2 = n + 1` members.

**Construction.** Choose `p : Z → A` with `d(x, p x) < ρ^i` on `R_0^i`, let `s_i = 4 ρ^(i+1)` and
`𝓐^i = 𝓐^i_0 ∪ ⋯ ∪ 𝓐^i_(n-1)` a colored cover of `A` at scale `s_i` (Lemma 8.3,
`Nagata.exists_colored_cover`: diameters `≤ c' s_i`, `c' = 2(c+1)(n+1)`, same-color members
`≥ s_i` apart). Pieces of `R_k^i`: `p⁻¹(C) ∩ R_k^i` for `C ∈ 𝓐_k^j`, `j ∈ {i, i+1}` ("order j").
Pieces of the same order are `≥ 2ρ^(j+1)` apart, so two pieces at distance `≤ ρ^(i+1)` have
different orders; combined with `ρ > 4(1 + c')` one shows that no piece of order `i` is within
`ρ^(i+1)` of two different pieces of order `i+1`. The members of `𝓑_k^i` are the equivalence
classes (unions) of pieces under "distance `≤ ρ^(i+1)`": concretely, the "stars" consisting of one
piece of order `i+1` together with all pieces of order `i` within `ρ^(i+1)` of it, and the
remaining pieces of order `i`. Then
`diam ≤ 2(2ρ^(i+1) + c' s_i) + 2ρ^(i+1) + (2ρ^(i+1) + c' s_(i+1))`,
`d(B, A) ≥ ρ^(i-1)`, so 1. holds, and 3. holds since `B ⊆ R_k^i`.

**Whitney property.** With `δ = 1/(8ρ²)`: if `z ∈ N_{δ r_i}(B_i)` for `i ∈ I(z)`, pick `x_i ∈ B_i`
with `d(z, x_i) < δ r_i`; then `r_i (1 - δ) ≤ (δ + ρ²) r_j`, and the (finite) set `E` of the `x_i`
satisfies `diam E ≤ 4δ(δ + ρ²) d(E, A) ≤ ρ^(1/(2n)) d(E, A)`, so `#I(z) ≤ n + 1`.

## Implementation notes

* We put `t = ρ^(1/n)`, so that `ρ^(i-1) ρ^(k/n) = t^(n(i-1)+k)`; only integer powers of `ρ` and
  `t` occur. The colors `k` are `Fin n` (`Nagata(n-1, c)` is used with `n = m + 1`), and the
  members of color `k` of the colored cover `𝓐^i` form the family `𝓒 i k`.
* The piece `RefinedWhitney.Data.piece k i C = p⁻¹(C) ∩ R_k^i` is indexed by the member `C` of the
  colored cover; its order (`i` or `i + 1`) is recorded by the hypothesis `C ∈ 𝓒 i k` or
  `C ∈ 𝓒 (i + 1) k`. The members of `𝓑_k^i` are defined directly as *stars*
  (`RefinedWhitney.Data.star`: a piece of order `i + 1` together with all pieces of order `i`
  linked to it, i.e. within `ρ^(i+1)`, see `RefinedWhitney.Linked`) and the pieces of order `i`
  linked to no piece of order `i + 1`.
* The Whitney family is indexed by triples `(k, i, M)` with `M` a nonempty member of `𝓑_k^i`
  (`RefinedWhitney.Data.Idx`), and `r (k, i, M) = inf_{x ∈ M} d(x, A)`.
* Multiplicity (`RefinedWhitney.Data.mult_bound`): if `d(z, B) < δ r_B` for a member
  `B ∈ 𝓑_k^i`, pick `e ∈ B` with `d(z, e) < δ r_B ≤ δ d(e, A)`; then
  `d(z, A)/(1+δ) < d(e, A) < d(z, A)/(1-δ)`, so all these `d(e, A)` lie in `(t^ℓ, t^(ℓ+2))` for
  one `ℓ ∈ ℤ` (as `(1+δ)/(1-δ) ≤ 2 ≤ t`), which forces `n i + k ∈ [ℓ + 1, ℓ + n + 1]`; and two
  such members with the same `(k, i)` coincide since their points `e` are at distance
  `≤ ρ^(i+1)`. This replaces the golden-ratio argument of the paper.
* `Nagata.exists_refinedCover` uses the same covering as `Nagata.exists_isWhitneyFamily_refined`:
  the index type is `RefinedWhitney.Data.Idx` and `B (k, i, M) = M`. Properties 1. and 3. and the
  covering properties follow from `RefinedWhitney.Data.isWhitneyFamily`, since
  `r (k, i, M) ≤ d(b, A)` for `b ∈ M`.
* Property 2. is proved with `u = ρ^(1/(2n))`, so that `u² = t` and `u ≥ 2`: let
  `a = inf_{e ∈ E} d(e, A)`; then `a ≤ d(e, A) ≤ (1 + u) a` for `e ∈ E`, and with
  `t^ℓ < a ≤ t^(ℓ+1)` all `d(e, A)` lie in `(t^ℓ, t^(ℓ+2))` since `1 + u < u² = t`. As in
  `RefinedWhitney.Data.mult_bound`, the map `(k, i, M) ↦ n i + k` sends the indices of the members
  meeting `E` to `[ℓ + 1, ℓ + n + 1]`, and it is injective on them: two members of the same
  `𝓑_k^i` meeting `E` in `e`, `e'` coincide, since `d(e, e') ≤ u d(e, A) < t ρ^i t^k ≤ ρ^(i+1)`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open Set Metric

namespace LipschitzExtension

universe u

namespace RefinedWhitney

variable {Z : Type u} [MetricSpace Z]

/-- Two sets are *linked at scale `s`* if they contain points at distance at most `s`. -/
def Linked (s : ℝ) (P Q : Set Z) : Prop := ∃ x ∈ P, ∃ y ∈ Q, dist x y ≤ s

/-- The data of the construction in the proof of Proposition 8.4 of [Basso2024], with colors
`k : Fin n`: a scale `ρ > 4 (1 + c')` with an `n`-th root `t ≥ 2`, a choice of nearby points `p x`
and, for every level `i : ℤ`, a colored covering `𝓒 i` at scale `4 ρ^(i+1)` (as in Lemma 8.3)
whose members have diameter at most `c' (4 ρ^(i+1))` and whose distinct members of the same color
are at distance at least `4 ρ^(i+1)`. -/
structure Data (A : Set Z) (n : ℕ) where
  /-- The scale parameter `ρ > 4 (1 + c')`. -/
  ρ : ℝ
  /-- The ratio `t = ρ^(1/n) ≥ 2` of consecutive annuli. -/
  t : ℝ
  /-- The diameter constant of the colored coverings `𝓒 i`. -/
  c' : ℝ
  /-- A choice of nearby points: `d(x, p x) < ρ^i` whenever `0 < d(x, A) < ρ^i`. -/
  p : Z → Z
  /-- `𝓒 i k` is the family of members of color `k` of a colored covering at scale
  `4 ρ^(i+1)`. -/
  𝓒 : ℤ → Fin n → Set (Set Z)
  /-- The diameter constant is nonnegative. -/
  c'_nonneg : 0 ≤ c'
  /-- The scale is large compared to the diameter constant: `ρ > 4 (1 + c')`. -/
  ρ_gt : 4 * (1 + c') < ρ
  /-- `t ≥ 2`. -/
  two_le_t : 2 ≤ t
  /-- `t` is an `n`-th root of `ρ`. -/
  t_pow : t ^ n = ρ
  /-- `d(x, p x) < ρ^i` whenever `0 < d(x, A) < ρ^i`. -/
  p_dist : ∀ x, 0 < infDist x A → ∀ i : ℤ, infDist x A < ρ ^ i → dist x (p x) < ρ ^ i
  /-- For every level `i`, each point `p x` lies in a member of the colored covering `𝓒 i`. -/
  p_cover : ∀ (i : ℤ) (x : Z), ∃ k, ∃ C ∈ 𝓒 i k, p x ∈ C
  /-- The members of `𝓒 i` have diameter at most `c' (4 ρ^(i+1))`. -/
  C_diam : ∀ i k, ∀ C ∈ 𝓒 i k, ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ c' * (4 * ρ ^ (i + 1))
  /-- Distinct members of `𝓒 i` of the same color are at distance at least `4 ρ^(i+1)`. -/
  C_sep : ∀ i k, ∀ C ∈ 𝓒 i k, ∀ C' ∈ 𝓒 i k, C ≠ C' → ∀ x ∈ C, ∀ y ∈ C',
    4 * ρ ^ (i + 1) ≤ dist x y

namespace Data

variable {A : Set Z} {n : ℕ} (D : Data A n)

theorem one_lt_ρ : 1 < D.ρ := by linarith [D.ρ_gt, D.c'_nonneg]

theorem ρ_pos : 0 < D.ρ := by linarith [D.one_lt_ρ]

theorem one_lt_t : 1 < D.t := by linarith [D.two_le_t]

theorem t_pos : 0 < D.t := by linarith [D.two_le_t]

theorem ρzpow_pos (i : ℤ) : 0 < D.ρ ^ i := zpow_pos D.ρ_pos i

theorem one_le_t_pow (k : ℕ) : 1 ≤ D.t ^ k := one_le_pow₀ D.one_lt_t.le

theorem t_pow_le (k : Fin n) : D.t ^ (k : ℕ) ≤ D.ρ := by
  rw [← D.t_pow]
  exact pow_le_pow_right₀ D.one_lt_t.le k.isLt.le

theorem zpow_conv (i : ℤ) (k : ℕ) : D.ρ ^ i * D.t ^ k = D.t ^ ((n : ℤ) * i + k) := by
  rw [zpow_add₀ D.t_pos.ne', zpow_mul, zpow_natCast, zpow_natCast, D.t_pow]

theorem zpow_succ_succ (i : ℤ) : D.ρ ^ (i + 1 + 1) = D.ρ ^ (i + 1) * D.ρ :=
  zpow_add_one₀ D.ρ_pos.ne' _

theorem zpow_sub_add (i : ℤ) : D.ρ ^ (i + 1) = D.ρ ^ (i - 1) * D.ρ ^ 2 := by
  rw [← zpow_natCast, ← zpow_add₀ D.ρ_pos.ne']
  congr 1
  push_cast
  ring

/-! ### Annuli, pieces and stars -/

/-- The annulus `R_k^i = {x | ρ^(i-1) t^k ≤ d(x, A) < ρ^i t^k}` (with `t = ρ^(1/n)`). -/
def ann (k : Fin n) (i : ℤ) : Set Z :=
  {x | D.ρ ^ (i - 1) * D.t ^ (k : ℕ) ≤ infDist x A ∧ infDist x A < D.ρ ^ i * D.t ^ (k : ℕ)}

/-- Points of `R_k^i` are at distance at least `ρ^(i-1)` from `A`. -/
theorem ann_lower {k : Fin n} {i : ℤ} {x : Z} (hx : x ∈ D.ann k i) :
    D.ρ ^ (i - 1) ≤ infDist x A :=
  (le_mul_of_one_le_right (D.ρzpow_pos _).le (D.one_le_t_pow _)).trans hx.1

theorem ann_pos {k : Fin n} {i : ℤ} {x : Z} (hx : x ∈ D.ann k i) : 0 < infDist x A :=
  (D.ρzpow_pos _).trans_le (D.ann_lower hx)

/-- Points of `R_k^i` are at distance less than `ρ^(i+1)` from `A`. -/
theorem ann_upper {k : Fin n} {i : ℤ} {x : Z} (hx : x ∈ D.ann k i) :
    infDist x A < D.ρ ^ (i + 1) := by
  rw [zpow_add_one₀ D.ρ_pos.ne']
  exact hx.2.trans_le (mul_le_mul_of_nonneg_left (D.t_pow_le k) (D.ρzpow_pos _).le)

/-- Points `x` of `R_k^i` satisfy `d(x, p x) < ρ^(i+1)`. -/
theorem ann_p {k : Fin n} {i : ℤ} {x : Z} (hx : x ∈ D.ann k i) :
    dist x (D.p x) < D.ρ ^ (i + 1) :=
  D.p_dist x (D.ann_pos hx) (i + 1) (D.ann_upper hx)

/-- The piece `p⁻¹(C) ∩ R_k^i`; it has order `j` if `C ∈ 𝓒 j k` (in the construction `j = i` or
`j = i + 1`). -/
def piece (k : Fin n) (i : ℤ) (C : Set Z) : Set Z := D.p ⁻¹' C ∩ D.ann k i

/-- Points of two distinct pieces of the same order `j` in `R_k^i` are more than
`4 ρ^(j+1) - 2 ρ^(i+1)` apart. -/
theorem piece_sep {k : Fin n} {i j : ℤ} {C C' : Set Z} (hC : C ∈ D.𝓒 j k) (hC' : C' ∈ D.𝓒 j k)
    (hne : C ≠ C') {x y : Z} (hx : x ∈ D.piece k i C) (hy : y ∈ D.piece k i C') :
    4 * D.ρ ^ (j + 1) - 2 * D.ρ ^ (i + 1) < dist x y := by
  have h1 := D.C_sep j k C hC C' hC' hne _ hx.1 _ hy.1
  have h2 := D.ann_p hx.2
  have h3 := D.ann_p hy.2
  have h4 : dist (D.p x) (D.p y) ≤ dist (D.p x) x + dist x y + dist y (D.p y) :=
    dist_triangle4 _ _ _ _
  rw [dist_comm (D.p x) x] at h4
  linarith

/-- Any two points of a piece of order `j` in `R_k^i` are at distance less than
`2 ρ^(i+1) + c' (4 ρ^(j+1))`. -/
theorem piece_diam {k : Fin n} {i j : ℤ} {C : Set Z} (hC : C ∈ D.𝓒 j k) {x y : Z}
    (hx : x ∈ D.piece k i C) (hy : y ∈ D.piece k i C) :
    dist x y < 2 * D.ρ ^ (i + 1) + D.c' * (4 * D.ρ ^ (j + 1)) := by
  have h1 := D.C_diam j k C hC _ hx.1 _ hy.1
  have h2 := D.ann_p hx.2
  have h3 := D.ann_p hy.2
  have h4 : dist x y ≤ dist x (D.p x) + dist (D.p x) (D.p y) + dist (D.p y) y :=
    dist_triangle4 _ _ _ _
  rw [dist_comm (D.p y) y] at h4
  linarith

/-- Distinct pieces of order `i` are far apart. -/
theorem low_eq {k : Fin n} {i : ℤ} {C₁ C₂ : Set Z} (hC₁ : C₁ ∈ D.𝓒 i k) (hC₂ : C₂ ∈ D.𝓒 i k)
    {x y : Z} (hx : x ∈ D.piece k i C₁) (hy : y ∈ D.piece k i C₂)
    (hxy : dist x y ≤ D.ρ ^ (i + 1)) : C₁ = C₂ := by
  by_contra hne
  have h1 := D.piece_sep hC₁ hC₂ hne hx hy
  have h2 := D.ρzpow_pos (i + 1)
  linarith

/-- Distinct pieces of order `i + 1` are far apart. -/
theorem high_eq {k : Fin n} {i : ℤ} {C₁ C₂ : Set Z} (hC₁ : C₁ ∈ D.𝓒 (i + 1) k)
    (hC₂ : C₂ ∈ D.𝓒 (i + 1) k) {x y : Z} (hx : x ∈ D.piece k i C₁) (hy : y ∈ D.piece k i C₂)
    (hxy : dist x y ≤ D.ρ ^ (i + 1)) : C₁ = C₂ := by
  by_contra hne
  have h1 := D.piece_sep hC₁ hC₂ hne hx hy
  have h2 := D.ρzpow_pos (i + 1)
  rw [D.zpow_succ_succ] at h1
  have h3 := D.one_lt_ρ
  nlinarith

/-- The key fact: no piece of order `i` is linked to two different pieces of order `i + 1`. -/
theorem key {k : Fin n} {i : ℤ} {C C₁ C₂ : Set Z} (hC : C ∈ D.𝓒 i k) (hC₁ : C₁ ∈ D.𝓒 (i + 1) k)
    (hC₂ : C₂ ∈ D.𝓒 (i + 1) k) (h₁ : Linked (D.ρ ^ (i + 1)) (D.piece k i C) (D.piece k i C₁))
    (h₂ : Linked (D.ρ ^ (i + 1)) (D.piece k i C) (D.piece k i C₂)) : C₁ = C₂ := by
  by_contra hne
  obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁⟩ := h₁
  obtain ⟨x₂, hx₂, y₂, hy₂, hxy₂⟩ := h₂
  have h1 := D.piece_sep hC₁ hC₂ hne hy₁ hy₂
  have h2 := D.piece_diam hC hx₁ hx₂
  have h3 : dist y₁ y₂ ≤ dist y₁ x₁ + dist x₁ x₂ + dist x₂ y₂ := dist_triangle4 _ _ _ _
  rw [dist_comm y₁ x₁] at h3
  rw [D.zpow_succ_succ] at h1
  have h5 := D.ρ_gt
  have h6 := D.ρzpow_pos (i + 1)
  have h7 := D.c'_nonneg
  nlinarith

/-- The star of a piece of order `i + 1`: the piece together with all pieces of order `i` linked
to it. -/
def star (k : Fin n) (i : ℤ) (C' : Set Z) : Set Z :=
  D.piece k i C' ∪ ⋃ C ∈ {C | C ∈ D.𝓒 i k ∧ Linked (D.ρ ^ (i + 1)) (D.piece k i C)
    (D.piece k i C')}, D.piece k i C

theorem mem_star {k : Fin n} {i : ℤ} {C' : Set Z} {x : Z} :
    x ∈ D.star k i C' ↔ x ∈ D.piece k i C' ∨
      ∃ C ∈ D.𝓒 i k, Linked (D.ρ ^ (i + 1)) (D.piece k i C) (D.piece k i C') ∧
        x ∈ D.piece k i C := by
  simp only [star, mem_union, mem_iUnion, mem_ofPred_eq, exists_prop, and_assoc]

/-- The members of `𝓑_k^i`: the stars and the pieces of order `i` not linked to any piece of
order `i + 1`. -/
def memb (k : Fin n) (i : ℤ) : Set (Set Z) :=
  {M | (∃ C' ∈ D.𝓒 (i + 1) k, M = D.star k i C') ∨
    ∃ C ∈ D.𝓒 i k, (∀ C' ∈ D.𝓒 (i + 1) k,
      ¬ Linked (D.ρ ^ (i + 1)) (D.piece k i C) (D.piece k i C')) ∧ M = D.piece k i C}

theorem piece_subset (k : Fin n) (i : ℤ) (C : Set Z) : D.piece k i C ⊆ D.ann k i :=
  inter_subset_right

theorem star_subset (k : Fin n) (i : ℤ) (C' : Set Z) : D.star k i C' ⊆ D.ann k i := by
  intro x hx
  rcases D.mem_star.1 hx with hx | ⟨C, -, -, hx⟩
  · exact hx.2
  · exact hx.2

/-- The members of `𝓑_k^i` lie in `R_k^i`. -/
theorem memb_subset {k : Fin n} {i : ℤ} {M : Set Z} (hM : M ∈ D.memb k i) : M ⊆ D.ann k i := by
  rcases hM with ⟨C', -, rfl⟩ | ⟨C, -, -, rfl⟩
  · exact D.star_subset k i C'
  · exact D.piece_subset k i C

/-- Two stars containing points at distance `≤ ρ^(i+1)` coincide. -/
theorem star_star {k : Fin n} {i : ℤ} {C₁ C₂ : Set Z} (hC₁ : C₁ ∈ D.𝓒 (i + 1) k)
    (hC₂ : C₂ ∈ D.𝓒 (i + 1) k) {x y : Z} (hx : x ∈ D.star k i C₁) (hy : y ∈ D.star k i C₂)
    (hxy : dist x y ≤ D.ρ ^ (i + 1)) : C₁ = C₂ := by
  rcases D.mem_star.1 hx with hx | ⟨E₁, hE₁, hl₁, hx⟩ <;>
    rcases D.mem_star.1 hy with hy | ⟨E₂, hE₂, hl₂, hy⟩
  · exact D.high_eq hC₁ hC₂ hx hy hxy
  · exact (D.key hE₂ hC₂ hC₁ hl₂ ⟨y, hy, x, hx, by rw [dist_comm]; exact hxy⟩).symm
  · exact D.key hE₁ hC₁ hC₂ hl₁ ⟨x, hx, y, hy, hxy⟩
  · obtain rfl := D.low_eq hE₁ hE₂ hx hy hxy
    exact D.key hE₁ hC₁ hC₂ hl₁ hl₂

/-- A star and an unlinked piece of order `i` do not contain points at distance `≤ ρ^(i+1)`. -/
theorem star_single {k : Fin n} {i : ℤ} {C₁ C₂ : Set Z} (hC₁ : C₁ ∈ D.𝓒 (i + 1) k)
    (hC₂ : C₂ ∈ D.𝓒 i k)
    (hC₂l : ∀ C' ∈ D.𝓒 (i + 1) k, ¬ Linked (D.ρ ^ (i + 1)) (D.piece k i C₂) (D.piece k i C'))
    {x y : Z} (hx : x ∈ D.star k i C₁) (hy : y ∈ D.piece k i C₂)
    (hxy : dist x y ≤ D.ρ ^ (i + 1)) : False := by
  rcases D.mem_star.1 hx with hx | ⟨E₁, hE₁, hl₁, hx⟩
  · exact hC₂l C₁ hC₁ ⟨y, hy, x, hx, by rw [dist_comm]; exact hxy⟩
  · obtain rfl := D.low_eq hE₁ hC₂ hx hy hxy
    exact hC₂l C₁ hC₁ hl₁

/-- Distinct members of `𝓑_k^i` are more than `ρ^(i+1)` apart. -/
theorem memb_eq {k : Fin n} {i : ℤ} {M M' : Set Z} (hM : M ∈ D.memb k i) (hM' : M' ∈ D.memb k i)
    {x y : Z} (hx : x ∈ M) (hy : y ∈ M') (hxy : dist x y ≤ D.ρ ^ (i + 1)) : M = M' := by
  rcases hM with ⟨C₁, hC₁, rfl⟩ | ⟨C₁, hC₁, hC₁l, rfl⟩ <;>
    rcases hM' with ⟨C₂, hC₂, rfl⟩ | ⟨C₂, hC₂, hC₂l, rfl⟩
  · rw [D.star_star hC₁ hC₂ hx hy hxy]
  · exact (D.star_single hC₁ hC₂ hC₂l hx hy hxy).elim
  · exact (D.star_single hC₂ hC₁ hC₁l hy hx (by rw [dist_comm]; exact hxy)).elim
  · rw [D.low_eq hC₁ hC₂ hx hy hxy]

/-- Every point of a star is close to its piece of order `i + 1`. -/
theorem star_near {k : Fin n} {i : ℤ} {C' : Set Z} {x : Z} (hx : x ∈ D.star k i C') :
    ∃ w ∈ D.piece k i C', dist x w ≤ (3 + 4 * D.c') * D.ρ ^ (i + 1) := by
  rcases D.mem_star.1 hx with hx | ⟨C, hC, ⟨x₁, hx₁, y₁, hy₁, hxy₁⟩, hx⟩
  · refine ⟨x, hx, ?_⟩
    rw [dist_self]
    have := D.c'_nonneg
    have := D.ρzpow_pos (i + 1)
    positivity
  · refine ⟨y₁, hy₁, ?_⟩
    have h1 := D.piece_diam hC hx hx₁
    have h2 := dist_triangle x x₁ y₁
    linarith

/-- The members of `𝓑_k^i` have diameter at most `(8 + 8 c' + 4 c' ρ) ρ^(i+1)`. -/
theorem memb_diam {k : Fin n} {i : ℤ} {M : Set Z} (hM : M ∈ D.memb k i) {x y : Z} (hx : x ∈ M)
    (hy : y ∈ M) : dist x y ≤ (8 + 8 * D.c' + 4 * D.c' * D.ρ) * D.ρ ^ (i + 1) := by
  have hc := D.c'_nonneg
  have hs := D.ρzpow_pos (i + 1)
  have hρ := D.one_lt_ρ
  rcases hM with ⟨C', hC', rfl⟩ | ⟨C, hC, -, rfl⟩
  · obtain ⟨w, hw, hxw⟩ := D.star_near hx
    obtain ⟨w', hw', hyw'⟩ := D.star_near hy
    have h1 := D.piece_diam hC' hw hw'
    rw [D.zpow_succ_succ] at h1
    have h2 : dist x y ≤ dist x w + dist w w' + dist w' y := dist_triangle4 _ _ _ _
    rw [dist_comm w' y] at h2
    nlinarith
  · have h1 := D.piece_diam hC hx hy
    nlinarith [mul_nonneg hc hs.le, mul_nonneg (mul_nonneg hc (by linarith : (0:ℝ) ≤ D.ρ)) hs.le]

/-- The members of the `𝓑_k^i` cover `{z | 0 < d(z, A)}`. -/
theorem memb_cover {z : Z} (hz : 0 < infDist z A) : ∃ k i, ∃ M ∈ D.memb k i, z ∈ M := by
  classical
  obtain ⟨i, hi1, hi2⟩ := exists_mem_Ico_zpow hz D.one_lt_ρ
  obtain ⟨k, C, hC, hpC⟩ := D.p_cover (i + 1) z
  by_cases hk : D.ρ ^ i * D.t ^ (k : ℕ) ≤ infDist z A
  · -- `z ∈ R_k^(i+1)` and its piece has order `i + 1`
    have hz' : z ∈ D.ann k (i + 1) := by
      refine ⟨by rwa [add_sub_cancel_right], ?_⟩
      exact hi2.trans_le (le_mul_of_one_le_right (D.ρzpow_pos _).le (D.one_le_t_pow _))
    have hzp : z ∈ D.piece k (i + 1) C := ⟨hpC, hz'⟩
    by_cases hl : ∃ C' ∈ D.𝓒 (i + 1 + 1) k,
        Linked (D.ρ ^ (i + 1 + 1)) (D.piece k (i + 1) C) (D.piece k (i + 1) C')
    · obtain ⟨C', hC', hl⟩ := hl
      exact ⟨k, i + 1, _, Or.inl ⟨C', hC', rfl⟩, D.mem_star.2 (Or.inr ⟨C, hC, hl, hzp⟩)⟩
    · push Not at hl
      exact ⟨k, i + 1, _, Or.inr ⟨C, hC, hl, rfl⟩, hzp⟩
  · -- `z ∈ R_k^i` and its piece has order `i + 1`
    push Not at hk
    have hz' : z ∈ D.ann k i := by
      refine ⟨?_, hk⟩
      calc D.ρ ^ (i - 1) * D.t ^ (k : ℕ) ≤ D.ρ ^ (i - 1) * D.ρ :=
            mul_le_mul_of_nonneg_left (D.t_pow_le k) (D.ρzpow_pos _).le
        _ = D.ρ ^ i := by rw [← zpow_add_one₀ D.ρ_pos.ne', sub_add_cancel]
        _ ≤ infDist z A := hi1
    exact ⟨k, i, _, Or.inl ⟨C, hC, rfl⟩, D.mem_star.2 (Or.inl ⟨hpC, hz'⟩)⟩

/-! ### The Whitney family -/

/-- In `R_k^i`, the index `n i + k` is determined up to `n + 1` values by the level of `d(x, A)`:
if `x ∈ R_k^i` and `t^ℓ < d(x, A) < t^(ℓ+2)`, then `ℓ + 1 ≤ n i + k ≤ ℓ + n + 1`. -/
theorem level_bounds {k : Fin n} {i : ℤ} {x : Z} (hx : x ∈ D.ann k i) {ℓ : ℤ}
    (h1 : D.t ^ ℓ < infDist x A) (h2 : infDist x A < D.t ^ (ℓ + 2)) :
    ℓ + 1 ≤ (n : ℤ) * i + (k : ℕ) ∧ (n : ℤ) * i + (k : ℕ) ≤ ℓ + n + 1 := by
  have hlo := hx.1
  have hhi := hx.2
  rw [D.zpow_conv] at hlo hhi
  have e1 := (zpow_lt_zpow_iff_right₀ D.one_lt_t).1 (h1.trans hhi)
  have e2 := (zpow_lt_zpow_iff_right₀ D.one_lt_t).1 (hlo.trans_lt h2)
  constructor
  · linarith
  · have : (n : ℤ) * (i - 1) = n * i - n := by ring
    linarith

omit [MetricSpace Z] in
/-- The map `(k, i) ↦ n i + k` is injective on `Fin n × ℤ`. -/
theorem idx_inj {k k' : Fin n} {i i' : ℤ}
    (h : (n : ℤ) * i + (k : ℕ) = (n : ℤ) * i' + (k' : ℕ)) : k = k' ∧ i = i' := by
  have hk : ((k : ℕ) : ℤ) < n := by exact_mod_cast k.isLt
  have hk' : ((k' : ℕ) : ℤ) < n := by exact_mod_cast k'.isLt
  have hk0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := by positivity
  have hk0' : (0 : ℤ) ≤ ((k' : ℕ) : ℤ) := by positivity
  have hii : i = i' := by
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · exfalso
      have : (n : ℤ) * (i + 1) ≤ (n : ℤ) * i' :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      linarith
    · exact heq
    · exfalso
      have : (n : ℤ) * (i' + 1) ≤ (n : ℤ) * i :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      linarith
  subst hii
  refine ⟨Fin.ext ?_, rfl⟩
  have : ((k : ℕ) : ℤ) = ((k' : ℕ) : ℤ) := by linarith
  exact_mod_cast this

omit [MetricSpace Z] in
/-- The integer interval `[ℓ + 1, ℓ + n + 1]` has `n + 1` elements. -/
theorem encard_Icc_int (ℓ : ℤ) (n : ℕ) :
    (Icc (ℓ + 1) (ℓ + n + 1) : Set ℤ).encard = (n + 1 : ℕ) := by
  rw [← Finset.coe_Icc, encard_coe_eq_coe_finsetCard, Int.card_Icc]
  congr 1
  have : ℓ + (n : ℤ) + 1 + 1 - (ℓ + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

/-- `inf_{x ∈ M} d(x, A) ≤ d(y, A)` for `y ∈ M`. -/
theorem sInf_le_of_mem {M : Set Z} {y : Z} (hy : y ∈ M) :
    sInf ((fun z ↦ infDist z A) '' M) ≤ infDist y A :=
  csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact infDist_nonneg⟩ ⟨y, hy, rfl⟩

/-- A nonempty member `M` of `𝓑_k^i` satisfies `ρ^(i-1) ≤ inf_{x ∈ M} d(x, A)`. -/
theorem le_sInf_of_memb {k : Fin n} {i : ℤ} {M : Set Z} (hM : M ∈ D.memb k i)
    (hne : M.Nonempty) : D.ρ ^ (i - 1) ≤ sInf ((fun z ↦ infDist z A) '' M) :=
  le_csInf (hne.image _) (by rintro _ ⟨w, hw, rfl⟩; exact D.ann_lower (D.memb_subset hM hw))

/-- The index type of the Whitney family: triples `(k, i, M)` with `M` a nonempty member of
`𝓑_k^i`. -/
abbrev Idx := {x : Fin n × ℤ × Set Z // x.2.2 ∈ D.memb x.1 x.2.1 ∧ x.2.2.Nonempty}

/-- The multiplicity bound of the Whitney family: with `δ = 1/(8ρ²)` and
`r (k, i, M) = inf_{x ∈ M} d(x, A)`, a point `z` with `0 < d(z, A)` lies in the neighbourhood
`N_{δ r}(M) = {x | d(x, M) < δ r}` of at most `n + 1` members `M` of the families `𝓑_k^i`. -/
theorem mult_bound {z : Z} (hz : 0 < infDist z A) :
    {x : D.Idx | infDist z x.1.2.2 <
      1 / (8 * D.ρ ^ 2) * sInf ((fun w ↦ infDist w A) '' x.1.2.2)}.encard ≤ (n + 1 : ℕ) := by
  set δ : ℝ := 1 / (8 * D.ρ ^ 2) with hδ
  have hρ := D.one_lt_ρ
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 / 8 := by
    rw [hδ]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  set a : ℝ := infDist z A / (1 + δ) with ha
  have hapos : 0 < a := by positivity
  have ha' : a * (1 + δ) = infDist z A := by rw [ha]; field_simp
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := exists_mem_Ico_zpow hapos D.one_lt_t
  -- every index in the set gives a point `e` of its member close to `z`
  have hpt : ∀ x : D.Idx, infDist z x.1.2.2 < δ * sInf ((fun w ↦ infDist w A) '' x.1.2.2) →
      ∃ e ∈ x.1.2.2, dist z e < δ * infDist e A ∧ D.t ^ ℓ < infDist e A ∧
        infDist e A < D.t ^ (ℓ + 2) := by
    intro x hx
    obtain ⟨e, he, hze⟩ := (infDist_lt_iff x.2.2).1 hx
    have h1 := sInf_le_of_mem (A := A) he
    have hze' : dist z e < δ * infDist e A :=
      hze.trans_le (mul_le_mul_of_nonneg_left h1 hδpos.le)
    refine ⟨e, he, hze', ?_, ?_⟩
    · have h2 : infDist z A ≤ infDist e A + dist z e := infDist_le_infDist_add_dist
      have : a < infDist e A := by nlinarith
      exact hℓ1.trans_lt this
    · have h2 : infDist e A ≤ infDist z A + dist e z := infDist_le_infDist_add_dist
      rw [dist_comm] at h2
      have ht := D.two_le_t
      have h3 : D.t ^ (ℓ + 2) = D.t ^ (ℓ + 1) * D.t := by
        rw [← zpow_add_one₀ D.t_pos.ne']; ring_nf
      rw [h3]
      have h4 : 0 ≤ infDist e A := infDist_nonneg
      nlinarith
  let f : D.Idx → ℤ := fun x ↦ (n : ℤ) * x.1.2.1 + (x.1.1 : ℕ)
  have hmaps : MapsTo f {x : D.Idx | infDist z x.1.2.2 <
      δ * sInf ((fun w ↦ infDist w A) '' x.1.2.2)} (Icc (ℓ + 1) (ℓ + n + 1)) := by
    intro x hx
    obtain ⟨e, he, -, he1, he2⟩ := hpt x hx
    exact D.level_bounds (D.memb_subset x.2.1 he) he1 he2
  have hinj : InjOn f {x : D.Idx | infDist z x.1.2.2 <
      δ * sInf ((fun w ↦ infDist w A) '' x.1.2.2)} := by
    intro x hx x' hx' hxx'
    obtain ⟨e, he, hze, -, -⟩ := hpt x hx
    obtain ⟨e', he', hze', -, -⟩ := hpt x' hx'
    obtain ⟨⟨k, i, M⟩, hM, hne⟩ := x
    obtain ⟨⟨k', i', M'⟩, hM', hne'⟩ := x'
    obtain ⟨rfl, rfl⟩ := idx_inj hxx'
    have h1 := D.ann_upper (D.memb_subset hM he)
    have h2 := D.ann_upper (D.memb_subset hM' he')
    have h3 : dist e e' ≤ dist e z + dist z e' := dist_triangle _ _ _
    rw [dist_comm e z] at h3
    have h4 := D.ρzpow_pos (i + 1)
    have h5 : dist e e' ≤ D.ρ ^ (i + 1) := by nlinarith
    obtain rfl := D.memb_eq hM hM' he he' h5
    rfl
  calc _ ≤ (Icc (ℓ + 1) (ℓ + n + 1) : Set ℤ).encard := encard_le_encard_of_injOn hmaps hinj
    _ = (n + 1 : ℕ) := encard_Icc_int ℓ n

/-- The members of all the `𝓑_k^i` form a Whitney family (indexed by `Idx`, with
`r (k, i, M) = inf_{x ∈ M} d(x, A)`) with multiplicity `n + 1`, `δ = 1/(8ρ²)`, `γ = ρ²` and every
`α ≥ (8 + 8 c' + 4 c' ρ) ρ²`. -/
theorem isWhitneyFamily {α : ℝ} (hα : (8 + 8 * D.c' + 4 * D.c' * D.ρ) * D.ρ ^ 2 ≤ α) :
    IsWhitneyFamily A (fun x : D.Idx ↦ x.1.2.2)
      (fun x ↦ sInf ((fun z ↦ infDist z A) '' x.1.2.2)) (n + 1) α (1 / (8 * D.ρ ^ 2))
      (D.ρ ^ 2) where
  nonempty x := x.2.2
  r_pos x := (D.ρzpow_pos _).trans_le (D.le_sInf_of_memb x.2.1 x.2.2)
  isGLB x := isGLB_csInf (x.2.2.image _) ⟨0, by rintro _ ⟨w, -, rfl⟩; exact infDist_nonneg⟩
  cover z hz := by
    obtain ⟨k, i, M, hM, hzM⟩ := D.memb_cover hz
    exact ⟨⟨(k, i, M), hM, z, hzM⟩, hzM⟩
  diam_le x y hy y' hy' := by
    obtain ⟨⟨k, i, M⟩, hM, hne⟩ := x
    have h1 := D.memb_diam hM hy hy'
    have h2 := D.le_sInf_of_memb hM hne
    rw [D.zpow_sub_add] at h1
    have h3 := D.ρzpow_pos (i - 1)
    have h4 : 0 ≤ α := le_trans (by have := D.c'_nonneg; have := D.ρ_pos; positivity) hα
    calc dist y y' ≤ (8 + 8 * D.c' + 4 * D.c' * D.ρ) * (D.ρ ^ (i - 1) * D.ρ ^ 2) := h1
      _ = (8 + 8 * D.c' + 4 * D.c' * D.ρ) * D.ρ ^ 2 * D.ρ ^ (i - 1) := by ring
      _ ≤ α * D.ρ ^ (i - 1) := mul_le_mul_of_nonneg_right hα h3.le
      _ ≤ α * _ := mul_le_mul_of_nonneg_left h2 h4
  mult_le z hz := D.mult_bound hz
  hd_le x y hy := by
    obtain ⟨⟨k, i, M⟩, hM, hne⟩ := x
    have h1 := D.ann_upper (D.memb_subset hM hy)
    have h2 := D.le_sInf_of_memb hM hne
    rw [D.zpow_sub_add] at h1
    calc infDist y A ≤ D.ρ ^ (i - 1) * D.ρ ^ 2 := h1.le
      _ = D.ρ ^ 2 * D.ρ ^ (i - 1) := by ring
      _ ≤ D.ρ ^ 2 * _ := mul_le_mul_of_nonneg_left h2 (by positivity)

end Data

end RefinedWhitney

/-! ### Proposition 8.4

We construct the `RefinedWhitney.Data` from the Nagata condition and deduce both forms of
Proposition 8.4: the Whitney family (`Nagata.exists_isWhitneyFamily_refined`) and the covering with
all three properties of the paper (`Nagata.exists_refinedCover`). Property 2. is proved with the
argument of `RefinedWhitney.Data.mult_bound`, see the implementation notes of the module docstring.
-/

/-- Property 2. of Proposition 8.4 for the members of the `𝓑_k^i` of a `RefinedWhitney.Data`,
with `u = √t`: every set `E ⊆ {z | 0 < d(z, A)}` with `diam E ≤ u d(E, A)` meets at most `n + 1`
of them. -/
private theorem encard_meet_le {Z : Type u} [MetricSpace Z] {A : Set Z} {n : ℕ}
    (D : RefinedWhitney.Data A n) {u : ℝ} (hu : 2 ≤ u) (hut : u * u = D.t) {E : Set Z}
    (hE : ∀ e ∈ E, 0 < infDist e A)
    (hEd : ∀ x ∈ E, ∀ y ∈ E, ∀ e ∈ E, dist x y ≤ u * infDist e A) :
    {x : D.Idx | (x.1.2.2 ∩ E).Nonempty}.encard ≤ (n + 1 : ℕ) := by
  rcases E.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · simp
  -- the infimum `a` of `d(e, A)` over `e ∈ E`
  set a : ℝ := sInf ((fun e ↦ infDist e A) '' E) with ha
  have hbdd : BddBelow ((fun e ↦ infDist e A) '' E) :=
    ⟨0, by rintro _ ⟨w, -, rfl⟩; exact infDist_nonneg⟩
  have ha_le : ∀ e ∈ E, a ≤ infDist e A := fun e he ↦ csInf_le hbdd ⟨e, he, rfl⟩
  have hle_a : ∀ e ∈ E, infDist e A ≤ (1 + u) * a := by
    intro e he
    have : infDist e A / (1 + u) ≤ a := by
      rw [ha]
      refine le_csInf ((nonempty_of_mem he₀).image _) ?_
      rintro _ ⟨e', he', rfl⟩
      rw [div_le_iff₀ (by linarith)]
      have h1 : infDist e A ≤ infDist e' A + dist e e' := infDist_le_infDist_add_dist
      have h2 := hEd e he e' he' e' he'
      linarith
    rwa [div_le_iff₀ (by linarith), mul_comm] at this
  have hapos : 0 < a := by
    have h1 := hle_a e₀ he₀
    have h2 := hE e₀ he₀
    nlinarith
  -- all `d(e, A)`, `e ∈ E`, lie in `(t^ℓ, t^(ℓ+2))`
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := exists_mem_Ioc_zpow hapos D.one_lt_t
  have hlev : ∀ e ∈ E, D.t ^ ℓ < infDist e A ∧ infDist e A < D.t ^ (ℓ + 2) := by
    intro e he
    refine ⟨hℓ1.trans_le (ha_le e he), ?_⟩
    have h3 : D.t ^ (ℓ + 2) = D.t ^ (ℓ + 1) * D.t := by
      rw [← zpow_add_one₀ D.t_pos.ne']; ring_nf
    rw [h3]
    have h4 := hle_a e he
    have h5 : 1 + u < D.t := by nlinarith
    have h6 : 0 < D.t ^ (ℓ + 1) := zpow_pos D.t_pos _
    nlinarith
  let f : D.Idx → ℤ := fun x ↦ (n : ℤ) * x.1.2.1 + (x.1.1 : ℕ)
  have hmaps : MapsTo f {x : D.Idx | (x.1.2.2 ∩ E).Nonempty} (Icc (ℓ + 1) (ℓ + n + 1)) := by
    rintro x ⟨e, he, heE⟩
    exact D.level_bounds (D.memb_subset x.2.1 he) (hlev e heE).1 (hlev e heE).2
  have hinj : InjOn f {x : D.Idx | (x.1.2.2 ∩ E).Nonempty} := by
    rintro ⟨⟨k, i, M⟩, hM, hne⟩ ⟨e, he, heE⟩ ⟨⟨k', i', M'⟩, hM', hne'⟩ ⟨e', he', he'E⟩ hff
    obtain ⟨rfl, rfl⟩ := RefinedWhitney.Data.idx_inj hff
    have h1 := (D.memb_subset hM he).2
    have h2 := hEd e heE e' he'E e heE
    have ht1 : D.t * D.t ^ (k : ℕ) ≤ D.ρ := by
      rw [← pow_succ', ← D.t_pow]
      exact pow_le_pow_right₀ D.one_lt_t.le k.isLt
    have hut' : u ≤ D.t := by nlinarith
    have hd0 : 0 ≤ infDist e A := infDist_nonneg
    have hρi := D.ρzpow_pos i
    have h5 : dist e e' ≤ D.ρ ^ (i + 1) :=
      calc dist e e' ≤ u * infDist e A := h2
        _ ≤ D.t * (D.ρ ^ i * D.t ^ (k : ℕ)) := mul_le_mul hut' h1.le hd0 D.t_pos.le
        _ = D.ρ ^ i * (D.t * D.t ^ (k : ℕ)) := by ring
        _ ≤ D.ρ ^ i * D.ρ := mul_le_mul_of_nonneg_left ht1 hρi.le
        _ = D.ρ ^ (i + 1) := (zpow_add_one₀ D.ρ_pos.ne' i).symm
    obtain rfl := D.memb_eq hM hM' he he' h5
    rfl
  calc _ ≤ (Icc (ℓ + 1) (ℓ + n + 1) : Set ℤ).encard := encard_le_encard_of_injOn hmaps hinj
    _ = (n + 1 : ℕ) := RefinedWhitney.Data.encard_Icc_int ℓ n

/-- The data of the construction for a nonempty set satisfying `Nagata(m, c)` (so `n = m + 1`),
built from the colored coverings of Lemma 8.3 (`Nagata.exists_colored_cover`), together with the
estimate `(8 + 8 c' + 4 c' ρ) ρ² ≤ 40 ρ³ (c + 1)(n + 1)` for the diameter constant. -/
private theorem exists_data {Z : Type u} [MetricSpace Z] {A : Set Z} (hA : A.Nonempty)
    {m : ℕ} {c : ℝ} (hN : Nagata m c A) {ρ : ℝ} (hρ : 2 * (c + 1) * 4 ^ (m + 1 + 1) < ρ) :
    ∃ D : RefinedWhitney.Data A (m + 1), D.ρ = ρ ∧ D.t = ρ ^ (((m + 1 : ℕ) : ℝ)⁻¹) ∧
      (8 + 8 * D.c' + 4 * D.c' * D.ρ) * D.ρ ^ 2 ≤
        40 * ρ ^ 3 * (c + 1) * (((m + 1 : ℕ) : ℝ) + 1) := by
  classical
  have hc : 0 ≤ c := hN.nonneg hA
  -- numerical facts
  have h4 : (1 : ℝ) + ((m + 1 : ℕ) : ℝ) * 3 ≤ 4 ^ (m + 1) := by
    have := one_add_mul_le_pow (a := (3 : ℝ)) (by norm_num) (m + 1)
    norm_num at this ⊢
    linarith
  have h4' : (4 : ℝ) ^ (m + 1 + 1) = 4 * 4 ^ (m + 1) := by ring
  rw [h4'] at hρ
  push_cast at h4
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set c' : ℝ := 2 * (c + 1) * ((m : ℝ) + 2) with hc'
  have hρc' : 4 * (1 + c') < ρ := by
    rw [hc']
    nlinarith [mul_nonneg hc hm]
  have hρ1 : 1 < ρ := by nlinarith [mul_nonneg hc hm]
  have hρ0 : 0 < ρ := by linarith
  -- the `n`-th root `t` of `ρ`
  set t : ℝ := ρ ^ (((m + 1 : ℕ) : ℝ)⁻¹) with ht
  have ht_pow : t ^ (m + 1) = ρ := Real.rpow_inv_natCast_pow hρ0.le (by omega)
  have ht2 : 2 ≤ t := by
    have ht0 : 0 ≤ t := Real.rpow_nonneg hρ0.le _
    rw [← pow_le_pow_iff_left₀ (by norm_num) ht0 (by omega : m + 1 ≠ 0), ht_pow]
    have h2 : (2 : ℝ) ^ (m + 1) ≤ 4 ^ (m + 1) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h5 : (0 : ℝ) < 4 ^ (m + 1) := by positivity
    nlinarith
  -- the retraction `p`
  have hp : ∀ x : Z, ∃ a ∈ A, 0 < infDist x A → ∀ i : ℤ, infDist x A < ρ ^ i →
      dist x a < ρ ^ i := by
    intro x
    by_cases hx : 0 < infDist x A
    · obtain ⟨i₀, hi₀1, hi₀2⟩ := exists_mem_Ico_zpow hx hρ1
      obtain ⟨a, ha, hxa⟩ := (infDist_lt_iff hA).1 hi₀2
      refine ⟨a, ha, fun _ i hi ↦ hxa.trans_le ?_⟩
      apply zpow_le_zpow_right₀ hρ1.le
      have := (zpow_lt_zpow_iff_right₀ hρ1).1 (hi₀1.trans_lt hi)
      omega
    · obtain ⟨a, ha⟩ := hA
      exact ⟨a, ha, fun h ↦ absurd h hx⟩
  choose p hpA hpd using hp
  -- the colored coverings `𝓐^i` at scales `s_i = 4 ρ^(i+1)`
  have hcol := fun i : ℤ ↦ hN.exists_colored_cover (s := 4 * ρ ^ (i + 1)) (by positivity)
  choose 𝓒 h𝓒sub h𝓒cov h𝓒diam h𝓒sep using hcol
  let D : RefinedWhitney.Data A (m + 1) :=
    { ρ := ρ
      t := t
      c' := c'
      p := p
      𝓒 := 𝓒
      c'_nonneg := by positivity
      ρ_gt := hρc'
      two_le_t := ht2
      t_pow := ht_pow
      p_dist := hpd
      p_cover := fun i x ↦ by
        have := h𝓒cov i (hpA x)
        rw [mem_iUnion] at this
        obtain ⟨k, hk⟩ := this
        rw [mem_sUnion] at hk
        obtain ⟨C, hC, hxC⟩ := hk
        exact ⟨k, C, hC, hxC⟩
      C_diam := fun i k C hC x hx y hy ↦ h𝓒diam i k C hC x hx y hy
      C_sep := h𝓒sep }
  refine ⟨D, rfl, rfl, ?_⟩
  change (8 + 8 * c' + 4 * c' * ρ) * ρ ^ 2 ≤ 40 * ρ ^ 3 * (c + 1) * (((m + 1 : ℕ) : ℝ) + 1)
  push_cast
  rw [hc']
  have hY : 1 ≤ (c + 1) * ((m : ℝ) + 2) := by nlinarith
  have hρ2 : 0 < ρ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hρ1.le
    (mul_nonneg hρ2.le (by linarith : (0:ℝ) ≤ (c + 1) * ((m : ℝ) + 2)))]

/-- **Proposition 8.4** of [Basso2024], Whitney-family form (the paragraph after its proof): if
`A` is nonempty and satisfies `Nagata(n - 1, c)` with `n ≥ 1` and `ρ > 2 (c + 1) 4^(n+1)`, then
`{z | 0 < d(z, A)}` admits a covering satisfying `Whitney(n, 40 ρ³ (c+1)(n+1), 1/(8ρ²), ρ²)`, i.e.
a Whitney family with multiplicity `n + 1`. This is the form used in the proof of Theorem 1.1. -/
theorem Nagata.exists_isWhitneyFamily_refined {Z : Type u} [MetricSpace Z] {A : Set Z}
    (hA : A.Nonempty) {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hN : Nagata (n - 1) c A) {ρ : ℝ}
    (hρ : 2 * (c + 1) * 4 ^ (n + 1) < ρ) :
    ∃ (ι : Type u) (B : ι → Set Z) (r : ι → ℝ),
      IsWhitneyFamily A B r (n + 1) (40 * ρ ^ 3 * (c + 1) * (n + 1)) (1 / (8 * ρ ^ 2)) (ρ ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hN
  obtain ⟨D, hDρ, -, hα⟩ := exists_data hA hN hρ
  subst hDρ
  exact ⟨_, _, _, D.isWhitneyFamily hα⟩

/-- **Proposition 8.4** of [Basso2024] with all three properties: if `A` is nonempty and satisfies
`Nagata(n - 1, c)` with `n ≥ 1` and `ρ > 2 (c + 1) 4^(n+1)`, then there is a covering of
`{z | 0 < d(z, A)}` by nonempty subsets `B i` of `{z | 0 < d(z, A)}` such that
1. `diam B i ≤ 40 ρ³ (c + 1)(n + 1) d(B i, A)`,
2. every `E ⊆ {z | 0 < d(z, A)}` with `diam E ≤ ρ^(1/(2n)) d(E, A)` meets at most `n + 1` of the
   `B i`,
3. `hd⁺(B i, A) ≤ ρ² d(B i, A)`.

Here `diam B ≤ α d(B, A)` is stated as `d(x, y) ≤ α d(b, A)` for all `x, y, b ∈ B`, and similarly
for 2. and 3. -/
theorem Nagata.exists_refinedCover {Z : Type u} [MetricSpace Z] {A : Set Z} (hA : A.Nonempty)
    {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hN : Nagata (n - 1) c A) {ρ : ℝ}
    (hρ : 2 * (c + 1) * 4 ^ (n + 1) < ρ) :
    ∃ (ι : Type u) (B : ι → Set Z),
      (∀ i, (B i).Nonempty) ∧
      (∀ i, ∀ x ∈ B i, 0 < infDist x A) ∧
      (∀ z, 0 < infDist z A → ∃ i, z ∈ B i) ∧
      (∀ i, ∀ x ∈ B i, ∀ y ∈ B i, ∀ b ∈ B i,
        dist x y ≤ 40 * ρ ^ 3 * (c + 1) * (n + 1) * infDist b A) ∧
      (∀ E : Set Z, (∀ e ∈ E, 0 < infDist e A) →
        (∀ x ∈ E, ∀ y ∈ E, ∀ e ∈ E, dist x y ≤ ρ ^ (1 / (2 * (n : ℝ))) * infDist e A) →
          {i | (B i ∩ E).Nonempty}.encard ≤ n + 1) ∧
      (∀ i, ∀ x ∈ B i, ∀ b ∈ B i, infDist x A ≤ ρ ^ 2 * infDist b A) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hN
  have hc : 0 ≤ c := hN.nonneg hA
  obtain ⟨D, hDρ, hDt, hα⟩ := exists_data hA hN hρ
  subst hDρ
  have hW := D.isWhitneyFamily hα
  -- `u = ρ^(1/(2n))` is a square root of `t = ρ^(1/n)` and `u ≥ 2`
  have hN0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hut : D.ρ ^ (1 / (2 * ((m + 1 : ℕ) : ℝ))) * D.ρ ^ (1 / (2 * ((m + 1 : ℕ) : ℝ))) =
      D.t := by
    rw [hDt, ← Real.rpow_add D.ρ_pos]
    congr 1
    field_simp
    ring
  have ht4 : 4 ≤ D.t := by
    by_contra h
    have h1 : D.t ^ (m + 1) < 4 ^ (m + 1) := pow_lt_pow_left₀ (not_le.1 h) D.t_pos.le (by omega)
    rw [D.t_pow] at h1
    have h2 : (0 : ℝ) < 4 ^ (m + 1) := by positivity
    have h3 : (4 : ℝ) ^ (m + 1 + 1) = 4 ^ (m + 1) * 4 := pow_succ _ _
    nlinarith [mul_nonneg hc h2.le]
  have hu : 2 ≤ D.ρ ^ (1 / (2 * ((m + 1 : ℕ) : ℝ))) := by
    have h0 := Real.rpow_nonneg D.ρ_pos.le (1 / (2 * ((m + 1 : ℕ) : ℝ)))
    nlinarith
  have hα0 : 0 ≤ 40 * D.ρ ^ 3 * (c + 1) * (((m + 1 : ℕ) : ℝ) + 1) := by
    have := D.ρ_pos
    have : 0 ≤ c + 1 := by linarith
    positivity
  refine ⟨D.Idx, fun x ↦ x.1.2.2, hW.nonempty, fun x y hy ↦ D.ann_pos (D.memb_subset x.2.1 hy),
    hW.cover, ?_, ?_, ?_⟩
  · intro x y hy y' hy' b hb
    exact (hW.diam_le x y hy y' hy').trans
      (mul_le_mul_of_nonneg_left (hW.r_le_infDist hb) hα0)
  · intro E hE hEd
    refine (encard_meet_le D hu hut hE hEd).trans ?_
    push_cast
    rfl
  · intro x y hy b hb
    exact (hW.hd_le x y hy).trans (mul_le_mul_of_nonneg_left (hW.r_le_infDist hb) (by positivity))

end LipschitzExtension
