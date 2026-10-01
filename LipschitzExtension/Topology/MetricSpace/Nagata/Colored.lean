/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Nagata.Defs

/-!
# Colored coverings from the Nagata condition

This file proves Lemma 8.3 of [Basso2024], with the correction of item 10 of the errata
[BassoClaude2026]: if `A` satisfies `Nagata(n, c)`, then for every `s > 0` there is a covering
`𝓑 = 𝓑_1 ∪ ⋯ ∪ 𝓑_{n+1}` of `A` with `diam B ≤ 2(c + 1)(n + 2) s` for all `B ∈ 𝓑` and
`d(B, B') ≥ s` for distinct `B, B'` of the same color. The construction of the paper at scale `s`
gives `diam B ≤ 2(c + 1) s` and `d(B, B') ≥ s/(n + 2)`; as in the errata, we apply it at scale
`(n + 2) s`, which gives the lemma with `d(B, B') ≥ s` instead of `d(B, B') > s`. This suffices for
Proposition 8.4 of [Basso2024], in whose proof the lemma is used.

## Main statements

* `Nagata.exists_colored_cover`: Lemma 8.3 of [Basso2024], corrected as in errata item 10.

## Proof outline

This is the construction of the paper at scale `σ = (n + 2) s`, with the cells described
directly instead of via a cubical complex. Take a Nagata cover `(B_i)` at scale `2σ`
(`diam B_i ≤ 2cσ`, `2σ`-multiplicity `≤ n + 1`) and put `φ_i(x) = max(σ - d(x, B_i), 0) ∈ [0, σ]`
(`1`-Lipschitz). For each `x` at most `n + 1` of the `φ_i(x)` are positive. Let
`s_k = (1 - k/(n+2)) σ` (so `s_k - s_{k+1} = s`, `s_{n+2} = 0`). For a finite set `J` of indices
with `1 ≤ #J = k ≤ n + 1` put `B_J = {x ∈ A | φ_i(x) > s_k for i ∈ J, φ_i(x) ≤ s_{k+1} for i ∉ J}`,
of color `k`.

* Separation: if `#J = #J' = k` and `J ≠ J'`, pick `i ∈ J \ J'`; then
  `d(x, x') ≥ φ_i(x) - φ_i(x') > s_k - s_{k+1} = s` for `x ∈ B_J`, `x' ∈ B_J'`.
* Diameter: for `x, x' ∈ B_J` and `i ∈ J`, `d(x, B_i), d(x', B_i) < σ`, so
  `d(x, x') ≤ 2σ + diam B_i ≤ 2(c + 1)σ`.
* Covering: for `x ∈ A`, let `k` be maximal such that some `J` with `#J = k` has `φ_i(x) > s_k` for
  all `i ∈ J` (`k = 1` works since `x ∈ B_i` for some `i`, where `φ_i(x) = σ`); then `x ∈ B_J`.

## Implementation notes

The functions `φ_i` are eliminated: with `d_i(x) = Metric.infDist x B_i` we have `φ_i(x) > s_k`
iff `d_i(x) < k s`, and `φ_i(x) ≤ s_{k+1}` iff `d_i(x) ≥ (k + 1) s`; this is how the cells `B_J`
are defined. Empty members of the Nagata cover are discarded (for them `Metric.infDist` is `0`). The
multiplicity condition is used to show that at most `n + 1` nonempty members of the cover are
closer than `σ` to a given point. The colors are indexed by `Fin (n + 1)`: the color of `B_J` is
`#J - 1`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
-/

open Set Metric

namespace LipschitzExtension

variable {X : Type*} [PseudoMetricSpace X]

/-- The cell `B_J` of the colored covering: the points of `A` that are closer than `#J * s` to
every member of `J` and at distance at least `(#J + 1) * s` from every other member of `𝓑`. -/
private def coloredCell (A : Set X) (𝓑 : Set (Set X)) (s : ℝ) (J : Finset (Set X)) : Set X :=
  {x ∈ A | (∀ B ∈ J, infDist x B < J.card * s) ∧
    ∀ B ∈ 𝓑, B ∉ J → (J.card + 1) * s ≤ infDist x B}

/-- In a covering with `2σ`-multiplicity at most `n + 1`, at most `n + 1` nonempty members are
at distance `< σ` from a given point. -/
private theorem card_le_of_infDist_lt {n : ℕ} {A : Set X} {𝓑 : Set (Set X)} {σ : ℝ}
    (hσ : 0 < σ) (hsub : ∀ B ∈ 𝓑, B ⊆ A)
    (hmult : ∀ E ⊆ A, Metric.ediam E < ENNReal.ofReal (2 * σ) →
      {B ∈ 𝓑 | (B ∩ E).Nonempty}.encard ≤ n + 1)
    {x : X} {J : Finset (Set X)} (hJ : ↑J ⊆ 𝓑) (hne : ∀ B ∈ J, B.Nonempty)
    (hx : ∀ B ∈ J, infDist x B < σ) : J.card ≤ n + 1 := by
  have hchoose : ∀ B : Set X, ∃ b : X, B ∈ J → b ∈ B ∧ dist x b < σ := by
    intro B
    by_cases hB : B ∈ J
    · obtain ⟨b, hb, hxb⟩ := (infDist_lt_iff (hne B hB)).1 (hx B hB)
      exact ⟨b, fun _ ↦ ⟨hb, hxb⟩⟩
    · exact ⟨x, fun h ↦ absurd h hB⟩
  choose g hg using hchoose
  set E : Set X := g '' ↑J with hE
  have hEA : E ⊆ A := by
    rintro _ ⟨B, hB, rfl⟩
    exact hsub B (hJ hB) (hg B hB).1
  have hEdiam : Metric.ediam E < ENNReal.ofReal (2 * σ) := by
    apply ediam_lt_ofReal_of_finite (J.finite_toSet.image g) (by positivity)
    rintro _ ⟨B, hB, rfl⟩ _ ⟨B', hB', rfl⟩
    calc dist (g B) (g B') ≤ dist (g B) x + dist x (g B') := dist_triangle _ _ _
      _ < σ + σ := add_lt_add (by rw [dist_comm]; exact (hg B hB).2) (hg B' hB').2
      _ = 2 * σ := by ring
  have hJE : (↑J : Set (Set X)) ⊆ {B ∈ 𝓑 | (B ∩ E).Nonempty} := by
    intro B hB
    exact ⟨hJ hB, g B, (hg B hB).1, B, hB, rfl⟩
  have := (encard_le_encard hJE).trans (hmult E hEA hEdiam)
  rw [encard_coe_eq_coe_finsetCard] at this
  exact_mod_cast this

/-- **Lemma 8.3** of [Basso2024] (corrected as in errata item 10): if `A` satisfies
`Nagata(n, c)` and `s > 0`, then `A` is covered by the members of families `𝓒 k` of subsets of
`A`, indexed by the colors `k : Fin (n + 1)`, such that every member has diameter at most
`2 (c + 1) (n + 2) s` and distinct members of the same color are at distance at least `s`. -/
theorem Nagata.exists_colored_cover {n : ℕ} {c : ℝ} {A : Set X} (h : Nagata n c A) {s : ℝ}
    (hs : 0 < s) :
    ∃ 𝓒 : Fin (n + 1) → Set (Set X), (∀ k, ∀ C ∈ 𝓒 k, C ⊆ A) ∧ A ⊆ ⋃ k, ⋃₀ 𝓒 k ∧
      (∀ k, ∀ C ∈ 𝓒 k, ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ 2 * (c + 1) * (n + 2) * s) ∧
      ∀ k, ∀ C ∈ 𝓒 k, ∀ C' ∈ 𝓒 k, C ≠ C' → ∀ x ∈ C, ∀ y ∈ C', s ≤ dist x y := by
  classical
  set σ : ℝ := (n + 2) * s with hσ
  have hσpos : 0 < σ := by positivity
  obtain ⟨𝓑, hsub, hcov, hdiam, hmult⟩ := h (2 * σ) (by positivity)
  set 𝓑' : Set (Set X) := {B ∈ 𝓑 | B.Nonempty} with h𝓑'
  refine ⟨fun i ↦ {C | ∃ J : Finset (Set X), ↑J ⊆ 𝓑' ∧ J.card = i.val + 1 ∧
    C = coloredCell A 𝓑' s J}, ?_, ?_, ?_, ?_⟩
  · -- the cells are subsets of `A`
    rintro i _ ⟨J, -, -, rfl⟩ x hx
    exact hx.1
  · -- covering
    intro x hx
    let P : ℕ → Prop := fun k ↦ 1 ≤ k ∧
      ∃ J : Finset (Set X), ↑J ⊆ 𝓑' ∧ J.card = k ∧ ∀ B ∈ J, infDist x B < k * s
    obtain ⟨B₀, hB₀, hxB₀⟩ := hcov hx
    have hP1 : P 1 := by
      refine ⟨le_rfl, {B₀}, ?_, Finset.card_singleton _, ?_⟩
      · rw [Finset.coe_singleton, singleton_subset_iff]
        exact ⟨hB₀, x, hxB₀⟩
      · intro B hB
        rw [Finset.mem_singleton] at hB
        subst hB
        rw [infDist_zero_of_mem hxB₀]
        simpa using hs
    have hPk : P (Nat.findGreatest P (n + 1)) := Nat.findGreatest_spec (by omega) hP1
    have hkn : Nat.findGreatest P (n + 1) ≤ n + 1 := Nat.findGreatest_le _
    set k := Nat.findGreatest P (n + 1) with hk
    obtain ⟨hk1, J, hJ, hJcard, hJx⟩ := hPk
    have hxJ : x ∈ coloredCell A 𝓑' s J := by
      refine ⟨hx, ?_, ?_⟩
      · rw [hJcard]
        exact hJx
      · intro B hB hBJ
        by_contra hlt
        push Not at hlt
        rw [hJcard] at hlt
        have hJ'card : (insert B J).card = k + 1 := by
          rw [Finset.card_insert_of_notMem hBJ, hJcard]
        have hJ'sub : (↑(insert B J) : Set (Set X)) ⊆ 𝓑' := by
          rw [Finset.coe_insert]
          exact insert_subset hB hJ
        have hJ'x : ∀ B' ∈ insert B J, infDist x B' < ((k + 1 : ℕ) : ℝ) * s := by
          intro B' hB'
          rw [Finset.mem_insert] at hB'
          push_cast
          rcases hB' with rfl | hB'
          · exact hlt
          · have := hJx B' hB'
            nlinarith
        by_cases hk' : k + 1 ≤ n + 1
        · exact Nat.findGreatest_is_greatest (P := P) (by omega) hk'
            ⟨by omega, insert B J, hJ'sub, hJ'card, hJ'x⟩
        · -- `k = n + 1`: then `n + 2` nonempty members are closer than `σ` to `x`
          have hkeq : k + 1 = n + 2 := by omega
          have := card_le_of_infDist_lt (n := n) hσpos hsub hmult (x := x) (J := insert B J)
            (fun B' hB' ↦ (hJ'sub hB').1) (fun B' hB' ↦ (hJ'sub hB').2) (fun B' hB' ↦ by
              have := hJ'x B' hB'
              rw [hkeq] at this
              rw [hσ]
              exact_mod_cast this)
          omega
    refine mem_iUnion.2 ⟨⟨k - 1, by omega⟩, _, ⟨J, hJ, ?_, rfl⟩, hxJ⟩
    simp only
    omega
  · -- diameter bound
    rintro i _ ⟨J, hJ, hcard, rfl⟩ x hx y hy
    have hJne : J.Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    obtain ⟨B, hBJ⟩ := hJne
    have hB : B ∈ 𝓑 := (hJ hBJ).1
    have hBne : B.Nonempty := (hJ hBJ).2
    have hcardσ : (J.card : ℝ) * s ≤ σ := by
      rw [hσ, hcard]
      have : (i.val : ℝ) + 1 ≤ n + 2 := by
        have := i.isLt
        have : (i.val : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 this
        linarith
      push_cast
      nlinarith
    obtain ⟨b, hb, hxb⟩ := (infDist_lt_iff hBne).1 ((hx.2.1 B hBJ).trans_le hcardσ)
    obtain ⟨b', hb', hyb'⟩ := (infDist_lt_iff hBne).1 ((hy.2.1 B hBJ).trans_le hcardσ)
    have hbb' := hdiam B hB b hb b' hb'
    have key : 2 * (c + 1) * ((n : ℝ) + 2) * s = σ + c * (2 * σ) + σ := by
      rw [hσ]; ring
    rw [key]
    calc dist x y ≤ dist x b + dist b y := dist_triangle _ _ _
      _ ≤ dist x b + (dist b b' + dist b' y) := by gcongr; exact dist_triangle _ _ _
      _ ≤ σ + c * (2 * σ) + σ := by
        rw [dist_comm b' y]
        linarith
  · -- separation of cells of the same color
    rintro i _ ⟨J, hJ, hcard, rfl⟩ _ ⟨J', hJ', hcard', rfl⟩ hne x hx y hy
    have hJJ' : J ≠ J' := by
      rintro rfl
      exact hne rfl
    obtain ⟨B, hBJ, hBJ'⟩ : ∃ B ∈ J, B ∉ J' := by
      by_contra hcon
      push Not at hcon
      exact hJJ' (Finset.eq_of_subset_of_card_le hcon (by rw [hcard, hcard']))
    have h1 := hx.2.1 B hBJ
    have h2 := hy.2.2 B (hJ hBJ) hBJ'
    have h3 : infDist y B ≤ infDist x B + dist y x := infDist_le_infDist_add_dist
    rw [hcard'] at h2
    rw [hcard] at h1
    rw [dist_comm] at h3
    push_cast at h1 h2
    linarith

end LipschitzExtension
