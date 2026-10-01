/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Nagata.Defs
import LipschitzExtension.Topology.MetricSpace.WhitneyCovering.Defs
import Mathlib.Order.Zorn
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Whitney families from the Nagata condition

This file proves Proposition 3.1 of [Basso2024], with the constants corrected as in item 2) of
Section 9 of the errata [BassoClaude2026]: a nonempty subset `A` of a metric space `Z` which
satisfies `Nagata(n, c)` admits a Whitney family (`IsWhitneyFamily`) with multiplicity `3(n + 1)`.

More precisely, let `ρ > 1`, `ε = (ρ - 1)/(2ρ)` and `δ = ε/(2ρ)`. Then there is a covering `(B i)`
of `{z | 0 < d(z, A)}` such that, with `r i = d(B i, A)`,
1. `diam B i ≤ α r i` with `α = 2(ρ + ε + c(ρ + 2ε))/(1 - ε)`
   (errata: instead of `2(ρ + ε)(1 + c)/(1 - ε)`),
2. every `z` lies in `N_{δ r i}(B i)` for at most `3(n + 1)` indices `i`,
3. `hd⁺(B i, A) ≤ γ r i` with `γ = (ρ + ε)/(1 - ε)` (errata: instead of `γ = ρ + ε`).

In the paper the parameter `ρ` is called `r`.

## Main statements

* `Nagata.exists_isWhitneyFamily`: Proposition 3.1 for a general parameter `ρ > 1`.
* `Nagata.exists_isWhitneyFamily'`: the case `ρ = 5/4`, in which `ε = 1/10`, `δ = 1/25`,
  `α = 3 + (29/9) c` and `γ = 3/2`; this is the Whitney family used in the proof of Theorem 1.2.

## Proof outline

We follow the proof of the paper. For `k ∈ ℤ` let `R_k = {x | ρ^k ≤ d(x, A) < ρ^(k+1)}`, let
`W_k ⊆ R_k` be a maximal subset whose points are pairwise at distance `> ε ρ^k` (Zorn), and
choose `p_k : W_k → A` with `d(p_k w, w) < ρ^(k+1)` (possible since `d(w, A) < ρ^(k+1)`; the
strict inequality is important). Let `s_k = 2(2ε + ρ) ρ^k` and let `𝓐_k` be a cover of `A` as in
`Nagata(n, c)` at scale `s_k`. For `C ∈ 𝓐_k` put
`B_{k,C} = {x | ∃ w ∈ W_k, d(x, w) ≤ ε ρ^k ∧ p_k w ∈ C}` and keep the nonempty ones; the index
type is `Σ k : ℤ, 𝓐_k` (restricted to nonempty members).
* `(1 - ε) ρ^k ≤ d(x, A) < (ρ + ε) ρ^k` for `x ∈ B_{k,C}`; hence `r_{k,C} ≥ (1 - ε) ρ^k`.
* `diam B_{k,C} ≤ 2 ε ρ^k + 2 ρ^(k+1) + c s_k = 2(ρ + ε + c(ρ + 2ε)) ρ^k`.
* `δ r_{k,C} < ε ρ^k`, so `N_{δ r}(B_{k,C}) ⊆ {x | ∃ w ∈ W_k, d(x, w) < 2ερ^k ∧ p_k w ∈ C}`.
  For fixed `k` at most `n + 1` sets `C` occur (take any finite family of witnesses `w`; the points
  `p_k w` form a finite set of diameter `< s_k`, which meets at most `n + 1` members of `𝓐_k`),
  and only `k` with `d(x, A) ∈ (ρ^(k-1), ρ^(k+2))` occur (use `1 - 2ε = 1/ρ` and
  `ρ + (ρ-1)/ρ ≤ ρ^2`), i.e. at most three values of `k`.

## Implementation notes

In the formal proof we simply take `W_k = R_k`: the separation of `W_k` is never used (the
multiplicity bound only uses the Nagata condition), so no appeal to Zorn's lemma is needed. We work
with `d(x, A) = infDist x A` directly (`A` need not be closed), the index type is
`{q : ℤ × Set Z // q.2 ∈ 𝓐_{q.1} ∧ B_{q.1, q.2}.Nonempty}`, and `r_i` is the infimum of `d(·, A)`
over `B_i`. The constant `c ≥ 0` is read off directly from the Nagata coverings.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
-/

open Set Metric

namespace LipschitzExtension

universe u

/-- **Proposition 3.1** of [Basso2024], with the constants of item 2) of the errata: if `A` is
nonempty and satisfies `Nagata(n, c)`, `ρ > 1`, `ε = (ρ - 1)/(2ρ)` and `δ = ε/(2ρ)`, then there is
a Whitney family for `A` with multiplicity `3(n + 1)`, `α = 2(ρ + ε + c(ρ + 2ε))/(1 - ε)`, the
given `δ` and `γ = (ρ + ε)/(1 - ε)`. -/
theorem Nagata.exists_isWhitneyFamily {Z : Type u} [MetricSpace Z] {A : Set Z}
    (hA : A.Nonempty) {n : ℕ} {c : ℝ} (hN : Nagata n c A) {ρ ε δ : ℝ} (hρ : 1 < ρ)
    (hε : ε = (ρ - 1) / (2 * ρ)) (hδ : δ = ε / (2 * ρ)) :
    ∃ (ι : Type u) (B : ι → Set Z) (r : ι → ℝ),
      IsWhitneyFamily A B r (3 * (n + 1)) (2 * (ρ + ε + c * (ρ + 2 * ε)) / (1 - ε)) δ
        ((ρ + ε) / (1 - ε)) := by
  -- Elementary facts about the constants.
  have hρ0 : 0 < ρ := by linarith
  have h2ε : 2 * ε * ρ = ρ - 1 := by rw [hε]; field_simp
  have hε0 : 0 < ε := by rw [hε]; apply div_pos <;> linarith
  have hε1 : ε < 1 / 2 := by nlinarith
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδε : δ * (ρ + ε) ≤ ε := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  have hρinv : ρ⁻¹ = 1 - 2 * ε := inv_eq_of_mul_eq_one_right (by linarith)
  have hρ2 : ρ + 2 * ε ≤ ρ ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (ρ - 1)) (by linarith : (0:ℝ) ≤ ρ + 1)]
  have hpow : ∀ k : ℤ, 0 < ρ ^ k := fun k ↦ zpow_pos hρ0 k
  have hpow1 : ∀ k : ℤ, ρ ^ (k + 1) = ρ ^ k * ρ := fun k ↦ zpow_add_one₀ hρ0.ne' k
  -- The annuli `R k = {w | ρ^k ≤ d(w, A) < ρ^(k+1)}`.
  set R : ℤ → Set Z := fun k ↦ {w | ρ ^ k ≤ infDist w A ∧ infDist w A < ρ ^ (k + 1)} with hR
  -- Almost nearest points `p k w ∈ A` with `d(w, p k w) < ρ^(k+1)` (strict).
  have hp : ∀ (k : ℤ) (w : Z), ∃ a ∈ A, infDist w A < ρ ^ (k + 1) → dist w a < ρ ^ (k + 1) := by
    intro k w
    by_cases h : infDist w A < ρ ^ (k + 1)
    · obtain ⟨a, ha, hwa⟩ := (infDist_lt_iff hA).1 h
      exact ⟨a, ha, fun _ ↦ hwa⟩
    · obtain ⟨a, ha⟩ := hA
      exact ⟨a, ha, fun h' ↦ absurd h' h⟩
  choose p hpA hpd using hp
  -- The scales `s k = 2 (2ε + ρ) ρ^k` and the corresponding Nagata coverings of `A`.
  set s : ℤ → ℝ := fun k ↦ 2 * (2 * ε + ρ) * ρ ^ k with hs
  have hs0 : ∀ k, 0 < s k := fun k ↦ by have := hpow k; simp only [hs]; positivity
  choose 𝓐 h𝓐A h𝓐cov h𝓐diam h𝓐mult using fun k : ℤ ↦ hN (s k) (hs0 k)
  have hc : 0 ≤ c := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨C, hC, haC⟩ := mem_sUnion.1 (h𝓐cov 0 ha)
    have := h𝓐diam 0 C hC a haC a haC
    rw [dist_self] at this
    exact nonneg_of_mul_nonneg_left this (hs0 0)
  -- The sets `B' k C`.
  set B' : ℤ → Set Z → Set Z :=
    fun k C ↦ {x | ∃ w ∈ R k, dist x w ≤ ε * ρ ^ k ∧ p k w ∈ C} with hB'
  have hB'lo : ∀ k C, ∀ x ∈ B' k C, (1 - ε) * ρ ^ k ≤ infDist x A := by
    rintro k C x ⟨w, ⟨hw1, hw2⟩, hxw, -⟩
    have := infDist_le_infDist_add_dist (x := w) (y := x) (s := A)
    rw [dist_comm] at this
    linarith
  have hB'hi : ∀ k C, ∀ x ∈ B' k C, infDist x A < (ρ + ε) * ρ ^ k := by
    rintro k C x ⟨w, ⟨hw1, hw2⟩, hxw, -⟩
    have := infDist_le_infDist_add_dist (x := x) (y := w) (s := A)
    rw [hpow1] at hw2
    linarith
  -- The index set, the covering and the scales.
  let ι : Type u := {q : ℤ × Set Z // q.2 ∈ 𝓐 q.1 ∧ (B' q.1 q.2).Nonempty}
  let B : ι → Set Z := fun i ↦ B' i.1.1 i.1.2
  let r : ι → ℝ := fun i ↦ sInf ((fun z ↦ infDist z A) '' B i)
  have hbdd : ∀ i : ι, BddBelow ((fun z ↦ infDist z A) '' B i) :=
    fun i ↦ ⟨0, by rintro _ ⟨z, -, rfl⟩; exact infDist_nonneg⟩
  have hne : ∀ i : ι, ((fun z ↦ infDist z A) '' B i).Nonempty := fun i ↦ i.2.2.image _
  have hr_lo : ∀ i : ι, (1 - ε) * ρ ^ i.1.1 ≤ r i := fun i ↦
    le_csInf (hne i) (by rintro _ ⟨x, hx, rfl⟩; exact hB'lo _ _ x hx)
  have hr_le : ∀ i : ι, ∀ x ∈ B i, r i ≤ infDist x A :=
    fun i x hx ↦ csInf_le (hbdd i) ⟨x, hx, rfl⟩
  have hαr : ∀ i : ι, ∀ K : ℝ, 0 ≤ K → K * ρ ^ i.1.1 ≤ K / (1 - ε) * r i := by
    intro i K hK
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    calc K * ρ ^ i.1.1 * (1 - ε) = K * ((1 - ε) * ρ ^ i.1.1) := by ring
      _ ≤ K * r i := mul_le_mul_of_nonneg_left (hr_lo i) hK
  refine ⟨ι, B, r, ?_⟩
  refine
    { nonempty := fun i ↦ i.2.2
      r_pos := fun i ↦ lt_of_lt_of_le (mul_pos (by linarith) (hpow _)) (hr_lo i)
      isGLB := fun i ↦ isGLB_csInf (hne i) (hbdd i)
      cover := ?_
      diam_le := ?_
      mult_le := ?_
      hd_le := ?_ }
  · -- covering
    intro z hz
    obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow hz hρ
    obtain ⟨C, hC, hpC⟩ := mem_sUnion.1 (h𝓐cov k (hpA k z))
    have hzB : z ∈ B' k C :=
      ⟨z, ⟨hk1, hk2⟩, by rw [dist_self]; exact (mul_pos hε0 (hpow k)).le, hpC⟩
    exact ⟨⟨(k, C), hC, z, hzB⟩, hzB⟩
  · -- controlled diameter
    rintro ⟨⟨k, C⟩, hC, hne'⟩ x ⟨w1, ⟨hw1, hw1'⟩, hxw1, hpw1⟩ y ⟨w2, ⟨hw2, hw2'⟩, hyw2, hpw2⟩
    have d1 := hpd k w1 hw1'
    have d2 := hpd k w2 hw2'
    have d3 := h𝓐diam k C hC _ hpw1 _ hpw2
    have t1 : dist x y ≤ dist x w1 + dist w1 (p k w1) + dist (p k w1) (p k w2) +
        dist (p k w2) w2 + dist w2 y := by
      have := dist_triangle x w1 y
      have := dist_triangle4 w1 (p k w1) (p k w2) y
      have := dist_triangle (p k w2) w2 y
      linarith
    rw [dist_comm (p k w2) w2, dist_comm w2 y] at t1
    have key := hαr ⟨(k, C), hC, hne'⟩ (2 * (ρ + ε + c * (ρ + 2 * ε))) (by positivity)
    simp only at key
    rw [hpow1] at d1 d2
    simp only [hs] at d3
    nlinarith
  · -- bounded multiplicity
    intro z hz
    obtain ⟨k0, hk01, hk02⟩ := exists_mem_Ico_zpow hz hρ
    -- If `z ∈ N_{δ r_i}(B_i)` with `i = (k, C)`, there is `w ∈ R k` with `d(z, w) < 2ερ^k` and
    -- `p k w ∈ C`.
    have key : ∀ i : ι, infDist z (B i) < δ * r i →
        ∃ w ∈ R i.1.1, dist z w < 2 * ε * ρ ^ i.1.1 ∧ p i.1.1 w ∈ i.1.2 := by
      intro i hi
      obtain ⟨y, hy, hzy⟩ := (infDist_lt_iff i.2.2).1 hi
      have h1 := hr_le i y hy
      have h2 := hB'hi _ _ y hy
      obtain ⟨w, hw, hyw, hpw⟩ := hy
      refine ⟨w, hw, ?_, hpw⟩
      have h3 : dist z w ≤ dist z y + dist y w := dist_triangle _ _ _
      have h4 : δ * r i ≤ δ * infDist y A := mul_le_mul_of_nonneg_left h1 hδ0.le
      have h5 : δ * infDist y A < δ * ((ρ + ε) * ρ ^ i.1.1) := mul_lt_mul_of_pos_left h2 hδ0
      have h6 : δ * (ρ + ε) * ρ ^ i.1.1 ≤ ε * ρ ^ i.1.1 :=
        mul_le_mul_of_nonneg_right hδε (hpow _).le
      linarith
    -- Only the three scales `k0 - 1`, `k0`, `k0 + 1` occur.
    have hrange : ∀ i : ι, infDist z (B i) < δ * r i →
        i.1.1 = k0 - 1 ∨ i.1.1 = k0 ∨ i.1.1 = k0 + 1 := by
      intro i hi
      obtain ⟨w, ⟨hw1, hw2⟩, hzw, -⟩ := key i hi
      have e1 : infDist w A ≤ infDist z A + dist w z := infDist_le_infDist_add_dist
      have e2 : infDist z A ≤ infDist w A + dist z w := infDist_le_infDist_add_dist
      rw [dist_comm] at e1
      have lo : ρ ^ (i.1.1 - 1) < infDist z A := by
        rw [zpow_sub_one₀ hρ0.ne', hρinv]
        linarith
      have hi' : infDist z A < ρ ^ (i.1.1 + 2) := by
        rw [show i.1.1 + 2 = i.1.1 + 1 + 1 by ring, hpow1, hpow1]
        rw [hpow1] at hw2
        have := mul_le_mul_of_nonneg_left hρ2 (hpow i.1.1).le
        nlinarith
      have a1 : i.1.1 - 1 < k0 + 1 := (zpow_lt_zpow_iff_right₀ hρ).1 (lo.trans hk02)
      have a2 : k0 < i.1.1 + 2 := (zpow_lt_zpow_iff_right₀ hρ).1 (hk01.trans_lt hi')
      omega
    -- Witnesses as a function.
    have hw : ∀ i : ι, ∃ w : Z, infDist z (B i) < δ * r i →
        w ∈ R i.1.1 ∧ dist z w < 2 * ε * ρ ^ i.1.1 ∧ p i.1.1 w ∈ i.1.2 := by
      intro i
      by_cases h : infDist z (B i) < δ * r i
      · obtain ⟨w, hw1, hw2, hw3⟩ := key i h
        exact ⟨w, fun _ ↦ ⟨hw1, hw2, hw3⟩⟩
      · exact ⟨z, fun h' ↦ absurd h' h⟩
    choose wf hwf using hw
    -- For a fixed scale `j`, at most `n + 1` indices occur.
    have hper : ∀ j : ℤ, {i : ι | i.1.1 = j ∧ infDist z (B i) < δ * r i}.encard ≤ n + 1 := by
      intro j
      refine not_lt.1 fun hcon ↦ ?_
      obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq ((ENat.add_one_le_iff (by simp)).2 hcon)
      have htfin : t.Finite :=
        Set.finite_of_encard_eq_coe (k := n + 2) (by rw [htc]; push_cast; ring)
      set M : Set Z := (fun i ↦ p j (wf i)) '' t with hM
      have hMfin : M.Finite := htfin.image _
      have hMA : M ⊆ A := by rintro _ ⟨i, -, rfl⟩; exact hpA _ _
      have hMd : ∀ x ∈ M, ∀ y ∈ M, dist x y < s j := by
        rintro _ ⟨i, hi, rfl⟩ _ ⟨i', hi', rfl⟩
        obtain ⟨hij, hi2⟩ := hts hi
        obtain ⟨hi'j, hi'2⟩ := hts hi'
        obtain ⟨⟨-, hw1⟩, hzw1, -⟩ := hwf i hi2
        obtain ⟨⟨-, hw2⟩, hzw2, -⟩ := hwf i' hi'2
        rw [hij] at hw1 hzw1
        rw [hi'j] at hw2 hzw2
        have d1 := hpd j (wf i) hw1
        have d2 := hpd j (wf i') hw2
        have t1 : dist (p j (wf i)) (p j (wf i')) ≤ dist (p j (wf i)) (wf i) + dist (wf i) z +
            dist z (wf i') + dist (wf i') (p j (wf i')) := by
          have := dist_triangle4 (p j (wf i)) (wf i) z (wf i')
          have := dist_triangle (p j (wf i)) (wf i') (p j (wf i'))
          linarith
        rw [dist_comm (p j (wf i)) (wf i), dist_comm (wf i) z] at t1
        rw [hpow1] at d1 d2
        simp only [hs]
        linarith
      have hMdiam := ediam_lt_ofReal_of_finite hMfin (hs0 j) hMd
      have hbound := h𝓐mult j M hMA hMdiam
      have hinj : t.encard ≤ {C ∈ 𝓐 j | (C ∩ M).Nonempty}.encard := by
        apply Set.encard_le_encard_of_injOn (f := fun i : ι ↦ i.1.2)
        · intro i hi
          obtain ⟨hij, hi2⟩ := hts hi
          obtain ⟨-, -, hpw⟩ := hwf i hi2
          rw [hij] at hpw
          have hC := i.2.1
          rw [hij] at hC
          exact ⟨hC, p j (wf i), hpw, ⟨i, hi, rfl⟩⟩
        · rintro ⟨⟨k, C⟩, hC⟩ hi ⟨⟨k', C'⟩, hC'⟩ hi' h
          have hk : k = j := (hts hi).1
          have hk' : k' = j := (hts hi').1
          simp only at h
          subst hk hk' h
          rfl
      rw [htc] at hinj
      have := hinj.trans hbound
      norm_cast at this
      omega
    have hsub : {i : ι | infDist z (B i) < δ * r i} ⊆
        ({i : ι | i.1.1 = k0 - 1 ∧ infDist z (B i) < δ * r i} ∪
          {i : ι | i.1.1 = k0 ∧ infDist z (B i) < δ * r i}) ∪
          {i : ι | i.1.1 = k0 + 1 ∧ infDist z (B i) < δ * r i} := by
      intro i hi
      rcases hrange i hi with h | h | h
      · exact Or.inl (Or.inl ⟨h, hi⟩)
      · exact Or.inl (Or.inr ⟨h, hi⟩)
      · exact Or.inr ⟨h, hi⟩
    calc _ ≤ _ := Set.encard_le_encard hsub
      _ ≤ _ := Set.encard_union_le _ _
      _ ≤ _ := add_le_add (Set.encard_union_le _ _) le_rfl
      _ ≤ (n + 1) + (n + 1) + (n + 1) := add_le_add (add_le_add (hper _) (hper _)) (hper _)
      _ = _ := by push_cast; ring
  · -- controlled distance to `A`
    intro i x hx
    have h1 := hB'hi _ _ x hx
    have h2 := hαr i (ρ + ε) (by linarith)
    linarith

/-- **Proposition 3.1** of [Basso2024] for `ρ = 5/4`: then `ε = 1/10`, `δ = 1/25`,
`α = 3 + (29/9) c` and `γ = 3/2` (errata, item 2). This is the Whitney family used in the proof of
Theorem 1.2. -/
theorem Nagata.exists_isWhitneyFamily' {Z : Type u} [MetricSpace Z] {A : Set Z}
    (hA : A.Nonempty) {n : ℕ} {c : ℝ} (hN : Nagata n c A) :
    ∃ (ι : Type u) (B : ι → Set Z) (r : ι → ℝ),
      IsWhitneyFamily A B r (3 * (n + 1)) (3 + 29 / 9 * c) (1 / 25) (3 / 2) := by
  obtain ⟨ι, B, r, h⟩ := Nagata.exists_isWhitneyFamily hA hN (ρ := 5 / 4) (ε := 1 / 10)
    (δ := 1 / 25) (by norm_num) (by norm_num) (by norm_num)
  have e1 : 2 * (5 / 4 + 1 / 10 + c * (5 / 4 + 2 * (1 / 10))) / (1 - 1 / 10) = 3 + 29 / 9 * c := by
    ring
  have e2 : ((5 : ℝ) / 4 + 1 / 10) / (1 - 1 / 10) = 3 / 2 := by norm_num
  rw [e1, e2] at h
  exact ⟨ι, B, r, h⟩

end LipschitzExtension
