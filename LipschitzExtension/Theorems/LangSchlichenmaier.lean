/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Theorems.Whitney
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.SimplicialExtensor
import LipschitzExtension.Topology.MetricSpace.WhitneyCovering.Refined
import LipschitzExtension.Topology.MetricSpace.LocalExtension

/-!
# The Lang–Schlichenmaier theorem with explicit constants

This file proves Theorem 1.1 of [Basso2024] (with item 6 of the errata [BassoClaude2026]), an
explicit version of the Lipschitz extension theorem of Lang and Schlichenmaier: let `X` be a metric
space and `A ⊆ X` a closed subset satisfying `Nagata(n, c)`, and let `Y` be a metric space which
is Lipschitz `n`-connected with constant `λ`. Then every `1`-Lipschitz map `f : A → Y` admits a
`K`-Lipschitz extension `F : X → Y`, where `K` is either of the bounds

* (1.1) `10^(10^10) · λ^(n+1) · (c + 1)^10 · (n + 1)^(10 n)`,
* (1.2) `10^14 · (c + 1)^10 · (10^5 λ)^(n+1) · (n + 1)^(6 n)`.

## Main statements

* `LipschitzOnWith.extend_nagata_lipschitzConnected'`: Theorem 1.1 with the bound (1.2).
* `LipschitzOnWith.extend_nagata_lipschitzConnected`: Theorem 1.1 with the bound (1.1).

## Implementation notes

* In (1.2) the paper has the constant `3 · 10^10`. By item 6 of the errata, the value of `α` in the
  proof is `40 · 16³ (c+1)⁴ 128ⁿ` (the factor `16³` was lost), and `3 · 10^10` has to be replaced
  by `10^14`; with `3 · 10^10` the final estimate of the proof fails already for `n = 0`, by a
  factor of about `150`.
* The bound (1.2) is never worse than (1.1): the inequality between them amounts to
  `10^(5n+19) ≤ 10^(10^10) (n + 1)^(4n)`, which is clear if `5n + 19 ≤ 10^10` and follows from
  `(n + 1)^(4n) ≥ 10^(8n)` otherwise. So, contrary to the remark after Theorem 1.1 in the paper,
  the bound (1.1) is never the better choice, and we derive it from (1.2). (The number
  `10^(10^10)` is never evaluated.)
* No assumption on `c` or `λ` is needed: `Nagata(n, c)` for a nonempty set forces `c ≥ 0`
  (`Nagata.nonneg`), and for `λ < 1` the space `Y` has at most one point
  (`LipschitzConnected.subsingleton`).

## Proof outline

This is the proof of Section 8 of [Basso2024], with items 5 and 6 of the errata. Write
`N = n + 1`. Embed `X` isometrically into a normed space and work there
(`exists_lipschitz_extension_of_local`, errata item 5). With `ρ = 16(c+1) 4^N`, Proposition 8.4
(`Nagata.exists_isWhitneyFamily_refined`) gives a Whitney family for the image of `A` with
multiplicity `N + 1`, `α = 40 ρ³ (c+1)(N+1)`, `δ = 1/(8ρ²)` and `γ = ρ²`; Proposition 8.1
(`LipschitzConnected.simplicialExtensor`) shows that `Y` is an
`(N, λ^N (√2)^(N-1) √N (N!)²)`-simplicial extensor; and Theorem 6.1
(`exists_lipAt_extension_of_isWhitneyFamily`) gives the local extension property with the
constant `100 C α δ⁻¹ γ log₂(N + 2)`, which is at most `10^14 (c+1)^8 (10^5 λ)^N N^(2(N+1))` (the
last display of Section 8, with `10^14`) and hence at most the bound (1.2).

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
* U. Lang and T. Schlichenmaier, *Nagata dimension, quasisymmetric embeddings, and Lipschitz
  extensions*, Int. Math. Res. Not. 2005, no. 58, 3625–3655
-/

open Set Metric

namespace LipschitzExtension

universe u v

/-- The last display of Section 8 (with `10^14` by errata item 6), for `N = n + 1`: the constant of
Theorem 6.1 obtained from Propositions 8.1 and 8.4 is at most
`10^14 (c+1)^8 (10^5 λ)^N N^(2(N+1))`. -/
private theorem whitneyConst_le (n : ℕ) {c Λ : ℝ} (hc : 0 ≤ c) (hΛ : 1 ≤ Λ) :
    100 * (Λ ^ (n + 1) * √2 ^ n * √((n : ℝ) + 1) * ((n + 1).factorial : ℝ) ^ 2) *
        (40 * (16 * (c + 1) * 4 ^ (n + 1)) ^ 3 * (c + 1) * ((n + 1 : ℕ) + 1)) *
        (1 / (8 * (16 * (c + 1) * 4 ^ (n + 1)) ^ 2))⁻¹ * (16 * (c + 1) * 4 ^ (n + 1)) ^ 2 *
        Real.logb 2 ((n + 1 : ℕ) + 2) ≤
      10 ^ 14 * (c + 1) ^ 8 * (10 ^ 5 * Λ) ^ (n + 1) * ((n : ℝ) + 1) ^ (2 * (n + 2)) := by
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hx1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  -- `n + 1 ≤ 2^n`
  have hxa : (n : ℝ) + 1 ≤ 2 ^ n := by
    have h := Nat.lt_two_pow_self (n := n)
    have h' : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  -- the factors
  have hF : ((n + 1).factorial : ℝ) ≤ ((n : ℝ) + 1) ^ (n + 1) := by
    have h := Nat.factorial_le_pow (n + 1)
    have h' : (((n + 1).factorial : ℕ) : ℝ) ≤ (((n + 1) ^ (n + 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    exact h'
  have hsx : √((n : ℝ) + 1) ≤ 2 ^ n :=
    (Real.sqrt_le_self_iff.2 (Or.inr hx1)).trans hxa
  have hs2 : √2 ^ n ≤ (2 : ℝ) ^ n := by
    refine pow_le_pow_left₀ (Real.sqrt_nonneg 2) ?_ n
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hL0 : 0 ≤ Real.logb 2 ((n : ℝ) + 1 + 2) :=
    Real.logb_nonneg one_lt_two (by linarith)
  have hL : Real.logb 2 ((n : ℝ) + 1 + 2) ≤ 2 * ((n : ℝ) + 1) := by
    rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity)]
    have h1 : (n : ℝ) + 3 ≤ 2 ^ (n + 2) := by
      have h : n + 3 ≤ 2 ^ (n + 2) := Nat.lt_two_pow_self
      exact_mod_cast h
    have h2 : (2 : ℝ) ^ (n + 2) ≤ (2 : ℝ) ^ (2 * ((n : ℝ) + 1)) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      push_cast
      linarith
    linarith
  -- rewrite the left-hand side
  have e : 100 * (Λ ^ (n + 1) * √2 ^ n * √((n : ℝ) + 1) * ((n + 1).factorial : ℝ) ^ 2) *
        (40 * (16 * (c + 1) * 4 ^ (n + 1)) ^ 3 * (c + 1) * ((n : ℝ) + 1 + 1)) *
        (1 / (8 * (16 * (c + 1) * 4 ^ (n + 1)) ^ 2))⁻¹ * (16 * (c + 1) * 4 ^ (n + 1)) ^ 2 *
        Real.logb 2 ((n : ℝ) + 1 + 2) =
      32000 * 16 ^ 7 * 4 ^ 7 * ((c + 1) ^ 8 * Λ ^ (n + 1)) * (((2 : ℝ) ^ n) ^ 14 *
        (√2 ^ n * √((n : ℝ) + 1) * ((n + 1).factorial : ℝ) ^ 2 * ((n : ℝ) + 1 + 1) *
          Real.logb 2 ((n : ℝ) + 1 + 2))) := by
    have h4 : (4 : ℝ) ^ (n + 1) = 4 * ((2 : ℝ) ^ n) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      ring
    rw [one_div, inv_inv, h4]
    ring
  rw [e]
  have key : √2 ^ n * √((n : ℝ) + 1) * ((n + 1).factorial : ℝ) ^ 2 * ((n : ℝ) + 1 + 1) *
        Real.logb 2 ((n : ℝ) + 1 + 2) ≤
      2 ^ n * 2 ^ n * (((n : ℝ) + 1) ^ (n + 1)) ^ 2 * (2 * ((n : ℝ) + 1)) *
        (2 * ((n : ℝ) + 1)) := by
    gcongr
    linarith
  have hpow : (((2 : ℝ) ^ n) ^ 16) ≤ (10 ^ 5 : ℝ) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hcΛ : 0 ≤ (c + 1) ^ 8 * Λ ^ (n + 1) :=
    mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
  calc 32000 * 16 ^ 7 * 4 ^ 7 * ((c + 1) ^ 8 * Λ ^ (n + 1)) * (((2 : ℝ) ^ n) ^ 14 *
        (√2 ^ n * √((n : ℝ) + 1) * ((n + 1).factorial : ℝ) ^ 2 * ((n : ℝ) + 1 + 1) *
          Real.logb 2 ((n : ℝ) + 1 + 2)))
      ≤ 32000 * 16 ^ 7 * 4 ^ 7 * ((c + 1) ^ 8 * Λ ^ (n + 1)) * (((2 : ℝ) ^ n) ^ 14 *
          (2 ^ n * 2 ^ n * (((n : ℝ) + 1) ^ (n + 1)) ^ 2 * (2 * ((n : ℝ) + 1)) *
            (2 * ((n : ℝ) + 1)))) := by gcongr
    _ = 32000 * 16 ^ 7 * 4 ^ 7 * 4 * ((c + 1) ^ 8 * Λ ^ (n + 1)) *
          (((2 : ℝ) ^ n) ^ 16 * ((n : ℝ) + 1) ^ (2 * (n + 2))) := by ring
    _ ≤ 32000 * 16 ^ 7 * 4 ^ 7 * 4 * ((c + 1) ^ 8 * Λ ^ (n + 1)) *
          ((10 ^ 5 : ℝ) ^ n * ((n : ℝ) + 1) ^ (2 * (n + 2))) := by gcongr
    _ ≤ 10 ^ 19 * ((c + 1) ^ 8 * Λ ^ (n + 1)) *
          ((10 ^ 5 : ℝ) ^ n * ((n : ℝ) + 1) ^ (2 * (n + 2))) := by
        gcongr
        norm_num
    _ = 10 ^ 14 * (c + 1) ^ 8 * (10 ^ 5 * Λ) ^ (n + 1) * ((n : ℝ) + 1) ^ (2 * (n + 2)) := by
        ring

/-- The bound (1.2) is at most the bound (1.1). -/
private theorem bound_one_two_le_bound_one_one (n : ℕ) (c : ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    10 ^ 14 * (c + 1) ^ 10 * (10 ^ 5 * Λ) ^ (n + 1) * ((n : ℝ) + 1) ^ (6 * n) ≤
      10 ^ (10 ^ 10) * Λ ^ (n + 1) * (c + 1) ^ 10 * ((n : ℝ) + 1) ^ (10 * n) := by
  -- abstract the huge constant `10^(10^10)` (it is never evaluated)
  have hM : ∀ k : ℕ, k ≤ 10 ^ 10 → (10 : ℝ) ^ k ≤ 10 ^ (10 ^ 10) := fun k hk ↦
    pow_le_pow_right₀ (by norm_num) hk
  generalize (10 : ℝ) ^ (10 ^ 10) = M at hM ⊢
  have hM1 : 1 ≤ M := by simpa using hM 0 (by norm_num)
  have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have key : (10 : ℝ) ^ (5 * n + 19) * ((n : ℝ) + 1) ^ (6 * n) ≤
      M * ((n : ℝ) + 1) ^ (10 * n) := by
    by_cases hn : 5 * n + 19 ≤ 10 ^ 10
    · -- small `n`: the power of `10` is absorbed by `M`
      calc (10 : ℝ) ^ (5 * n + 19) * ((n : ℝ) + 1) ^ (6 * n)
          ≤ M * ((n : ℝ) + 1) ^ (6 * n) := by gcongr; exact hM _ hn
        _ ≤ M * ((n : ℝ) + 1) ^ (10 * n) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (by omega)) (by linarith)
    · -- large `n`: `(n + 1)^(4n) ≥ 10^(8n) ≥ 10^(5n+19)`
      push Not at hn
      norm_num at hn
      have h100 : (10 : ℝ) ^ 2 ≤ (n : ℝ) + 1 := by
        have : (99 : ℝ) ≤ n := by exact_mod_cast (show 99 ≤ n by omega)
        linarith
      have h1 : (10 : ℝ) ^ (5 * n + 19) ≤ ((n : ℝ) + 1) ^ (4 * n) := by
        calc (10 : ℝ) ^ (5 * n + 19) ≤ 10 ^ (2 * (4 * n)) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
          _ = ((10 : ℝ) ^ 2) ^ (4 * n) := pow_mul _ _ _
          _ ≤ ((n : ℝ) + 1) ^ (4 * n) := by gcongr
      calc (10 : ℝ) ^ (5 * n + 19) * ((n : ℝ) + 1) ^ (6 * n)
          ≤ ((n : ℝ) + 1) ^ (4 * n) * ((n : ℝ) + 1) ^ (6 * n) := by gcongr
        _ = ((n : ℝ) + 1) ^ (10 * n) := by rw [← pow_add]; ring_nf
        _ ≤ M * ((n : ℝ) + 1) ^ (10 * n) := le_mul_of_one_le_left (by positivity) hM1
  have e1 : (10 ^ 5 * Λ) ^ (n + 1) = (10 : ℝ) ^ (5 * (n + 1)) * Λ ^ (n + 1) := by
    rw [mul_pow, ← pow_mul]
  have e2 : (10 : ℝ) ^ 14 * 10 ^ (5 * (n + 1)) = 10 ^ (5 * n + 19) := by
    rw [← pow_add]
    ring_nf
  calc (10 : ℝ) ^ 14 * (c + 1) ^ 10 * (10 ^ 5 * Λ) ^ (n + 1) * ((n : ℝ) + 1) ^ (6 * n)
      = ((c + 1) ^ 10 * Λ ^ (n + 1)) *
          ((10 : ℝ) ^ 14 * 10 ^ (5 * (n + 1)) * ((n : ℝ) + 1) ^ (6 * n)) := by
        rw [e1]
        ring
    _ = ((c + 1) ^ 10 * Λ ^ (n + 1)) * ((10 : ℝ) ^ (5 * n + 19) * ((n : ℝ) + 1) ^ (6 * n)) := by
        rw [e2]
    _ ≤ ((c + 1) ^ 10 * Λ ^ (n + 1)) * (M * ((n : ℝ) + 1) ^ (10 * n)) := by gcongr
    _ = M * Λ ^ (n + 1) * (c + 1) ^ 10 * ((n : ℝ) + 1) ^ (10 * n) := by ring

end LipschitzExtension

open LipschitzExtension

namespace LipschitzOnWith

universe u v

variable {X : Type u} [MetricSpace X] {Y : Type v} [MetricSpace Y] {n : ℕ} {c Λ : ℝ} {A : Set X}
  {f : X → Y}

/-- **Theorem 1.1** (Lang–Schlichenmaier) with the bound (1.2), where the constant `3 · 10^10` of
the paper is replaced by `10^14` (errata item 6): if `A` is closed and satisfies `Nagata(n, c)` and
`Y` is Lipschitz `n`-connected with constant `λ`, then every `1`-Lipschitz map on `A` extends to a
`10^14 (c + 1)^10 (10^5 λ)^(n+1) (n + 1)^(6n)`-Lipschitz map on `X`. -/
theorem extend_nagata_lipschitzConnected' (hf : LipschitzOnWith 1 f A) (hA : IsClosed A)
    (hN : Nagata n c A) (hY : LipschitzConnected n Λ Y) :
    ∃ F : X → Y, LipschitzWith
        (10 ^ 14 * (c + 1) ^ 10 * (10 ^ 5 * Λ) ^ (n + 1) * (n + 1 : ℝ) ^ (6 * n)).toNNReal F ∧
      EqOn f F A := by
  refine exists_lipschitzWith_eqOn_of_nonempty fun _ ↦ ?_
  -- `Λ < 1`: `Y` has at most one point
  by_cases hΛ1 : Λ < 1
  · have := hY.subsingleton hΛ1
    exact exists_lipschitzWith_eqOn_of_subsingleton f A _
  push Not at hΛ1
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · exact exists_lipschitzWith_eqOn_empty f _
  have hc : 0 ≤ c := hN.nonneg hAne
  have hΛ : 0 ≤ Λ := by linarith
  have hK : 0 ≤ (10 : ℝ) ^ 14 * (c + 1) ^ 10 * (10 ^ 5 * Λ) ^ (n + 1) *
      ((n : ℝ) + 1) ^ (6 * n) := by
    positivity
  suffices h : ∃ F : X → Y, EqOn F f A ∧ ∀ x y, dist (F x) (F y) ≤
      10 ^ 14 * (c + 1) ^ 10 * (10 ^ 5 * Λ) ^ (n + 1) * ((n : ℝ) + 1) ^ (6 * n) * dist x y by
    obtain ⟨F, hFA, hF⟩ := h
    exact ⟨F, LipschitzWith.of_dist_le' hF, hFA.symm⟩
  -- the local extension property, via Propositions 8.4, 8.1 and Theorem 6.1
  refine exists_lipschitz_extension_of_local hA hAne hK ?_
  intro V _ _ _ ι hι
  have : Nonempty X := ⟨hAne.some⟩
  have hc1 : (1 : ℝ) ≤ c + 1 := by linarith
  have h4 : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hρ1 : (1 : ℝ) ≤ 16 * (c + 1) * 4 ^ (n + 1) := by nlinarith
  have hρ : 2 * (c + 1) * 4 ^ (n + 1 + 1) < 16 * (c + 1) * 4 ^ (n + 1) := by
    have h : 0 < (c + 1) * 4 ^ (n + 1) := by positivity
    calc 2 * (c + 1) * 4 ^ (n + 1 + 1) = 8 * ((c + 1) * 4 ^ (n + 1)) := by ring
      _ < 16 * ((c + 1) * 4 ^ (n + 1)) := by linarith
      _ = 16 * (c + 1) * 4 ^ (n + 1) := by ring
  have hNι : Nagata (n + 1 - 1) c (ι '' A) := by
    simpa using hN.image_isometry hι
  obtain ⟨κ, B, r, hW⟩ :=
    Nagata.exists_isWhitneyFamily_refined (hAne.image ι) (n := n + 1) (by omega) hNι hρ
  have hYι : LipschitzConnected (n + 1 - 1) Λ Y := by simpa using hY
  have hS := LipschitzConnected.simplicialExtensor.{u} (n := n + 1) hΛ1 hYι
  have hα : 1 ≤ 40 * (16 * (c + 1) * 4 ^ (n + 1)) ^ 3 * (c + 1) * (((n + 1 : ℕ) : ℝ) + 1) := by
    have h3 : (1 : ℝ) ≤ (16 * (c + 1) * 4 ^ (n + 1)) ^ 3 := one_le_pow₀ hρ1
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) h3) hc1) hn1
  have hγ : (1 : ℝ) ≤ (16 * (c + 1) * 4 ^ (n + 1)) ^ 2 := one_le_pow₀ hρ1
  have hδ : (0 : ℝ) < 1 / (8 * (16 * (c + 1) * 4 ^ (n + 1)) ^ 2) := by positivity
  have hδ' : 1 / (8 * (16 * (c + 1) * 4 ^ (n + 1)) ^ 2) ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hC0 : 0 ≤ Λ ^ (n + 1) * √2 ^ (n + 1 - 1) * √((n + 1 : ℕ) : ℝ) *
      ((n + 1).factorial : ℝ) ^ 2 := by
    positivity
  obtain ⟨F, hF1, hF2, C, hC⟩ := exists_lipAt_extension_of_isWhitneyFamily (hAne.image ι)
    (lipschitzOnWith_comp_invFun hι hf) hW hα hδ hδ' hγ hC0 hS
  refine ⟨F, fun a ha ↦ ?_, fun z hz ↦ (hF2 z hz).mono ?_, C, fun a ha z hz ↦ ?_⟩
  · rw [hF1 _ (mem_image_of_mem ι ha), comp_invFun_apply hι]
  · -- the constant of Proposition 8.1 for `N = n + 1`, and the bound (1.2)
    have e : Λ ^ (n + 1) * √2 ^ (n + 1 - 1) * √((n + 1 : ℕ) : ℝ) *
        ((n + 1).factorial : ℝ) ^ 2 =
        Λ ^ (n + 1) * √2 ^ n * √((n : ℝ) + 1) * ((n + 1).factorial : ℝ) ^ 2 := by
      rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    rw [e]
    refine (whitneyConst_le n hc hΛ1).trans ?_
    have hx1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have h8 : (c + 1) ^ 8 ≤ (c + 1) ^ 10 := pow_le_pow_right₀ hc1 (by norm_num)
    have hpow : ((n : ℝ) + 1) ^ (2 * (n + 2)) ≤ ((n : ℝ) + 1) ^ (6 * n) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num
      · exact pow_le_pow_right₀ hx1 (by omega)
    gcongr
  · have := hC _ (mem_image_of_mem ι ha) z hz
    rwa [comp_invFun_apply hι] at this

/-- **Theorem 1.1** (Lang–Schlichenmaier) with the bound (1.1): if `A` is closed and satisfies
`Nagata(n, c)` and `Y` is Lipschitz `n`-connected with constant `λ`, then every `1`-Lipschitz map
on `A` extends to a `10^(10^10) λ^(n+1) (c + 1)^10 (n + 1)^(10n)`-Lipschitz map on `X`. This
follows from the bound (1.2) (`extend_nagata_lipschitzConnected'`). -/
theorem extend_nagata_lipschitzConnected (hf : LipschitzOnWith 1 f A) (hA : IsClosed A)
    (hN : Nagata n c A) (hY : LipschitzConnected n Λ Y) :
    ∃ F : X → Y, LipschitzWith
        (10 ^ (10 ^ 10) * Λ ^ (n + 1) * (c + 1) ^ 10 * (n + 1 : ℝ) ^ (10 * n)).toNNReal F ∧
      EqOn f F A := by
  -- `Λ < 0`: `Y` has at most one point
  by_cases hΛ : Λ < 0
  · have := hY.subsingleton (hΛ.trans one_pos)
    exact exists_lipschitzWith_eqOn_of_subsingleton f A _
  push Not at hΛ
  obtain ⟨F, hF, hFA⟩ := hf.extend_nagata_lipschitzConnected' hA hN hY
  exact ⟨F, hF.weaken (Real.toNNReal_le_toNNReal (bound_one_two_le_bound_one_one n c hΛ)), hFA⟩

end LipschitzOnWith
