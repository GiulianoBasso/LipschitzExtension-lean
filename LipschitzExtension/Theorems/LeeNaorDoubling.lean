/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Theorems.Barycentric
import LipschitzExtension.Topology.MetricSpace.Nagata.Doubling

/-!
# The Lee–Naor theorem for doubling spaces with explicit constants

This file proves Theorem 1.4 of [Basso2024] (which holds as stated by the errata
[BassoClaude2026]): let `X` be a metric space and `A ⊆ X` a subset that is `M`-doubling for some
`M ≥ 2`, and let `E` be a real Banach space. Then every `1`-Lipschitz map `f : A → E` admits a
`10^5 · log M`-Lipschitz extension `F : X → E`.

## Main statements

* `LipschitzOnWith.extend_doubling_normedSpace`: Theorem 1.4.
* `LipschitzOnWith.extend_finite_normedSpace'`: the consequence for sets with at most `n ≥ 2`
  points, with constant `10^5 log n` (compare Theorem 1.5,
  `LipschitzOnWith.extend_finite_normedSpace`, which gives `1000 log n / log log n` for `n ≥ 3`).

## Proof outline

`A` satisfies `Nagata(M³, 2)` (`Doubling.nagata_cube`), so Theorem 1.2
(`LipschitzOnWith.extend_nagata_normedSpace`) gives the constant `3000 log₂(M³ + 2)`, which is at
most `10^5 log M`. A set with at most `n` points is `n`-doubling (`doubling_of_ncard_le`).

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
* J. R. Lee and A. Naor, *Extending Lipschitz functions via random metric partitions*,
  Invent. Math. 160 (2005), 59–95
-/

open Set Metric

namespace LipschitzExtension

/-- The constant of Theorem 1.2 for `Nagata(M³, 2)` is at most `10^5 log M`. -/
private theorem doubling_numeric {M : ℕ} (hM : 2 ≤ M) :
    1000 * ((2 : ℝ) + 1) * Real.logb 2 ((M ^ 3 : ℕ) + 2) ≤ 10 ^ 5 * Real.log M := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hlog2 : 0.69 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogM : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM'
  have hcube : ((M ^ 3 : ℕ) : ℝ) + 2 ≤ 2 * (M : ℝ) ^ 3 := by
    push_cast
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hM' 3]
  have hlogcube : Real.log (((M ^ 3 : ℕ) : ℝ) + 2) ≤ Real.log 2 + 3 * Real.log M := by
    calc Real.log (((M ^ 3 : ℕ) : ℝ) + 2) ≤ Real.log (2 * (M : ℝ) ^ 3) :=
          Real.log_le_log (by positivity) hcube
      _ = Real.log 2 + 3 * Real.log M := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  rw [Real.logb, div_eq_mul_inv]
  have hl2pos : 0 < Real.log 2 := by linarith
  rw [show 1000 * ((2 : ℝ) + 1) * (Real.log (((M ^ 3 : ℕ) : ℝ) + 2) * (Real.log 2)⁻¹) =
      3000 * Real.log (((M ^ 3 : ℕ) : ℝ) + 2) / Real.log 2 by ring]
  rw [div_le_iff₀ hl2pos]
  nlinarith

end LipschitzExtension

open LipschitzExtension

namespace LipschitzOnWith

universe u v

variable {X : Type u} [MetricSpace X] {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {A : Set X} {f : X → E}

/-- **Theorem 1.4** (Lee–Naor for doubling spaces, with explicit constant): if `A ⊆ X` is
`M`-doubling, `M ≥ 2`, and `E` is a real Banach space, then every `1`-Lipschitz map `f : A → E`
extends to a `10^5 log M`-Lipschitz map `F : X → E`. -/
theorem extend_doubling_normedSpace {M : ℕ} (hf : LipschitzOnWith 1 f A) (hA : Doubling M A)
    (hM : 2 ≤ M) : ∃ F : X → E, LipschitzWith (10 ^ 5 * Real.log M).toNNReal F ∧ EqOn f F A := by
  obtain ⟨F, hF, hFA⟩ := hf.extend_nagata_normedSpace hA.nagata_cube
  exact ⟨F, hF.weaken (Real.toNNReal_le_toNNReal (doubling_numeric hM)), hFA⟩

/-- Consequence of **Theorem 1.4**: extensions from sets with at most `n ≥ 2` points into Banach
spaces, with constant `10^5 log n` (compare `extend_finite_normedSpace`). -/
theorem extend_finite_normedSpace' {n : ℕ} (hf : LipschitzOnWith 1 f A) (hA : A.Finite)
    (hcard : A.ncard ≤ n) (hn : 2 ≤ n) :
    ∃ F : X → E, LipschitzWith (10 ^ 5 * Real.log n).toNNReal F ∧ EqOn f F A :=
  hf.extend_doubling_normedSpace (doubling_of_ncard_le hA hcard) hn

end LipschitzOnWith
