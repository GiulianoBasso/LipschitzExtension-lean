/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Theorems.LeeNaorFinite.Local
import LipschitzExtension.Topology.MetricSpace.LocalExtension
import LipschitzExtension.Topology.MetricSpace.AbsoluteExtendability

/-!
# The Lee–Naor theorem for finite sets with explicit constants

This file proves Theorem 1.5 of [Basso2024], with the constant `1000` of item 1 of the errata
[BassoClaude2026] instead of `600`: let `X` be a metric space and `A ⊆ X` a subset consisting of
at most `n` points, `n ≥ 3`, and let `E` be a real normed space. Then every `1`-Lipschitz map
`f : A → E` admits a `1000 · log n / log (log n)`-Lipschitz extension `F : X → E` (the bound
(1.5)). As a consequence, the absolute Lipschitz extendability constant (Definition 1.4) of a
metric space with at most `n ≥ 3` points satisfies `æ(X) ≤ 1000 log n / log log n` (the bound
(1.6)).

## Main statements

* `LipschitzOnWith.extend_finite_normedSpace`: Theorem 1.5.
* `absLipExtendableWith_of_card_le`, `absLipExtConst_le_of_card_le`: the bound (1.6).

## Implementation notes

* Completeness of `E` is not needed; we state the theorem for all real normed spaces.
* The extension is constructed on an isometric copy of `X` in a normed space
  (`exists_lipAt_extension_of_finite`, the construction of Section 4 of [Basso2024]), and the
  reduction of item 5 of the errata (`exists_lipschitz_extension_of_local`) gives the global
  bound.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
* J. R. Lee and A. Naor, *Extending Lipschitz functions via random metric partitions*,
  Invent. Math. 160 (2005), 59–95
-/

open Set Metric

namespace LipschitzExtension

/-- The constant `1000 log n / log log n` is positive for `n ≥ 3`. -/
private theorem leeNaor_constant_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < 1000 * Real.log n / Real.log (Real.log n) := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith
  have hloglog : 0 < Real.log (Real.log n) := Real.log_pos hlog
  positivity

end LipschitzExtension

open LipschitzExtension

namespace LipschitzOnWith

universe u v

variable {X : Type u} [MetricSpace X] {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : Set X} {f : X → E}

/-- **Theorem 1.5** (Lee–Naor for finite sets, with the constant `1000` of errata item 1): if
`A ⊆ X` has at most `n ≥ 3` points and `E` is a real normed space, then every `1`-Lipschitz map
`f : A → E` extends to a `1000 log n / log log n`-Lipschitz map `F : X → E`. -/
theorem extend_finite_normedSpace {n : ℕ} (hf : LipschitzOnWith 1 f A) (hA : A.Finite)
    (hcard : A.ncard ≤ n) (hn : 3 ≤ n) :
    ∃ F : X → E,
      LipschitzWith (1000 * Real.log n / Real.log (Real.log n)).toNNReal F ∧ EqOn f F A := by
  have hK := leeNaor_constant_pos hn
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · exact exists_lipschitzWith_eqOn_empty f _
  obtain ⟨F, hFA, hF⟩ := exists_lipschitz_extension_of_local hA.isClosed hAne hK.le (by
    intro V _ _ _ ι hι
    have : Nonempty X := ⟨hAne.some⟩
    have hcard' : (ι '' A).ncard ≤ n := by
      rw [ncard_image_of_injective _ hι.injective]
      exact hcard
    obtain ⟨F, hF1, hF2, C, hC⟩ := exists_lipAt_extension_of_finite compl_closedBall_nonempty
      (hA.image ι) (hAne.image ι) hn hcard' (lipschitzOnWith_comp_invFun hι hf)
    refine ⟨F, fun a ha ↦ ?_, hF2, C, fun a ha z hz ↦ ?_⟩
    · rw [hF1 _ (mem_image_of_mem ι ha), comp_invFun_apply hι]
    · have := hC _ (mem_image_of_mem ι ha) z hz
      rwa [comp_invFun_apply hι] at this)
  exact ⟨F, LipschitzWith.of_dist_le' hF, hFA.symm⟩

end LipschitzOnWith


open scoped ENNReal NNReal

namespace LipschitzExtension

universe u v w

/-- **Theorem 1.5**, reformulated: a metric space with at most `n ≥ 3` points is absolutely
Lipschitz extendable with constant `1000 log n / log log n`. -/
theorem absLipExtendableWith_of_card_le {X : Type w} [MetricSpace X] [Finite X] {n : ℕ}
    (hn : 3 ≤ n) (hX : Nat.card X ≤ n) :
    AbsLipExtendableWith.{u, v} X (1000 * Real.log n / Real.log (Real.log n)) := by
  intro Xe _ ι hι Y _ _ _ f hf
  have hinj : Function.Injective ι := hι.injective
  -- extend `f ∘ ι⁻¹` from the range of `ι` to all of `Xe` (arbitrarily)
  have hext : ∀ x, Function.extend ι f 0 (ι x) = f x := fun x ↦ hinj.extend_apply f 0 x
  have hcard : (range ι).ncard ≤ n := by
    rw [ncard_range_of_injective hinj]
    exact hX
  have hf' : LipschitzOnWith 1 (Function.extend ι f 0) (range ι) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hext, hext, hι x y]
    exact hf x y
  obtain ⟨F, hF, hFA⟩ := hf'.extend_finite_normedSpace (finite_range ι) hcard hn
  refine ⟨F, fun x ↦ (hFA ⟨x, rfl⟩).symm.trans (hext x), fun x y ↦ ?_⟩
  rw [← Real.coe_toNNReal _ (leeNaor_constant_pos hn).le]
  exact hF.dist_le_mul x y

/-- **(1.6)** (with the constant `1000` of errata item 1): a metric space with at most `n ≥ 3`
points satisfies `æ(X) ≤ 1000 log n / log log n`. -/
theorem absLipExtConst_le_of_card_le {X : Type w} [MetricSpace X] [Finite X] {n : ℕ}
    (hn : 3 ≤ n) (hX : Nat.card X ≤ n) :
    absLipExtConst.{u, v} X ≤ ENNReal.ofReal (1000 * Real.log n / Real.log (Real.log n)) := by
  have hK := leeNaor_constant_pos hn
  let L : ℝ≥0 := ⟨1000 * Real.log n / Real.log (Real.log n), hK.le⟩
  have hL : AbsLipExtendableWith.{u, v} X (L : ℝ) := absLipExtendableWith_of_card_le hn hX
  calc absLipExtConst.{u, v} X ≤ (L : ℝ≥0∞) := iInf₂_le L hL
    _ = ENNReal.ofReal (1000 * Real.log n / Real.log (Real.log n)) :=
        (ENNReal.ofReal_coe_nnreal (p := L)).symm

end LipschitzExtension
