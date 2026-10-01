/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.PointwiseLipschitz.Basic

/-!
# Global Lipschitz bounds from pointwise bounds off a closed set

This file proves Lemma 2.2 of [Basso2024] (the "great simplification", which is applied in the
proofs of all main theorems of the paper): let `X` be a Banach space and `f : A → Y` a
`1`-Lipschitz map defined on a closed subset `A ⊆ X`. Suppose `F` is an extension of `f` that is
continuous at every point of `A` and there exists `L ≥ 1` such that `Lip F(x) ≤ L` for every
`x ∈ X \ A`. Then `F` is `L`-Lipschitz.

Completeness is not needed: we prove the lemma for every real normed space `X`, directly along
segments. The version for length spaces, which is needed for Theorem 6.1 of [Basso2024] by item 5
of the errata [BassoClaude2026], is `IsLengthSpace.dist_le_of_lipAt_of_continuousAt`.

## Main statements

* `dist_le_of_lipAt_of_continuousAt`: Lemma 2.2 of [Basso2024] for real normed spaces.

## Proof outline

For `x ∉ A` and `a ∈ A`, let `x_s` be the first point of the segment `[x, a]` in `A` (it exists
since `A` is closed). For `t < s` the segment `[x, x_t]` avoids `A`, so
`d(F x, F x_t) ≤ L ‖x - x_t‖` by Lemma 2.1 along segments (`dist_le_of_lipAt_segment`); letting
`t → s` (continuity of `F` at `x_s`) gives `d(F x, F x_s) ≤ L ‖x - x_s‖`, and
`d(F x_s, F a) ≤ ‖x_s - a‖ ≤ L ‖x_s - a‖`. For general `x, y`: if the segment `[x, y]` meets `A`
in a point `w`, apply this to the pairs `x, w` and `y, w`; otherwise apply Lemma 2.1 to the whole
segment `[x, y]`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
-/

open Set Metric Filter Topology

namespace LipschitzExtension

/-- The special case of **Lemma 2.2** of [Basso2024] where the second point lies in `A`. -/
private theorem dist_le_of_lipAt_of_continuousAt_of_mem {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Y : Type*} [PseudoMetricSpace Y] {A : Set E} (hA : IsClosed A)
    {F : E → Y} (hFA : ∀ a ∈ A, ∀ b ∈ A, dist (F a) (F b) ≤ dist a b)
    (hcont : ∀ a ∈ A, ContinuousAt F a) {L : ℝ} (hL : 1 ≤ L) (hF : ∀ x ∉ A, LipAt F x L)
    (p q : E) (hq : q ∈ A) : dist (F p) (F q) ≤ L * dist p q := by
  by_cases hp : p ∈ A
  · exact (hFA p hp q hq).trans (le_mul_of_one_le_left dist_nonneg hL)
  -- the first point `x_s` of the segment `[p, q]` in `A`
  set S : Set ℝ := Icc 0 1 ∩ (fun t : ℝ ↦ AffineMap.lineMap p q t) ⁻¹' A with hS
  have hSc : IsClosed S := isClosed_Icc.inter (hA.preimage AffineMap.lineMap_continuous)
  have h1S : (1 : ℝ) ∈ S := ⟨⟨zero_le_one, le_rfl⟩, by simpa using hq⟩
  have hSne : S.Nonempty := ⟨1, h1S⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht ↦ ht.1.1⟩
  obtain ⟨s, hs⟩ : ∃ s, s = sInf S := ⟨_, rfl⟩
  have hsS : s ∈ S := hs ▸ hSc.csInf_mem hSne hSbdd
  have hs1 : s ≤ 1 := hs ▸ csInf_le hSbdd h1S
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le hsS.1.1 with h | h
    · exfalso
      apply hp
      have := hsS.2
      rw [← h] at this
      simpa using this
    · exact h
  have hbefore : ∀ t, 0 ≤ t → t < s → AffineMap.lineMap p q t ∉ A := by
    intro t ht0 hts htA
    have : s ≤ t := hs ▸ csInf_le hSbdd ⟨⟨ht0, by linarith⟩, htA⟩
    linarith
  have hxsA : AffineMap.lineMap p q s ∈ A := hsS.2
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  -- `d(F p, F x_t) ≤ L t ‖p - q‖` for `t < s`
  have hbound : ∀ t ∈ Ioo 0 s,
      dist (F p) (F (AffineMap.lineMap p q t)) ≤ L * (s * dist p q) := by
    intro t ht
    have hseg : ∀ z ∈ segment ℝ p (AffineMap.lineMap p q t), LipAt F z L := by
      intro z hz
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨t', ht', rfl⟩ := hz
      rw [AffineMap.lineMap_lineMap_right]
      apply hF
      apply hbefore
      · exact mul_nonneg ht'.1 ht.1.le
      · calc t' * t ≤ 1 * t := mul_le_mul_of_nonneg_right ht'.2 ht.1.le
          _ < s := by linarith [ht.2]
    have := dist_le_of_lipAt_segment hseg
    rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_pos ht.1] at this
    calc _ ≤ L * (t * dist p q) := this
      _ ≤ L * (s * dist p q) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht.2.le dist_nonneg) hL0
  -- let `t → s`
  have hlim : Tendsto (fun t : ℝ ↦ dist (F p) (F (AffineMap.lineMap p q t))) (𝓝[<] s)
      (𝓝 (dist (F p) (F (AffineMap.lineMap p q s)))) := by
    have h1 : Tendsto (fun t : ℝ ↦ AffineMap.lineMap p q t) (𝓝[<] s)
        (𝓝 (AffineMap.lineMap p q s)) :=
      ((AffineMap.lineMap_continuous (p := p) (q := q)).tendsto s).mono_left
        nhdsWithin_le_nhds
    exact tendsto_const_nhds.dist ((hcont _ hxsA).tendsto.comp h1)
  have h2 : dist (F p) (F (AffineMap.lineMap p q s)) ≤ L * (s * dist p q) :=
    le_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsLT hs0) hbound)
  have h3 : dist (F (AffineMap.lineMap p q s)) (F q) ≤ (1 - s) * dist p q := by
    refine (hFA _ hxsA q hq).trans (le_of_eq ?_)
    rw [dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  calc dist (F p) (F q) ≤ dist (F p) (F (AffineMap.lineMap p q s)) +
        dist (F (AffineMap.lineMap p q s)) (F q) := dist_triangle _ _ _
    _ ≤ L * (s * dist p q) + (1 - s) * dist p q := add_le_add h2 h3
    _ ≤ L * (s * dist p q) + L * ((1 - s) * dist p q) := by
        have : (1 - s) * dist p q ≤ L * ((1 - s) * dist p q) :=
          le_mul_of_one_le_left (mul_nonneg (by linarith) dist_nonneg) hL
        linarith
    _ = L * dist p q := by ring

/-- **Lemma 2.2** of [Basso2024] for real normed spaces: let `A ⊆ E` be closed and let `F : E → Y`
be `1`-Lipschitz on `A` and continuous at every point of `A`, with `Lip F(x) ≤ L` for all `x ∉ A`,
where `L ≥ 1`. Then `F` is `L`-Lipschitz. -/
theorem dist_le_of_lipAt_of_continuousAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y : Type*} [PseudoMetricSpace Y] {A : Set E} (hA : IsClosed A) {F : E → Y}
    (hFA : ∀ a ∈ A, ∀ b ∈ A, dist (F a) (F b) ≤ dist a b)
    (hcont : ∀ a ∈ A, ContinuousAt F a) {L : ℝ} (hL : 1 ≤ L) (hF : ∀ x ∉ A, LipAt F x L)
    (x y : E) : dist (F x) (F y) ≤ L * dist x y := by
  by_cases h : ∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x y t ∈ A
  · -- the segment `[x, y]` meets `A` at `w`: use the special case twice
    obtain ⟨t, ht, htA⟩ := h
    have h1 := dist_le_of_lipAt_of_continuousAt_of_mem hA hFA hcont hL hF x _ htA
    have h2 := dist_le_of_lipAt_of_continuousAt_of_mem hA hFA hcont hL hF y _ htA
    rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht.1] at h1
    rw [dist_right_lineMap, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])] at h2
    calc dist (F x) (F y) ≤ dist (F x) (F (AffineMap.lineMap x y t)) +
          dist (F (AffineMap.lineMap x y t)) (F y) := dist_triangle _ _ _
      _ ≤ L * (t * dist x y) + L * ((1 - t) * dist x y) := by
          rw [dist_comm (F (AffineMap.lineMap x y t))]
          exact add_le_add h1 h2
      _ = L * dist x y := by ring
  · -- the segment `[x, y]` avoids `A`: Lemma 2.1
    push Not at h
    apply dist_le_of_lipAt_segment
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact hF _ (h t ht)

end LipschitzExtension
