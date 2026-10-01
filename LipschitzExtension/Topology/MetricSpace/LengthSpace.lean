/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.PointwiseLipschitz.Lower

/-!
# Length spaces

A pseudometric space `X` is a *length space* (`IsLengthSpace X`) if any two points are joined by
continuous curves of length arbitrarily close to their distance. By item 5 of the errata
[BassoClaude2026], this is the condition under which the proof of Theorem 6.1 of [Basso2024]
works. Real normed spaces are length spaces, and so are Riemannian manifolds
(`isLengthSpace_of_isRiemannianManifold`, used for Theorem 1.3 of [Basso2024]).

This file proves Lemma 2.1 of [Basso2024] for quasiconvex spaces and for length spaces, and
Lemma 2.2 of [Basso2024] for length spaces.

## Main definitions

* `IsLengthSpace X`: for every `ε > 0`, any two points `x, y` of `X` are joined by a continuous
  curve of length at most `d(x, y) + ε`.

## Main statements

* `IsLengthSpace.isQuasiconvex`: a length space is `c`-quasiconvex for every `c > 1`.
* `isLengthSpace_normedSpace`: real normed spaces are length spaces.
* `dist_le_of_lipAt_of_isQuasiconvex`: Lemma 2.1 of [Basso2024]: if `X` is `c`-quasiconvex and
  `Lip f(x) ≤ L` for every `x`, then `f` is `c L`-Lipschitz (from Lemma 2.4 of
  Basso–Wenger–Young, `dist_le_of_lipLowerLE_of_isQuasiconvex`, since `lip f ≤ Lip f`).
* `IsLengthSpace.dist_le_of_lipLowerLE`: Lemma 2.1 for length spaces: if `lip f ≤ C` at every
  point, then `f` is `C`-Lipschitz.
* `IsLengthSpace.dist_le_of_lipAt_of_continuousAt`: Lemma 2.2 of [Basso2024] for length spaces
  (errata item 5): let `A ⊆ X` be closed and let `F : X → Y` be `1`-Lipschitz on `A`, continuous
  at every point of `A`, with `Lip F(x) ≤ L` for all `x ∉ A`, where `L ≥ 1`. Then `F` is
  `L`-Lipschitz.

## Proof outline

Lemma 2.1 for length spaces: apply `dist_le_of_lipLowerLE_curve` to curves from `x` to `y` of
length `≤ d(x, y) + ε` and let `ε → 0`.

Lemma 2.2 for length spaces: given `ε > 0` take a curve `γ` from `x` to `y` of length
`≤ d(x, y) + ε`. If it avoids `A`, apply Lemma 2.1 along `γ`. If `x ∉ A` and `y ∈ A`, let `γ(t₀)`
be the first point of `γ` in `A`; on `[0, t]` for `t < t₀` the curve avoids `A`, so Lemma 2.1
along the curve and the continuity of `F` at `γ(t₀)` give `d(F x, F γ(t₀)) ≤ L ℓ(γ|[0, t₀])`,
while `d(F γ(t₀), F y) ≤ d(γ(t₀), y) ≤ ℓ(γ|[t₀, 1])`; sum up and use `L ≥ 1`. In general, if `γ`
meets `A` at `γ(t)`, apply this special case to `x, γ(t)` and to `y, γ(t)`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
* G. Basso, S. Wenger and R. Young, *Undistorted fillings in subsets of metric spaces*, Adv. Math.
  423 (2023), Paper No. 109024
-/

open Set Metric Filter Topology

namespace LipschitzExtension

/-- `IsLengthSpace X`: the pseudometric space `X` is a length space, i.e. for all `x, y : X` and
every `ε > 0` there is a curve `γ : ℝ → X`, continuous on `[0, 1]`, with `γ 0 = x`, `γ 1 = y` and
length `eVariationOn γ [0, 1]` at most `d(x, y) + ε`. -/
def IsLengthSpace (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x y : X, ∀ ε > 0, ∃ γ : ℝ → X, ContinuousOn γ (Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧
    eVariationOn γ (Icc 0 1) ≤ ENNReal.ofReal (dist x y + ε)

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A length space is `c`-quasiconvex for every `c > 1`. -/
theorem IsLengthSpace.isQuasiconvex (hX : IsLengthSpace X) {c : ℝ} (hc : 1 < c) :
    IsQuasiconvex c X := by
  intro x y
  rcases (dist_nonneg (x := x) (y := y)).lt_or_eq with hpos | hzero
  · obtain ⟨γ, hγc, h0, h1, hv⟩ := hX x y ((c - 1) * dist x y) (mul_pos (sub_pos.2 hc) hpos)
    exact ⟨γ, hγc, h0, h1, hv.trans_eq (by congr 1; ring)⟩
  · -- `d(x, y) = 0` (possible with `x ≠ y` in a pseudometric space): a jump from `x` to `y`
    have hd : ∀ s t : ℝ, dist (if s = 1 then y else x) (if t = 1 then y else x) = 0 := by
      intro s t
      split_ifs <;> simp [← hzero, dist_comm]
    refine ⟨fun t ↦ if t = 1 then y else x, ?_, by simp, by simp, ?_⟩
    · exact (LipschitzWith.of_dist_le_mul (K := 0) fun s t ↦ by
        simp [hd s t]).continuous.continuousOn
    · rw [(eVariationOn.eq_zero_iff _).2 fun s _ t _ ↦ by
        rw [edist_dist, hd s t, ENNReal.ofReal_zero]]
      exact zero_le

/-- Real normed spaces are length spaces. -/
theorem isLengthSpace_normedSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsLengthSpace E := by
  intro x y ε hε
  obtain ⟨γ, hγc, h0, h1, hv⟩ := isQuasiconvex_normedSpace E x y
  exact ⟨γ, hγc, h0, h1, hv.trans (ENNReal.ofReal_le_ofReal (by linarith))⟩

/-- **Lemma 2.1** of [Basso2024]: on a `c`-quasiconvex space, a map with `Lip f ≤ L` at every
point (`L ≥ 0`) is `c L`-Lipschitz. -/
theorem dist_le_of_lipAt_of_isQuasiconvex {c : ℝ} (hX : IsQuasiconvex c X) {f : X → Y} {L : ℝ}
    (hL : 0 ≤ L) (hf : ∀ x, LipAt f x L) (x y : X) :
    dist (f x) (f y) ≤ c * L * dist x y := by
  calc dist (f x) (f y) ≤ L * c * dist x y :=
        dist_le_of_lipLowerLE_of_isQuasiconvex hX hL (fun x ↦ (hf x).lipLowerLE hL) x y
    _ = c * L * dist x y := by ring

/-- In a length space, a bound `a ≤ C ℓ(γ)` for all continuous curves `γ` of finite length from
`x` to `y` implies `a ≤ C d(x, y)`. -/
private theorem IsLengthSpace.le_mul_dist_of_forall_curve (hX : IsLengthSpace X) {C a : ℝ}
    (hC : 0 ≤ C) {x y : X}
    (h : ∀ γ : ℝ → X, ContinuousOn γ (Icc 0 1) → γ 0 = x → γ 1 = y →
      eVariationOn γ (Icc 0 1) ≠ ⊤ → a ≤ C * (eVariationOn γ (Icc 0 1)).toReal) :
    a ≤ C * dist x y := by
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  obtain ⟨γ, hγc, h0, h1, hv⟩ := hX x y (δ / (C + 1)) (by positivity)
  have hfin : eVariationOn γ (Icc 0 1) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv
  have hv' : (eVariationOn γ (Icc 0 1)).toReal ≤ dist x y + δ / (C + 1) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hCδ : C * (δ / (C + 1)) ≤ δ := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  calc a ≤ C * (eVariationOn γ (Icc 0 1)).toReal := h γ hγc h0 h1 hfin
    _ ≤ C * (dist x y + δ / (C + 1)) := by gcongr
    _ ≤ C * dist x y + δ := by rw [mul_add]; linarith

/-- **Lemma 2.1** of [Basso2024] for length spaces: a map with `lip f ≤ C` at every point
(`C ≥ 0`) is `C`-Lipschitz. -/
theorem IsLengthSpace.dist_le_of_lipLowerLE (hX : IsLengthSpace X) {f : X → Y} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, LipLowerLE f x C) (x y : X) :
    dist (f x) (f y) ≤ C * dist x y :=
  hX.le_mul_dist_of_forall_curve hC fun γ hγc h0 h1 hfin ↦ by
    have := dist_le_of_lipLowerLE_curve hC zero_le_one hγc hfin (fun t _ ↦ hf (γ t))
    rwa [h0, h1] at this

/-- Along a continuous curve `γ : [a, b] → X` of finite length with `lip F ≤ L` at the points
`γ t`, `t ∈ [a, b)`, and `F` continuous at `γ b`: `d(F(γ a), F(γ b)) ≤ L ℓ(γ)`. -/
private theorem dist_le_of_lipLowerLE_curve_of_continuousAt {F : X → Y} {L : ℝ} (hL : 0 ≤ L)
    {γ : ℝ → X} {a b : ℝ} (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hlen : eVariationOn γ (Icc a b) ≠ ⊤) (hF : ∀ t ∈ Ico a b, LipLowerLE F (γ t) L)
    (hb : ContinuousAt F (γ b)) :
    dist (F (γ a)) (F (γ b)) ≤ L * (eVariationOn γ (Icc a b)).toReal := by
  rcases hab.eq_or_lt with rfl | hab'
  · rw [dist_self]
    positivity
  -- the bound on `[a, t]` for `t < b`
  have hbound : ∀ t ∈ Ico a b,
      dist (F (γ a)) (F (γ t)) ≤ L * (eVariationOn γ (Icc a b)).toReal := by
    intro t ht
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2.le
    have hfin : eVariationOn γ (Icc a t) ≠ ⊤ := ne_top_of_le_ne_top hlen (eVariationOn.mono γ hsub)
    calc dist (F (γ a)) (F (γ t)) ≤ L * (eVariationOn γ (Icc a t)).toReal :=
          dist_le_of_lipLowerLE_curve hL ht.1 (hγ.mono hsub) hfin
            (fun s hs ↦ hF s ⟨hs.1, hs.2.trans_lt ht.2⟩)
      _ ≤ L * (eVariationOn γ (Icc a b)).toReal := by
          gcongr
          exact eVariationOn.mono γ hsub
  -- let `t → b` from the left
  have hlim : Tendsto (fun t ↦ dist (F (γ a)) (F (γ t))) (𝓝[<] b)
      (𝓝 (dist (F (γ a)) (F (γ b)))) := by
    have h1 : Tendsto γ (𝓝[<] b) (𝓝 (γ b)) := by
      refine (hγ b ⟨hab, le_rfl⟩).tendsto.mono_left ?_
      rw [← nhdsWithin_Ico_eq_nhdsLT hab']
      exact nhdsWithin_mono _ Ico_subset_Icc_self
    exact tendsto_const_nhds.dist (hb.tendsto.comp h1)
  exact le_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsLT hab') fun t ht ↦
    hbound t ⟨ht.1.le, ht.2⟩)

/-- The special case of **Lemma 2.2** of [Basso2024] for length spaces where the second point lies
in `A`. -/
private theorem IsLengthSpace.dist_le_of_lipAt_of_continuousAt_of_mem (hX : IsLengthSpace X)
    {A : Set X} (hA : IsClosed A) {F : X → Y}
    (hFA : ∀ a ∈ A, ∀ b ∈ A, dist (F a) (F b) ≤ dist a b)
    (hcont : ∀ a ∈ A, ContinuousAt F a) {L : ℝ} (hL : 1 ≤ L) (hF : ∀ x ∉ A, LipAt F x L)
    (p q : X) (hq : q ∈ A) : dist (F p) (F q) ≤ L * dist p q := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  by_cases hp : p ∈ A
  · exact (hFA p hp q hq).trans (le_mul_of_one_le_left dist_nonneg hL)
  refine hX.le_mul_dist_of_forall_curve hL0 fun γ hγc h0 h1 hfin ↦ ?_
  -- the first time `t₀` at which `γ` meets `A`
  set S : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | γ t ∈ A}
  have hSc : IsClosed S := hγc.preimage_isClosed_of_isClosed isClosed_Icc hA
  have h1S : (1 : ℝ) ∈ S := ⟨⟨zero_le_one, le_rfl⟩, h1 ▸ hq⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht ↦ ht.1.1⟩
  set t₀ := sInf S
  have ht₀S : t₀ ∈ S := hSc.csInf_mem ⟨1, h1S⟩ hSbdd
  have hbefore : ∀ t ∈ Ico 0 t₀, γ t ∉ A := fun t ht htA ↦ by
    have := csInf_le hSbdd ⟨⟨ht.1, ht.2.le.trans ht₀S.1.2⟩, htA⟩
    linarith [ht.2]
  have hsplit := eVariationOn.Icc_add_Icc γ (s := univ) ht₀S.1.1 ht₀S.1.2 (mem_univ _)
  simp only [univ_inter] at hsplit
  have hfin1 : eVariationOn γ (Icc 0 t₀) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (eVariationOn.mono γ (Icc_subset_Icc_right ht₀S.1.2))
  have hfin2 : eVariationOn γ (Icc t₀ 1) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (eVariationOn.mono γ (Icc_subset_Icc_left ht₀S.1.1))
  have e1 : dist (F p) (F (γ t₀)) ≤ L * (eVariationOn γ (Icc 0 t₀)).toReal := by
    have := dist_le_of_lipLowerLE_curve_of_continuousAt hL0 ht₀S.1.1
      (hγc.mono (Icc_subset_Icc_right ht₀S.1.2)) hfin1
      (fun t ht ↦ (hF _ (hbefore t ht)).lipLowerLE hL0) (hcont _ ht₀S.2)
    rwa [h0] at this
  have e2 : dist (F (γ t₀)) (F q) ≤ L * (eVariationOn γ (Icc t₀ 1)).toReal := by
    calc dist (F (γ t₀)) (F q) ≤ dist (γ t₀) (γ 1) := h1 ▸ hFA _ ht₀S.2 q hq
      _ ≤ (eVariationOn γ (Icc t₀ 1)).toReal :=
          BoundedVariationOn.dist_le hfin2 ⟨le_rfl, ht₀S.1.2⟩ ⟨ht₀S.1.2, le_rfl⟩
      _ ≤ L * (eVariationOn γ (Icc t₀ 1)).toReal :=
          le_mul_of_one_le_left ENNReal.toReal_nonneg hL
  calc dist (F p) (F q) ≤ dist (F p) (F (γ t₀)) + dist (F (γ t₀)) (F q) := dist_triangle _ _ _
    _ ≤ L * (eVariationOn γ (Icc 0 t₀)).toReal + L * (eVariationOn γ (Icc t₀ 1)).toReal :=
        add_le_add e1 e2
    _ = L * (eVariationOn γ (Icc 0 1)).toReal := by
        rw [← mul_add, ← ENNReal.toReal_add hfin1 hfin2, hsplit]

/-- **Lemma 2.2** of [Basso2024] for length spaces (errata item 5): a map which is `1`-Lipschitz
on a closed set `A`, continuous at the points of `A` and has `Lip F ≤ L` off `A`, `L ≥ 1`, is
`L`-Lipschitz. -/
theorem IsLengthSpace.dist_le_of_lipAt_of_continuousAt (hX : IsLengthSpace X) {A : Set X}
    (hA : IsClosed A) {F : X → Y} (hFA : ∀ a ∈ A, ∀ b ∈ A, dist (F a) (F b) ≤ dist a b)
    (hcont : ∀ a ∈ A, ContinuousAt F a) {L : ℝ} (hL : 1 ≤ L) (hF : ∀ x ∉ A, LipAt F x L)
    (x y : X) : dist (F x) (F y) ≤ L * dist x y := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  refine hX.le_mul_dist_of_forall_curve hL0 fun γ hγc h0 h1 hfin ↦ ?_
  by_cases h : ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ A
  · -- the curve meets `A` at `γ t`: use the special case twice
    obtain ⟨t, ht, htA⟩ := h
    have e1 := hX.dist_le_of_lipAt_of_continuousAt_of_mem hA hFA hcont hL hF x (γ t) htA
    have e2 := hX.dist_le_of_lipAt_of_continuousAt_of_mem hA hFA hcont hL hF y (γ t) htA
    have hsplit := eVariationOn.Icc_add_Icc γ (s := univ) ht.1 ht.2 (mem_univ _)
    simp only [univ_inter] at hsplit
    have hfin1 : eVariationOn γ (Icc 0 t) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (eVariationOn.mono γ (Icc_subset_Icc_right ht.2))
    have hfin2 : eVariationOn γ (Icc t 1) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (eVariationOn.mono γ (Icc_subset_Icc_left ht.1))
    have d1 : dist x (γ t) ≤ (eVariationOn γ (Icc 0 t)).toReal := by
      rw [← h0]
      exact BoundedVariationOn.dist_le hfin1 ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩
    have d2 : dist y (γ t) ≤ (eVariationOn γ (Icc t 1)).toReal := by
      rw [← h1, dist_comm]
      exact BoundedVariationOn.dist_le hfin2 ⟨le_rfl, ht.2⟩ ⟨ht.2, le_rfl⟩
    calc dist (F x) (F y) ≤ dist (F x) (F (γ t)) + dist (F y) (F (γ t)) :=
          dist_triangle_right _ _ _
      _ ≤ L * dist x (γ t) + L * dist y (γ t) := add_le_add e1 e2
      _ ≤ L * (eVariationOn γ (Icc 0 t)).toReal + L * (eVariationOn γ (Icc t 1)).toReal := by
          gcongr
      _ = L * (eVariationOn γ (Icc 0 1)).toReal := by
          rw [← mul_add, ← ENNReal.toReal_add hfin1 hfin2, hsplit]
  · -- the curve avoids `A`: Lemma 2.1 along the curve
    push Not at h
    have := dist_le_of_lipLowerLE_curve hL0 zero_le_one hγc hfin
      (fun t ht ↦ (hF _ (h t ht)).lipLowerLE hL0)
    rwa [h0, h1] at this

end LipschitzExtension
