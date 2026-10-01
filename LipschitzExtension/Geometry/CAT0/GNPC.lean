/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Geometry.CAT0.Defs
import LipschitzExtension.Topology.MetricSpace.Barycenter.Construction

/-!
# CAT(0) spaces are of generalized non-positive curvature

Section 1.5 of [Basso2024] notes, in the discussion after Definition 1.3, that CAT(0) spaces are
spaces of generalized non-positive curvature (gNPC), with `m(x, y)` the unique midpoint of `x` and
`y`, and that "any complete gNPC space is a geodesic metric space". This file proves both facts.

Consequently, Theorem 1.2 of [Basso2024] applies to complete CAT(0) targets
(`LipschitzOnWith.extend_nagata_isCAT0`): if `A ⊆ X` satisfies `Nagata(n, c)` and `Y` is a
complete CAT(0) space, then every `1`-Lipschitz map `f : A → Y` has a
`1000 (c + 1) log₂(n + 2)`-Lipschitz extension `F : X → Y`. This is the setting of the question
of Brudnyi and Brudnyi discussed after Theorem 1.2 of [Basso2024] (answered by Naor and
Silberman with a bound `O(c n³)`), and the bound is sublinear in `n` and `c`.

## Main statements

* `IsCAT0.isGNPC`: CAT(0) spaces are of generalized non-positive curvature.
* `IsGNPC.isGeodesicSpace`: complete gNPC spaces are geodesic.

## Proof outline

*CAT(0) ⇒ gNPC.* Midpoints are unique: if `m` is the midpoint of a geodesic from `x` to `y` and
`m'` is any midpoint of `x` and `y`, then the CN inequality (`IsCAT0.dist_sq_le`) gives
`d(m', m)² ≤ ½ d(m', x)² + ½ d(m', y)² - ¼ d(x, y)² = 0`. Let `m(x, y)` be the midpoint of `x`
and `y`; then `m` is symmetric and `m(y, y) = y`. For `x, y, z`, take geodesics from `x` to `y`,
from `y` to `z` and from `z` to `x` (which pass through the midpoints) and a comparison triangle
`x̄, ȳ, z̄`. The CAT(0) inequality for the midpoints of the sides `[x, y]` and `[z, x]` gives
`d(m(x, y), m(x, z)) ≤ |(x̄ + ȳ)/2 - (z̄ + x̄)/2| = d(y, z)/2`.

*gNPC ⇒ geodesic.* A complete gNPC space has a conical bicombing `σ`
(`isGNPC_iff_nonempty_conicalBicombing`), and `t ↦ σ(x, y, t/d(x, y))` is a geodesic from `x` to
`y`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* M. R. Bridson and A. Haefliger, *Metric spaces of non-positive curvature*, Grundlehren Math.
  Wiss. 319, Springer, Berlin, 1999
-/

open Set Metric

namespace LipschitzExtension

universe u v

/-- Midpoints in CAT(0) spaces are unique: every midpoint `m` of `x` and `y` is the midpoint
`γ(d(x, y)/2)` of any geodesic `γ` from `x` to `y` (by the CN inequality). -/
private lemma IsCAT0.eq_of_dist_eq_half {X : Type*} [MetricSpace X] (hX : IsCAT0 X)
    {γ : ℝ → X} {x y : X} (hγ : IsGeodesic γ x y) {m : X} (h1 : dist x m = dist x y / 2)
    (h2 : dist m y = dist x y / 2) : m = γ (1 / 2 * dist x y) := by
  have h := hX.dist_sq_le hγ m (t := 1 / 2) ⟨by norm_num, by norm_num⟩
  rw [dist_comm m x, h1, h2] at h
  have h0 : dist m (γ (1 / 2 * dist x y)) ^ 2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  exact dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)

/-- CAT(0) spaces are spaces of generalized non-positive curvature, with `m(x, y)` the unique
midpoint of `x` and `y` (Section 1.5 of [Basso2024]). -/
theorem IsCAT0.isGNPC {X : Type*} [MetricSpace X] (hX : IsCAT0 X) : IsGNPC X := by
  choose m hm1 hm2 _ using hX.exists_midpoint
  -- two midpoints of `x` and `y` coincide
  have huniq : ∀ {x y m₁ m₂ : X}, dist x m₁ = dist x y / 2 → dist m₁ y = dist x y / 2 →
      dist x m₂ = dist x y / 2 → dist m₂ y = dist x y / 2 → m₁ = m₂ := by
    intro x y m₁ m₂ h₁ h₂ h₃ h₄
    obtain ⟨γ, hγ⟩ := hX.1 x y
    rw [hX.eq_of_dist_eq_half hγ h₁ h₂, hX.eq_of_dist_eq_half hγ h₃ h₄]
  -- `m y x` is a midpoint of `x` and `y`
  have hsymm1 : ∀ x y, dist x (m y x) = dist x y / 2 := by
    intro x y
    rw [dist_comm, hm2 y x, dist_comm]
  have hsymm2 : ∀ x y, dist (m y x) y = dist x y / 2 := by
    intro x y
    rw [dist_comm, hm1 y x, dist_comm]
  refine ⟨m, fun x y ↦ huniq (hm1 x y) (hm2 x y) (hsymm1 x y) (hsymm2 x y), fun y ↦ ?_,
    fun x y z ↦ ?_⟩
  · have := hm1 y y
    rw [dist_self, zero_div] at this
    exact (dist_eq_zero.1 this).symm
  · -- the geodesic triangle `x, y, z` and a comparison triangle
    obtain ⟨γ₀, h₀⟩ := hX.1 x y
    obtain ⟨γ₁, h₁⟩ := hX.1 y z
    obtain ⟨γ₂, h₂⟩ := hX.1 z x
    obtain ⟨p, hp⟩ := exists_comparisonTriangle ![x, y, z]
    have hgeo : ∀ i, IsGeodesic (![γ₀, γ₁, γ₂] i) (![x, y, z] i) (![x, y, z] (i + 1)) := by
      intro i
      fin_cases i
      · exact h₀
      · exact h₁
      · exact h₂
    have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    -- compare the midpoints of the sides `[x, y]` and `[z, x]`
    have h := hX.2 ![x, y, z] ![γ₀, γ₁, γ₂] hgeo p hp 0 2 (1 / 2) hhalf (1 / 2) hhalf
    simp only [Fin.isValue, Matrix.cons_val_zero, zero_add, Matrix.cons_val_one,
      Matrix.cons_val, Fin.reduceAdd] at h
    have e₀ : γ₀ (1 / 2 * dist x y) = m x y :=
      (hX.eq_of_dist_eq_half h₀ (hm1 x y) (hm2 x y)).symm
    have e₂ : γ₂ (1 / 2 * dist z x) = m x z :=
      (hX.eq_of_dist_eq_half h₂ (hsymm1 z x) (hsymm2 z x)).symm
    rw [e₀, e₂] at h
    refine h.trans (le_of_eq ?_)
    -- the Euclidean computation `|(x̄ + ȳ)/2 - (z̄ + x̄)/2| = |ȳ - z̄|/2`
    have h12 := hp 1 2
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val] at h12
    rw [dist_eq_norm, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    have e : (1 - 1 / 2 : ℝ) • p 0 + (1 / 2 : ℝ) • p 1 - ((1 - 1 / 2 : ℝ) • p 2 + (1 / 2 : ℝ) • p 0)
        = (1 / 2 : ℝ) • (p 1 - p 2) := by
      module
    rw [e, norm_smul, ← dist_eq_norm, h12, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    ring

/-- Complete spaces of generalized non-positive curvature are geodesic (Section 1.5 of
[Basso2024]). -/
theorem IsGNPC.isGeodesicSpace {X : Type*} [MetricSpace X] [CompleteSpace X] (hX : IsGNPC X) :
    IsGeodesicSpace X := by
  obtain ⟨σ⟩ := isGNPC_iff_nonempty_conicalBicombing.1 hX
  intro x y
  rcases eq_or_ne x y with rfl | hxy
  · refine ⟨fun _ ↦ x, rfl, rfl, fun s hs t ht ↦ ?_⟩
    rw [dist_self] at hs ht
    rw [le_antisymm hs.2 hs.1, le_antisymm ht.2 ht.1, dist_self, sub_self, abs_zero]
  · have hd : 0 < dist x y := dist_pos.2 hxy
    refine ⟨fun t ↦ σ x y (t / dist x y), ?_, ?_, fun s hs t ht ↦ ?_⟩
    · simp only [zero_div]
      exact σ.toFun_zero x y
    · simp only [div_self hd.ne']
      exact σ.toFun_one x y
    · have hs' : s / dist x y ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hs.1 hd.le, (div_le_one hd).2 hs.2⟩
      have ht' : t / dist x y ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg ht.1 hd.le, (div_le_one hd).2 ht.2⟩
      have h := σ.dist_toFun_toFun x y hs' ht'
      change dist (σ x y (s / dist x y)) (σ x y (t / dist x y)) = |s - t|
      rw [h, ← sub_div, abs_div, abs_of_pos hd, div_mul_cancel₀ _ hd.ne']

end LipschitzExtension
