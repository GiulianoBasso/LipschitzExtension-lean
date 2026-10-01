/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Lipschitz `n`-connected spaces

This file defines Lipschitz `n`-connectedness, Definition 1.2 of [Basso2024], which goes back to
Lang and Schlichenmaier: a metric space `Y` is *Lipschitz `n`-connected with constant `λ`*, or
satisfies the condition `LC(n, λ)`, if for every `0 ≤ m ≤ n` every `L`-Lipschitz map `f : S^m → Y`
admits a `λ L`-Lipschitz extension `F : B^(m+1) → Y`. Here `B^(m+1) ⊆ ℝ^(m+1)` is the Euclidean
unit ball and `S^m = ∂B^(m+1)` is the unit sphere.

We also define the condition `LC(B^(n+1), λ)` of Section 7 of [Basso2024], which concerns a single
dimension: every `L`-Lipschitz map `f : S^n → Y` admits a `λ L`-Lipschitz extension
`F : B^(n+1) → Y`. Thus `LC(n, λ)` holds if and only if `LC(B^(m+1), λ)` holds for all `m ≤ n`.

## Main definitions

* `LipschitzConnected n Λ Y`: `Y` satisfies `LC(n, Λ)` (Definition 1.2 of [Basso2024]).
* `LCBall n Λ Y`: `Y` satisfies `LC(B^(n+1), Λ)`.

## Main statements

* `lipschitzConnected_iff_forall_lcBall`: `LC(n, Λ)` holds if and only if `LC(B^(m+1), Λ)` holds
  for all `m ≤ n`.
* `LipschitzConnected.mono`, `LCBall.mono`: monotonicity in `n` and in `Λ`, respectively.
* `LipschitzConnected.subsingleton`: if `Λ < 1`, then `LC(n, Λ)` (already `LC(0, Λ)`) forces `Y`
  to have at most one point.
* `LipschitzConnected.extend_sphere`: a uniform version of `LC(n, Λ)` for the spheres of any
  center and any positive radius in any real inner product space of dimension `m + 1 ≤ n + 1`, in
  which one extension works simultaneously for all admissible Lipschitz constants.

## Implementation notes

The maps are defined on the whole space `EuclideanSpace ℝ (Fin (m + 1))`, and the Lipschitz
conditions are only imposed on the unit sphere and on the closed unit ball, respectively. A
Lipschitz constant is a real number `L ≥ 0`, and "`g` is `L`-Lipschitz on `S`" is written as
`dist (g x) (g y) ≤ L * dist x y` for all `x, y ∈ S`.

`LipschitzConnected.extend_sphere` is proved by applying the definition to the optimal Lipschitz
constant, which is attained.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* U. Lang and T. Schlichenmaier, *Nagata dimension, quasisymmetric embeddings, and Lipschitz
  extensions*, Int. Math. Res. Not. 2005 (2005), no. 58, 3625–3655
-/

open Set Metric

namespace LipschitzExtension

/-- `LipschitzConnected n Λ Y`: `Y` is *Lipschitz `n`-connected with constant `Λ`*, i.e. it
satisfies `LC(n, Λ)` (Definition 1.2 of [Basso2024]). For every `m ≤ n`, every map `g` which is
`L`-Lipschitz on the unit sphere `S^m ⊆ ℝ^(m+1)` agrees on `S^m` with a map `G` which is
`Λ L`-Lipschitz on the closed unit ball `B^(m+1)`. -/
def LipschitzConnected (n : ℕ) (Λ : ℝ) (Y : Type*) [PseudoMetricSpace Y] : Prop :=
  ∀ m ≤ n, ∀ L : ℝ, 0 ≤ L → ∀ g : EuclideanSpace ℝ (Fin (m + 1)) → Y,
    (∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
      ∀ y ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, dist (g x) (g y) ≤ L * dist x y) →
    ∃ G : EuclideanSpace ℝ (Fin (m + 1)) → Y,
      (∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, G x = g x) ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
        ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
          dist (G x) (G y) ≤ Λ * L * dist x y

variable {Y : Type*}

/-- `LC(n, Λ)` implies `LC(n', Λ)` for `n' ≤ n`. -/
theorem LipschitzConnected.mono [PseudoMetricSpace Y] {n n' : ℕ} {Λ : ℝ}
    (h : LipschitzConnected n Λ Y) (hn : n' ≤ n) : LipschitzConnected n' Λ Y :=
  fun m hm ↦ h m (hm.trans hn)

/-- If `Λ < 1`, then `LC(n, Λ)` forces `Y` to have at most one point: already `LC(0, Λ)` applied
to a map sending the two points of `S⁰` to `y₁` and `y₂` gives `d(y₁, y₂) ≤ Λ d(y₁, y₂)`. -/
theorem LipschitzConnected.subsingleton [MetricSpace Y] {n : ℕ} {Λ : ℝ}
    (h : LipschitzConnected n Λ Y) (hΛ : Λ < 1) : Subsingleton Y := by
  refine ⟨fun y₁ y₂ ↦ ?_⟩
  classical
  -- the sphere `S⁰ = {±e₀}` of `ℝ¹`
  have hdist : ∀ x y : EuclideanSpace ℝ (Fin (0 + 1)), dist x y = |x 0 - y 0| := by
    intro x y
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.dist_eq, sq_abs, Real.sqrt_sq_eq_abs]
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin (0 + 1)), ‖x‖ = |x 0| := by
    intro x
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  have hsph : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (0 + 1))) 1, x 0 = 1 ∨ x 0 = -1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, hnorm] at hx
    exact eq_or_eq_neg_of_abs_eq hx
  let g : EuclideanSpace ℝ (Fin (0 + 1)) → Y := fun x ↦ if 0 ≤ x 0 then y₁ else y₂
  obtain ⟨G, hG, hGL⟩ := h 0 (Nat.zero_le n) (dist y₁ y₂ / 2) (by positivity) g (by
    intro x hx y hy
    have hxy := hdist x y
    rcases hsph x hx with h1 | h1 <;> rcases hsph y hy with h2 | h2 <;>
      simp only [g, h1, h2, hxy] <;> norm_num [dist_comm y₂ y₁])
  let e : EuclideanSpace ℝ (Fin (0 + 1)) := WithLp.toLp 2 (fun _ ↦ 1)
  have he0 : e 0 = 1 := rfl
  have hne0 : (-e) 0 = -1 := rfl
  have he : e ∈ sphere (0 : EuclideanSpace ℝ (Fin (0 + 1))) 1 := by
    rw [mem_sphere_zero_iff_norm, hnorm, he0, abs_one]
  have hne : -e ∈ sphere (0 : EuclideanSpace ℝ (Fin (0 + 1))) 1 := by
    rw [mem_sphere_zero_iff_norm, hnorm, hne0, abs_neg, abs_one]
  have key := hGL e (sphere_subset_closedBall he) (-e) (sphere_subset_closedBall hne)
  rw [hG e he, hG (-e) hne, hdist, he0, hne0] at key
  simp only [g, he0, hne0] at key
  norm_num at key
  have hd : dist y₁ y₂ ≤ 0 := by nlinarith [dist_nonneg (x := y₁) (y := y₂)]
  exact dist_le_zero.mp hd

/-- `LCBall n Λ Y`: `Y` satisfies the condition `LC(B^(n+1), Λ)` of Section 7 of [Basso2024],
i.e. every `L`-Lipschitz map on the unit sphere `S^n ⊆ ℝ^(n+1)` has a `Λ L`-Lipschitz extension to
the closed unit ball `B^(n+1)`. -/
def LCBall (n : ℕ) (Λ : ℝ) (Y : Type*) [PseudoMetricSpace Y] : Prop :=
  ∀ L : ℝ, 0 ≤ L → ∀ g : EuclideanSpace ℝ (Fin (n + 1)) → Y,
    (∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      ∀ y ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, dist (g x) (g y) ≤ L * dist x y) →
    ∃ G : EuclideanSpace ℝ (Fin (n + 1)) → Y,
      (∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, G x = g x) ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
          dist (G x) (G y) ≤ Λ * L * dist x y

/-- `LC(n, Λ)` holds if and only if `LC(B^(m+1), Λ)` holds for all `m ≤ n`. -/
theorem lipschitzConnected_iff_forall_lcBall {n : ℕ} {Λ : ℝ} {Y : Type*} [PseudoMetricSpace Y] :
    LipschitzConnected n Λ Y ↔ ∀ m ≤ n, LCBall m Λ Y := by
  exact Iff.rfl

/-- `LC(B^(n+1), Λ)` implies `LC(B^(n+1), Λ')` for `Λ ≤ Λ'`. -/
theorem LCBall.mono {n : ℕ} {Λ Λ' : ℝ} {Y : Type*} [PseudoMetricSpace Y] (h : LCBall n Λ Y)
    (hΛ : Λ ≤ Λ') : LCBall n Λ' Y := by
  intro L hL g hg
  obtain ⟨G, hGg, hG⟩ := h L hL g hg
  refine ⟨G, hGg, fun x hx y hy ↦ (hG x hx y hy).trans ?_⟩
  gcongr

/-- **Uniform `LC` on spheres of finite-dimensional inner product spaces.** If `Y` satisfies
`LC(n, Λ)` with `Λ ≥ 0`, `m ≤ n` and `W` is a real inner product space of dimension `m + 1`, then
for every sphere `S(c, ρ)` of `W` with `ρ > 0` and every map `g : W → Y` there is `G : W → Y`
which agrees with `g` on `S(c, ρ)` and is `Λ L`-Lipschitz on the closed ball `B(c, ρ)` whenever `g`
is `L`-Lipschitz on `S(c, ρ)`. The extension `G` does not depend on `L`: if `g` is Lipschitz on
`S(c, ρ)`, it is obtained from `LC(n, Λ)` for the optimal Lipschitz constant of `g`, which is
attained. -/
theorem LipschitzConnected.extend_sphere [PseudoMetricSpace Y] {n : ℕ} {Λ : ℝ}
    (h : LipschitzConnected n Λ Y) (hΛ : 0 ≤ Λ) {m : ℕ} (hm : m ≤ n) {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (hW : Module.finrank ℝ W = m + 1) (c : W) {ρ : ℝ} (hρ : 0 < ρ) (g : W → Y) :
    ∃ G : W → Y, (∀ x ∈ sphere c ρ, G x = g x) ∧
      ∀ L : ℝ, 0 ≤ L → (∀ x ∈ sphere c ρ, ∀ y ∈ sphere c ρ, dist (g x) (g y) ≤ L * dist x y) →
        ∀ x ∈ closedBall c ρ, ∀ y ∈ closedBall c ρ, dist (G x) (G y) ≤ Λ * L * dist x y := by
  classical
  -- the set of admissible Lipschitz constants of `g` on the sphere
  set S : Set ℝ := {L | 0 ≤ L ∧ ∀ x ∈ sphere c ρ, ∀ y ∈ sphere c ρ,
    dist (g x) (g y) ≤ L * dist x y} with hS_def
  by_cases hS : S.Nonempty
  swap
  · exact ⟨g, fun _ _ ↦ rfl, fun L hL hLip ↦ absurd ⟨L, hL, hLip⟩ hS⟩
  -- the optimal Lipschitz constant `L₀ = inf S` is admissible
  have hbdd : BddBelow S := ⟨0, fun L hL ↦ hL.1⟩
  set L₀ := sInf S with hL₀
  have hL₀nn : 0 ≤ L₀ := le_csInf hS fun L hL ↦ hL.1
  have hL₀lip : ∀ x ∈ sphere c ρ, ∀ y ∈ sphere c ρ, dist (g x) (g y) ≤ L₀ * dist x y := by
    intro x hx y hy
    rcases (dist_nonneg : 0 ≤ dist x y).eq_or_lt with hd | hd
    · obtain ⟨L, hL⟩ := hS
      have := hL.2 x hx y hy
      rw [← hd, mul_zero] at this ⊢
      exact this
    · rw [← div_le_iff₀ hd]
      exact le_csInf hS fun L hL ↦ (div_le_iff₀ hd).mpr (hL.2 x hx y hy)
  have hL₀le : ∀ L ∈ S, L₀ ≤ L := fun L hL ↦ csInf_le hbdd hL
  -- transfer to the unit sphere of `ℝ^(m+1)`
  let e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    ((stdOrthonormalBasis ℝ W).reindex (finCongr hW)).repr
  let φ : EuclideanSpace ℝ (Fin (m + 1)) → W := fun u ↦ c + ρ • e.symm u
  let ψ : W → EuclideanSpace ℝ (Fin (m + 1)) := fun x ↦ e (ρ⁻¹ • (x - c))
  have hρ' : ρ ≠ 0 := hρ.ne'
  have hφψ : ∀ x, φ (ψ x) = x := by
    intro x
    simp only [φ, ψ, LinearIsometryEquiv.symm_apply_apply, smul_smul, mul_inv_cancel₀ hρ',
      one_smul, add_sub_cancel]
  have hdistφ : ∀ u v, dist (φ u) (φ v) = ρ * dist u v := by
    intro u v
    simp only [φ, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ,
      LinearIsometryEquiv.dist_map]
  have hdistψ : ∀ x y, dist (ψ x) (ψ y) = ρ⁻¹ * dist x y := by
    intro x y
    simp only [ψ, LinearIsometryEquiv.dist_map, dist_smul₀, norm_inv, Real.norm_eq_abs,
      abs_of_pos hρ, dist_sub_right]
  have hnormψ : ∀ x, ‖ψ x‖ = ρ⁻¹ * dist x c := by
    intro x
    simp only [ψ, LinearIsometryEquiv.norm_map, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hρ, dist_eq_norm]
  have hψsph : ∀ x ∈ sphere c ρ, ψ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, hnormψ, mem_sphere.mp hx, inv_mul_cancel₀ hρ']
  have hψball : ∀ x ∈ closedBall c ρ,
      ψ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff, hnormψ, inv_mul_le_iff₀ hρ, mul_one]
    exact mem_closedBall.mp hx
  have hφsph : ∀ u ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, φ u ∈ sphere c ρ := by
    intro u hu
    rw [mem_sphere, dist_eq_norm]
    simp only [φ, add_sub_cancel_left, norm_smul, LinearIsometryEquiv.norm_map,
      Real.norm_eq_abs, abs_of_pos hρ]
    rw [mem_sphere_zero_iff_norm.mp hu, mul_one]
  obtain ⟨G', hG'eq, hG'lip⟩ := h m hm (L₀ * ρ) (mul_nonneg hL₀nn hρ.le) (g ∘ φ) (by
    intro u hu v hv
    calc dist ((g ∘ φ) u) ((g ∘ φ) v) ≤ L₀ * dist (φ u) (φ v) :=
          hL₀lip _ (hφsph u hu) _ (hφsph v hv)
      _ = L₀ * ρ * dist u v := by rw [hdistφ]; ring)
  refine ⟨G' ∘ ψ, fun x hx ↦ ?_, fun L hL hLip x hx y hy ↦ ?_⟩
  · simp only [Function.comp_apply]
    rw [hG'eq _ (hψsph x hx), Function.comp_apply, hφψ]
  · calc dist ((G' ∘ ψ) x) ((G' ∘ ψ) y) ≤ Λ * (L₀ * ρ) * dist (ψ x) (ψ y) :=
          hG'lip _ (hψball x hx) _ (hψball y hy)
      _ = Λ * L₀ * dist x y := by
          rw [hdistψ]
          field_simp
      _ ≤ Λ * L * dist x y := by
          gcongr
          exact hL₀le L ⟨hL, hLip⟩

end LipschitzExtension
