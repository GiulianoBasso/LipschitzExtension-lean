/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Analysis.Convex.RadialProjection
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.Defs
import LipschitzExtension.Topology.MetricSpace.PointwiseLipschitz.Lower
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Lipschitz extensions from the boundary of a convex body

This file proves Lemma 7.1 of [Basso2024], which compares the extension condition `LC(K, λ)` for a
convex body `K` with the condition `LC(B^(m+1), λ)` for the Euclidean unit ball.

A *convex body* is a compact convex set `K` with nonempty interior in a finite-dimensional real
inner product space. A metric space `Y` satisfies `LC(K, λ)` (Definition 7.1 of [Basso2024]) if
every `L`-Lipschitz map `f : ∂K → Y` admits a `λ L`-Lipschitz extension `F : K → Y`. For the unit
ball `K = B^(m+1)`, this is the condition `LC(B^(m+1), λ)` of `LCBall`.

**Lemma 7.1** of [Basso2024]: let `K ⊆ ℝ^(m+1)` be a convex body containing the origin in its
interior, and let `r` and `R` be the minimum and the maximum of `‖·‖` on `∂K`. If `λ` and `λ_K`
are the smallest constants such that `Y` satisfies `LC(B^(m+1), λ)` and `LC(K, λ_K)`, then
`(r/R) λ ≤ λ_K ≤ (R/r)² λ`.

## Main definitions

* `LCBody K Λ Y`: `Y` satisfies `LC(K, Λ)` (Definition 7.1 of [Basso2024]).

## Main statements

* `lcBody_closedBall_iff`: `LC(K, Λ)` for the unit ball `K = B^(m+1)` is `LC(B^(m+1), Λ)`.
* `LCBall.lcBody`: `LC(B^(m+1), λ)` implies `LC(K, (R/r)² λ)` (Lemma 7.1, upper bound).
* `LCBody.lcBall`: `LC(K, λ_K)` implies `LC(B^(m+1), (R/r) λ_K)` (Lemma 7.1, lower bound).

## Implementation notes

Lemma 7.1 is stated as the two implications above, which are equivalent to the inequalities
between the smallest constants. They are proved for `K` in any real inner product space of
dimension `m + 1` (given by `Convex ℝ K`, `IsCompact K` and `0 ∈ interior K`) and for any bounds
`0 < r ≤ ‖x‖ ≤ R` for `x ∈ ∂K`, where `∂K = frontier K`.

## Proof outline

We follow the paper. Write `B(t)`, `S(t)` and `U(t)` for the closed ball, the sphere and the open
ball of radius `t` about `0`.

*Upper bound.* By Vrecica's bound (`dist_radialProj_le`), the radial projection `ρ` onto `∂K` is
`(R/r)²`-Lipschitz on `K \ U(r)`. For an `L`-Lipschitz map `f : ∂K → Y`, let `F₁ = f ∘ ρ` on
`K \ U(r)`, and let `F₂ : B(r) → Y` be a `λ (R/r)² L`-Lipschitz extension of the restriction of
`f ∘ ρ` to `S(r)`, which exists by `LC(B(r), λ)`, a rescaling of `LC(B^(m+1), λ)`. Since `F₁ = F₂`
on `S(r)` and `K` is convex, the glued map is `(R/r)² λ L`-Lipschitz (split a segment where it
crosses `S(r)`). Here we need `λ ≥ 1`. If `λ < 1`, then the restriction of `f ∘ ρ` to `S(r)` is
`λᵏ L'`-Lipschitz for every `k` whenever it is `L'`-Lipschitz (extend and restrict again), so `f`
is constant, and we extend it constantly.

*Lower bound.* Let `f : S(1) → Y` be `L`-Lipschitz. Since `(1/R) K ⊆ B(1)` and the radial
projection `x ↦ x/‖x‖` onto `S(1)` is `(R/r)`-Lipschitz on `B(1) \ U(r/R)`, hence on
`B(1) \ int((1/R) K)`, we glue `f(x/‖x‖)` on `B(1) \ int((1/R) K)` with an `LC((1/R) K, λ_K)`
extension of the restriction of `f(x/‖x‖)` to `∂((1/R) K)`. (In the formalization we glue on
`B(R) ⊇ K` and rescale by `R` at the end; the case `λ_K < 1` is treated as above.)

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* S. Vrecica, *A note on starshaped sets*, Publ. Inst. Math. (Beograd) (N.S.) 29 (1981), 283–288
-/

open Set Metric Filter Topology

namespace LipschitzExtension

/-- `LCBody K Λ Y`: `Y` satisfies `LC(K, Λ)` (Definition 7.1 of [Basso2024]), i.e. every
`L`-Lipschitz map on the boundary `∂K = frontier K` has a `Λ L`-Lipschitz extension to `K`. In
[Basso2024], `K` is a convex body. -/
def LCBody {E : Type*} [NormedAddCommGroup E] (K : Set E) (Λ : ℝ) (Y : Type*)
    [PseudoMetricSpace Y] : Prop :=
  ∀ L : ℝ, 0 ≤ L → ∀ g : E → Y,
    (∀ x ∈ frontier K, ∀ y ∈ frontier K, dist (g x) (g y) ≤ L * dist x y) →
    ∃ G : E → Y, (∀ x ∈ frontier K, G x = g x) ∧
      ∀ x ∈ K, ∀ y ∈ K, dist (G x) (G y) ≤ Λ * L * dist x y

/-- `LC(B^(m+1), Λ)` is `LC(K, Λ)` for the unit ball `K = B^(m+1)`. -/
theorem lcBody_closedBall_iff {m : ℕ} {Λ : ℝ} {Y : Type*} [PseudoMetricSpace Y] :
    LCBody (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) Λ Y ↔ LCBall m Λ Y := by
  simp only [LCBody, LCBall, frontier_closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) one_ne_zero]

/-! ### Auxiliary lemmas -/

/-- Gluing two Lipschitz pieces on a convex set `D ⊆ A ∪ B`, `A`, `B` closed (split a segment
where it crosses from `A` to `B`). -/
private theorem lip_glue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Y : Type*}
    [PseudoMetricSpace Y] {D A B : Set E} (hD : Convex ℝ D) (hA : IsClosed A) (hB : IsClosed B)
    (hAB : D ⊆ A ∪ B) {F : E → Y} {c : ℝ}
    (hFA : ∀ x ∈ D ∩ A, ∀ y ∈ D ∩ A, dist (F x) (F y) ≤ c * dist x y)
    (hFB : ∀ x ∈ D ∩ B, ∀ y ∈ D ∩ B, dist (F x) (F y) ≤ c * dist x y) :
    ∀ x ∈ D, ∀ y ∈ D, dist (F x) (F y) ≤ c * dist x y := by
  have hmix : ∀ x ∈ D ∩ A, ∀ y ∈ D ∩ B, dist (F x) (F y) ≤ c * dist x y := by
    intro x hx y hy
    have hseg : segment ℝ x y ⊆ D := hD.segment_subset hx.1 hy.1
    obtain ⟨z, hzs, hzA, hzB⟩ := isPreconnected_closed_iff.1
      (convex_segment x y).isPreconnected A B hA hB (hseg.trans hAB)
      ⟨x, left_mem_segment ℝ x y, hx.2⟩ ⟨y, right_mem_segment ℝ x y, hy.2⟩
    have hzD := hseg hzs
    calc dist (F x) (F y) ≤ dist (F x) (F z) + dist (F z) (F y) := dist_triangle _ _ _
      _ ≤ c * dist x z + c * dist z y :=
          add_le_add (hFA x hx z ⟨hzD, hzA⟩) (hFB z ⟨hzD, hzB⟩ y hy)
      _ = c * dist x y := by rw [← mul_add, dist_add_dist_of_mem_segment hzs]
  intro x hx y hy
  rcases hAB hx with hxA | hxB <;> rcases hAB hy with hyA | hyB
  · exact hFA x ⟨hx, hxA⟩ y ⟨hy, hyA⟩
  · exact hmix x ⟨hx, hxA⟩ y ⟨hy, hyB⟩
  · rw [dist_comm, dist_comm x]
    exact hmix y ⟨hy, hyA⟩ x ⟨hx, hxB⟩
  · exact hFB x ⟨hx, hxB⟩ y ⟨hy, hyB⟩

/-- If every `L`-Lipschitz (on `S`) map `f` is automatically `Λ L`-Lipschitz on `S` with
`0 ≤ Λ < 1`, then a Lipschitz map `f` is constant on `S`. -/
private theorem eq_of_lip_self {X Y : Type*} [PseudoMetricSpace X] [MetricSpace Y] {S : Set X}
    {f : X → Y} {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : Λ < 1)
    (hstep : ∀ L, 0 ≤ L → (∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ L * dist x y) →
      ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ Λ * L * dist x y)
    {L : ℝ} (hL : 0 ≤ L) (hf : ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ L * dist x y) :
    ∀ x ∈ S, ∀ y ∈ S, f x = f y := by
  have hk : ∀ k : ℕ, ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ Λ ^ k * L * dist x y := by
    intro k
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      intro x hx y hy
      calc dist (f x) (f y) ≤ Λ * (Λ ^ k * L) * dist x y :=
            hstep (Λ ^ k * L) (by positivity) ih x hx y hy
        _ = Λ ^ (k + 1) * L * dist x y := by ring
  intro x hx y hy
  have ht : Tendsto (fun k : ℕ ↦ Λ ^ k * L * dist x y) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hΛ0 hΛ).mul_const (L * dist x y)
    simpa [mul_assoc] using this
  exact dist_le_zero.1 (ge_of_tendsto' ht fun k ↦ hk k x hx y hy)

/-- `LC(B^(m+1), Λ)` transferred to the balls `B(0, ρ)` of an `(m+1)`-dimensional real inner
product space (as in `LipschitzConnected.extend_sphere`). -/
private theorem LCBall.extend_sphere_zero {Y : Type*} [PseudoMetricSpace Y] {m : ℕ} {Λ : ℝ}
    (h : LCBall m Λ Y) {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (hW : Module.finrank ℝ W = m + 1) {ρ : ℝ} (hρ : 0 < ρ) {L : ℝ}
    (hL : 0 ≤ L) (g : W → Y)
    (hg : ∀ x ∈ sphere (0 : W) ρ, ∀ y ∈ sphere (0 : W) ρ, dist (g x) (g y) ≤ L * dist x y) :
    ∃ G : W → Y, (∀ x ∈ sphere (0 : W) ρ, G x = g x) ∧
      ∀ x ∈ closedBall (0 : W) ρ, ∀ y ∈ closedBall (0 : W) ρ,
        dist (G x) (G y) ≤ Λ * L * dist x y := by
  let e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    ((stdOrthonormalBasis ℝ W).reindex (finCongr hW)).repr
  let φ : EuclideanSpace ℝ (Fin (m + 1)) → W := fun u ↦ ρ • e.symm u
  let ψ : W → EuclideanSpace ℝ (Fin (m + 1)) := fun x ↦ e (ρ⁻¹ • x)
  have hρ' : ρ ≠ 0 := hρ.ne'
  have hφψ : ∀ x, φ (ψ x) = x := by
    intro x
    simp only [φ, ψ, LinearIsometryEquiv.symm_apply_apply, smul_smul, mul_inv_cancel₀ hρ',
      one_smul]
  have hdistφ : ∀ u v, dist (φ u) (φ v) = ρ * dist u v := by
    intro u v
    simp only [φ, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ, LinearIsometryEquiv.dist_map]
  have hdistψ : ∀ x y, dist (ψ x) (ψ y) = ρ⁻¹ * dist x y := by
    intro x y
    simp only [ψ, LinearIsometryEquiv.dist_map, dist_smul₀, norm_inv, Real.norm_eq_abs,
      abs_of_pos hρ]
  have hnormψ : ∀ x, ‖ψ x‖ = ρ⁻¹ * ‖x‖ := by
    intro x
    simp only [ψ, LinearIsometryEquiv.norm_map, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hρ]
  have hψsph : ∀ x ∈ sphere (0 : W) ρ, ψ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, hnormψ, mem_sphere_zero_iff_norm.1 hx, inv_mul_cancel₀ hρ']
  have hψball : ∀ x ∈ closedBall (0 : W) ρ,
      ψ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff, hnormψ, inv_mul_le_iff₀ hρ, mul_one]
    exact mem_closedBall_zero_iff.1 hx
  have hφsph : ∀ u ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, φ u ∈ sphere (0 : W) ρ := by
    intro u hu
    rw [mem_sphere_zero_iff_norm]
    simp only [φ, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs, abs_of_pos hρ]
    rw [mem_sphere_zero_iff_norm.1 hu, mul_one]
  obtain ⟨G', hG'eq, hG'lip⟩ := h (L * ρ) (mul_nonneg hL hρ.le) (g ∘ φ) (by
    intro u hu v hv
    calc dist ((g ∘ φ) u) ((g ∘ φ) v) ≤ L * dist (φ u) (φ v) :=
          hg _ (hφsph u hu) _ (hφsph v hv)
      _ = L * ρ * dist u v := by rw [hdistφ]; ring)
  refine ⟨G' ∘ ψ, fun x hx ↦ ?_, fun x hx y hy ↦ ?_⟩
  · simp only [Function.comp_apply]
    rw [hG'eq _ (hψsph x hx), Function.comp_apply, hφψ]
  · calc dist ((G' ∘ ψ) x) ((G' ∘ ψ) y) ≤ Λ * (L * ρ) * dist (ψ x) (ψ y) :=
          hG'lip _ (hψball x hx) _ (hψball y hy)
      _ = Λ * L * dist x y := by
          rw [hdistψ]
          field_simp

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem gauge_pos_of_isBounded {K : Set E} (hK0 : K ∈ 𝓝 (0 : E))
    (hKb : Bornology.IsBounded K) {x : E} (hx : x ≠ 0) : 0 < gauge K x :=
  (gauge_pos (absorbent_nhds_zero hK0) (NormedSpace.isVonNBounded_of_isBounded ℝ hKb)).2 hx

private theorem norm_radialProj {K : Set E} (hK0 : K ∈ 𝓝 (0 : E)) (hKb : Bornology.IsBounded K)
    {x : E} (hx : x ≠ 0) : ‖radialProj K x‖ = (gauge K x)⁻¹ * ‖x‖ := by
  rw [radialProj, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (gauge_pos_of_isBounded hK0 hKb hx))]

/-- If `r ≤ ‖·‖` on `∂K`, then `B(0, r) ⊆ K`. -/
private theorem ball_subset_of_le_norm {K : Set E} (hKc : Convex ℝ K) (hK0 : K ∈ 𝓝 (0 : E))
    (hKb : Bornology.IsBounded K) {r : ℝ} (hrK : ∀ x ∈ frontier K, r ≤ ‖x‖) :
    ball (0 : E) r ⊆ K := by
  intro z hz
  rw [mem_ball_zero_iff] at hz
  by_cases hz0 : z = 0
  · rw [hz0]
    exact mem_of_mem_nhds hK0
  have hg := gauge_pos_of_isBounded hK0 hKb hz0
  have hr := hrK _ (radialProj_mem_frontier hKc hK0 hKb hz0)
  rw [norm_radialProj hK0 hKb hz0] at hr
  have hlt : gauge K z < 1 := by
    by_contra hc
    have h1 : (gauge K z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (not_lt.1 hc)
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg z)]
  exact interior_subset ((gauge_lt_one_iff_mem_interior hKc hK0).1 hlt)

/-- If `‖·‖ ≤ R` on `∂K` (and `0 ≤ R`), then `K ⊆ B(0, R)`. -/
private theorem subset_closedBall_of_norm_le {K : Set E} (hKc : Convex ℝ K)
    (hK0 : K ∈ 𝓝 (0 : E)) (hKb : Bornology.IsBounded K) {R : ℝ} (hR : 0 ≤ R)
    (hRK : ∀ x ∈ frontier K, ‖x‖ ≤ R) : K ⊆ closedBall (0 : E) R := by
  intro z hz
  rw [mem_closedBall_zero_iff]
  by_cases hz0 : z = 0
  · rw [hz0, norm_zero]
    exact hR
  have hg := gauge_pos_of_isBounded hK0 hKb hz0
  have hR' := hRK _ (radialProj_mem_frontier hKc hK0 hKb hz0)
  rw [norm_radialProj hK0 hKb hz0] at hR'
  have h1 : 1 ≤ (gauge K z)⁻¹ := one_le_inv₀ hg |>.2 (gauge_le_one_of_mem hz)
  nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg z)]

/-- `x ↦ x / ‖x‖` is `1/r`-Lipschitz on `{x | r ≤ ‖x‖}`. -/
private theorem norm_inv_smul_sub_inv_smul_le {x y : E} {r : ℝ} (hr : 0 < r) (hx : r ≤ ‖x‖)
    (hy : r ≤ ‖y‖) : ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ ‖x - y‖ / r := by
  have hx0 : 0 < ‖x‖ := hr.trans_le hx
  have hy0 : 0 < ‖y‖ := hr.trans_le hy
  set N := ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ with hNdef
  have h1 : ‖x‖ * ‖y‖ * N ^ 2 = 2 * ‖x‖ * ‖y‖ - 2 * inner ℝ x y := by
    rw [hNdef, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, norm_inv, norm_norm, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne',
      inv_mul_cancel₀ hy0.ne']
    field_simp
    ring
  have h2 : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := norm_sub_sq_real x y
  have h3 : (r * N) ^ 2 ≤ ‖x - y‖ ^ 2 := by
    have : r * r ≤ ‖x‖ * ‖y‖ := mul_le_mul hx hy hr.le hx0.le
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg N]
  rw [le_div_iff₀ hr, mul_comm]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 h3

end Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Y : Type*} [MetricSpace Y]

/-- **Lemma 7.1** of [Basso2024], upper bound: `LC(B^(m+1), λ)` implies `LC(K, (R/r)² λ)` for
every convex body `K` of an `(m+1)`-dimensional real inner product space with `0 ∈ int K` and
`0 < r ≤ ‖x‖ ≤ R` for `x ∈ ∂K`. -/
theorem LCBall.lcBody {m : ℕ} (hE : Module.finrank ℝ E = m + 1) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hY : LCBall m Λ Y) {K : Set E} (hKc : Convex ℝ K) (hKK : IsCompact K)
    (h0 : (0 : E) ∈ interior K) {r R : ℝ} (hr : 0 < r) (hrK : ∀ x ∈ frontier K, r ≤ ‖x‖)
    (hRK : ∀ x ∈ frontier K, ‖x‖ ≤ R) :
    LCBody K ((R / r) ^ 2 * Λ) Y := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hK0 : K ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.1 h0
  have hKb : Bornology.IsBounded K := hKK.isBounded
  have hball : ball (0 : E) r ⊆ K := ball_subset_of_le_norm hKc hK0 hKb hrK
  intro L hL g hg
  -- the outer piece `g ∘ ρ` is `(R/r)² L`-Lipschitz on `{x | r ≤ ‖x‖}` (Vrecica's bound)
  have hout : ∀ x y : E, r ≤ ‖x‖ → r ≤ ‖y‖ →
      dist (g (radialProj K x)) (g (radialProj K y)) ≤ (R / r) ^ 2 * L * dist x y := by
    intro x y hx hy
    have hx0 : x ≠ 0 := norm_pos_iff.1 (hr.trans_le hx)
    have hy0 : y ≠ 0 := norm_pos_iff.1 (hr.trans_le hy)
    calc dist (g (radialProj K x)) (g (radialProj K y))
        ≤ L * dist (radialProj K x) (radialProj K y) :=
          hg _ (radialProj_mem_frontier hKc hK0 hKb hx0) _
            (radialProj_mem_frontier hKc hK0 hKb hy0)
      _ ≤ L * ((R / r) ^ 2 * dist x y) := by
          gcongr
          exact dist_radialProj_le hKc hKb hr hball hRK hx hy
      _ = (R / r) ^ 2 * L * dist x y := by ring
  have hsph : ∀ x ∈ sphere (0 : E) r, ∀ y ∈ sphere (0 : E) r,
      dist (g (radialProj K x)) (g (radialProj K y)) ≤ (R / r) ^ 2 * L * dist x y :=
    fun x hx y hy ↦ hout x y (mem_sphere_zero_iff_norm.1 hx).ge (mem_sphere_zero_iff_norm.1 hy).ge
  rcases lt_or_ge Λ 1 with hΛ1 | hΛ1
  · -- `Λ < 1`: `g` is constant on `∂K`, extend it constantly
    have hconst : ∀ x ∈ sphere (0 : E) r, ∀ y ∈ sphere (0 : E) r,
        g (radialProj K x) = g (radialProj K y) := by
      refine eq_of_lip_self (f := fun x ↦ g (radialProj K x)) hΛ hΛ1 ?_ (by positivity) hsph
      intro L' hL' hL'lip x hx y hy
      obtain ⟨G', hG'eq, hG'lip⟩ :=
        LCBall.extend_sphere_zero hY hE hr hL' (fun x ↦ g (radialProj K x)) hL'lip
      have := hG'lip x (sphere_subset_closedBall hx) y (sphere_subset_closedBall hy)
      rwa [hG'eq x hx, hG'eq y hy] at this
    have hgp : ∀ p ∈ frontier K, (r / ‖p‖) • p ∈ sphere (0 : E) r ∧
        g (radialProj K ((r / ‖p‖) • p)) = g p := by
      intro p hp
      have hp0 : 0 < ‖p‖ := hr.trans_le (hrK p hp)
      refine ⟨?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hp0),
          div_mul_cancel₀ _ hp0.ne']
      · rw [radialProj_smul (div_pos hr hp0), radialProj_eq_self hKc hK0 hp]
    by_cases hne : (frontier K).Nonempty
    · obtain ⟨p₀, hp₀⟩ := hne
      refine ⟨fun _ ↦ g p₀, fun x hx ↦ ?_, fun x _ y _ ↦ ?_⟩
      · rw [← (hgp x hx).2, ← (hgp p₀ hp₀).2]
        exact hconst _ (hgp p₀ hp₀).1 _ (hgp x hx).1
      · rw [dist_self]
        positivity
    · refine ⟨fun _ ↦ g 0, fun x hx ↦ absurd ⟨x, hx⟩ hne, fun x _ y _ ↦ ?_⟩
      rw [dist_self]
      positivity
  · -- `Λ ≥ 1`: glue `g ∘ ρ` with an extension from the sphere `S(r)`
    obtain ⟨F₂, hF₂eq, hF₂lip⟩ := LCBall.extend_sphere_zero hY hE hr (by positivity)
      (fun x ↦ g (radialProj K x)) hsph
    classical
    have hG_out : ∀ x : E, r ≤ ‖x‖ →
        (if ‖x‖ ≤ r then F₂ x else g (radialProj K x)) = g (radialProj K x) := by
      intro x hx
      split_ifs with h
      · exact hF₂eq x (mem_sphere_zero_iff_norm.2 (le_antisymm h hx))
      · rfl
    refine ⟨fun x ↦ if ‖x‖ ≤ r then F₂ x else g (radialProj K x), fun x hx ↦ ?_, ?_⟩
    · simp only
      rw [hG_out x (hrK x hx), radialProj_eq_self hKc hK0 hx]
    · refine lip_glue hKc isClosed_closedBall (isClosed_le continuous_const continuous_norm)
        (fun x _ ↦ (le_total ‖x‖ r).imp mem_closedBall_zero_iff.2 id) ?_ ?_
      · intro x hx y hy
        simp only [ite_eq_left (mem_closedBall_zero_iff.1 hx.2),
          ite_eq_left (mem_closedBall_zero_iff.1 hy.2)]
        calc dist (F₂ x) (F₂ y) ≤ Λ * ((R / r) ^ 2 * L) * dist x y := hF₂lip x hx.2 y hy.2
          _ = (R / r) ^ 2 * Λ * L * dist x y := by ring
      · intro x hx y hy
        rw [hG_out x hx.2, hG_out y hy.2]
        have h1 : 0 ≤ (R / r) ^ 2 * L * dist x y := by positivity
        calc dist (g (radialProj K x)) (g (radialProj K y)) ≤ (R / r) ^ 2 * L * dist x y :=
              hout x y hx.2 hy.2
          _ ≤ (R / r) ^ 2 * Λ * L * dist x y := by nlinarith

/-- **Lemma 7.1** of [Basso2024], lower bound: `LC(K, λ_K)` implies `LC(B^(m+1), (R/r) λ_K)` for
every convex body `K` of an `(m+1)`-dimensional real inner product space with `0 ∈ int K` and
`0 < r ≤ ‖x‖ ≤ R` for `x ∈ ∂K`. -/
theorem LCBody.lcBall {m : ℕ} (hE : Module.finrank ℝ E = m + 1) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {K : Set E} (hY : LCBody K Λ Y) (hKc : Convex ℝ K) (hKK : IsCompact K)
    (h0 : (0 : E) ∈ interior K) {r R : ℝ} (hr : 0 < r) (hrK : ∀ x ∈ frontier K, r ≤ ‖x‖)
    (hRK : ∀ x ∈ frontier K, ‖x‖ ≤ R) :
    LCBall m ((R / r) * Λ) Y := by
  have hK0 : K ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.1 h0
  have hKb : Bornology.IsBounded K := hKK.isBounded
  have hKcl : IsClosed K := hKK.isClosed
  have hball : ball (0 : E) r ⊆ K := ball_subset_of_le_norm hKc hK0 hKb hrK
  have hint : ball (0 : E) r ⊆ interior K := interior_maximal hball isOpen_ball
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  have hp₀ := radialProj_mem_frontier hKc hK0 hKb hx₀
  have hR : 0 < R := hr.trans_le ((hrK _ hp₀).trans (hRK _ hp₀))
  have hKR : K ⊆ closedBall (0 : E) R := subset_closedBall_of_norm_le hKc hK0 hKb hR.le hRK
  have hintR : interior K ⊆ ball (0 : E) R := by
    rw [← interior_closedBall (0 : E) hR.ne']
    exact interior_mono hKR
  let e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    ((stdOrthonormalBasis ℝ E).reindex (finCongr hE)).repr
  intro L hL g hg
  -- `f x = g (x / ‖x‖)` (transported to `E`) is `L/r`-Lipschitz on `{x | r ≤ ‖x‖}`
  set f : E → Y := fun x ↦ g (e (‖x‖⁻¹ • x)) with hfdef
  have hf : ∀ x y : E, r ≤ ‖x‖ → r ≤ ‖y‖ → dist (f x) (f y) ≤ L / r * dist x y := by
    intro x y hx hy
    have hx0 : 0 < ‖x‖ := hr.trans_le hx
    have hy0 : 0 < ‖y‖ := hr.trans_le hy
    have hux : e (‖x‖⁻¹ • x) ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
      rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, norm_smul, norm_inv,
        norm_norm, inv_mul_cancel₀ hx0.ne']
    have huy : e (‖y‖⁻¹ • y) ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
      rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, norm_smul, norm_inv,
        norm_norm, inv_mul_cancel₀ hy0.ne']
    calc dist (f x) (f y) ≤ L * dist (e (‖x‖⁻¹ • x)) (e (‖y‖⁻¹ • y)) := hg _ hux _ huy
      _ = L * ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ := by rw [LinearIsometryEquiv.dist_map, dist_eq_norm]
      _ ≤ L * (‖x - y‖ / r) := by
          gcongr
          exact norm_inv_smul_sub_inv_smul_le hr hx hy
      _ = L / r * dist x y := by rw [dist_eq_norm]; ring
  have hfK : ∀ x ∈ frontier K, ∀ y ∈ frontier K, dist (f x) (f y) ≤ L / r * dist x y :=
    fun x hx y hy ↦ hf x y (hrK x hx) (hrK y hy)
  have hfg : ∀ u ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, ∀ t : ℝ, 0 < t →
      f (t • e.symm u) = g u := by
    intro u hu t ht
    have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 hu
    simp only [hfdef, norm_smul, LinearIsometryEquiv.norm_map, hu1, Real.norm_eq_abs,
      abs_of_pos ht, mul_one, smul_smul, inv_mul_cancel₀ ht.ne', one_smul,
      LinearIsometryEquiv.apply_symm_apply]
  rcases lt_or_ge Λ 1 with hΛ1 | hΛ1
  · -- `Λ < 1`: `f` is constant on `∂K`, hence `g` is constant on the unit sphere
    have hconst : ∀ x ∈ frontier K, ∀ y ∈ frontier K, f x = f y := by
      refine eq_of_lip_self hΛ hΛ1 ?_ (div_nonneg hL hr.le) hfK
      intro L' hL' hL'lip x hx y hy
      obtain ⟨H, hHeq, hHlip⟩ := hY L' hL' f hL'lip
      have := hHlip x (hKcl.frontier_subset hx) y (hKcl.frontier_subset hy)
      rwa [hHeq x hx, hHeq y hy] at this
    have hgp : ∀ u ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
        radialProj K (e.symm u) ∈ frontier K ∧ f (radialProj K (e.symm u)) = g u := by
      intro u hu
      have hu0 : e.symm u ≠ 0 := by
        rw [Ne, LinearIsometryEquiv.map_eq_zero_iff]
        exact ne_zero_of_mem_sphere one_ne_zero ⟨u, hu⟩
      exact ⟨radialProj_mem_frontier hKc hK0 hKb hu0,
        hfg u hu _ (inv_pos.2 (gauge_pos_of_isBounded hK0 hKb hu0))⟩
    obtain ⟨u₀, hu₀⟩ : (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).Nonempty :=
      NormedSpace.sphere_nonempty.2 zero_le_one
    refine ⟨fun _ ↦ g u₀, fun u hu ↦ ?_, fun x _ y _ ↦ ?_⟩
    · rw [← (hgp u hu).2, ← (hgp u₀ hu₀).2]
      exact hconst _ (hgp u₀ hu₀).1 _ (hgp u hu).1
    · rw [dist_self]
      positivity
  · -- `Λ ≥ 1`: glue `f` outside `int K` with an `LC(K, Λ)`-extension inside `K`
    obtain ⟨H, hHeq, hHlip⟩ := hY (L / r) (div_nonneg hL hr.le) f hfK
    classical
    set G : E → Y := fun x ↦ if x ∈ K then H x else f x with hGdef
    have hG_out : ∀ x, x ∉ interior K → G x = f x := by
      intro x hx
      simp only [hGdef]
      split_ifs with hxK
      · exact hHeq x ⟨subset_closure hxK, hx⟩
      · rfl
    have hGlip : ∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R,
        dist (G x) (G y) ≤ Λ * (L / r) * dist x y := by
      refine lip_glue (convex_closedBall 0 R) hKcl isOpen_interior.isClosed_compl
        (fun x _ ↦ (em (x ∈ K)).imp id fun hx hx' ↦ hx (interior_subset hx')) ?_ ?_
      · intro x hx y hy
        simp only [hGdef, ite_eq_left hx.2, ite_eq_left hy.2]
        exact hHlip x hx.2 y hy.2
      · intro x hx y hy
        rw [hG_out x hx.2, hG_out y hy.2]
        have hxr : r ≤ ‖x‖ := by
          by_contra hc
          exact hx.2 (hint (mem_ball_zero_iff.2 (not_le.1 hc)))
        have hyr : r ≤ ‖y‖ := by
          by_contra hc
          exact hy.2 (hint (mem_ball_zero_iff.2 (not_le.1 hc)))
        have h1 : 0 ≤ L / r * dist x y := by positivity
        calc dist (f x) (f y) ≤ L / r * dist x y := hf x y hxr hyr
          _ ≤ Λ * (L / r) * dist x y := by nlinarith
    have hmemR : ∀ w ∈ closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
        R • e.symm w ∈ closedBall (0 : E) R := by
      intro w hw
      rw [mem_closedBall_zero_iff, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
        abs_of_pos hR]
      calc R * ‖w‖ ≤ R * 1 := by gcongr; exact mem_closedBall_zero_iff.1 hw
        _ = R := mul_one R
    refine ⟨fun u ↦ G (R • e.symm u), fun u hu ↦ ?_, fun u hu v hv ↦ ?_⟩
    · have hnorm : ‖R • e.symm u‖ = R := by
        rw [norm_smul, LinearIsometryEquiv.norm_map, mem_sphere_zero_iff_norm.1 hu,
          Real.norm_eq_abs, abs_of_pos hR, mul_one]
      have hnotint : R • e.symm u ∉ interior K := fun hx ↦ by
        have := mem_ball_zero_iff.1 (hintR hx)
        linarith
      simp only
      rw [hG_out _ hnotint, hfg u hu R hR]
    · calc dist (G (R • e.symm u)) (G (R • e.symm v))
          ≤ Λ * (L / r) * dist (R • e.symm u) (R • e.symm v) :=
            hGlip _ (hmemR u hu) _ (hmemR v hv)
        _ = R / r * Λ * L * dist u v := by
            rw [dist_smul₀, LinearIsometryEquiv.dist_map, Real.norm_eq_abs, abs_of_pos hR]
            field_simp

end LipschitzExtension
