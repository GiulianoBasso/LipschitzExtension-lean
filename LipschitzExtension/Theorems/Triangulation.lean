/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Geometry.SimplicialComplex.Quasiconvex
import LipschitzExtension.Topology.MetricSpace.LengthSpace
import LipschitzExtension.Theorems.Kirszbraun
import Mathlib.Geometry.Manifold.Riemannian.Basic
import LipschitzExtension.Geometry.Manifold.Riemannian.LengthSpace

/-!
# Extensions on spaces with a bi-Lipschitz triangulation

This file proves Theorem 1.3 of [Basso2024], with items 3 and 4 of the errata [BassoClaude2026].
Let `K` be a finite pure `n`-dimensional simplicial complex in `ℓ₂(V)` (`n ≥ 2`) with at most `N`
`n`-simplices and let `h : Σ → X` be a homeomorphism from its carrier `Σ` onto a length space `X`
(for example a Riemannian manifold) which is bi-Lipschitz on every `n`-simplex:
`s |u - v| ≤ d(h u, h v) ≤ s D |u - v|` for `u, v` in a common `n`-simplex. Then every
`1`-Lipschitz map `f : A → Y` defined on `A ⊆ X` with values in a complete CAT(0) space `Y` admits
a `D N^(10 log n)`-Lipschitz extension `F : X → Y`.

## Main definitions

* `Triangulation.IsSimplexwiseBilip K h s D`: `s |u - v| ≤ d(h u, h v) ≤ s D |u - v|` whenever
  `u, v` lie in a common `n`-simplex of `K`.

## Main statements

* `Triangulation.IsSimplexwiseBilip.dist_le`: `d(h u, h v) ≤ s D N^(10 log n) |u - v|` for all
  `u, v ∈ Σ` if `Σ` is connected.
* `Triangulation.IsSimplexwiseBilip.le_dist`: `s |u - v| ≤ d(h u, h v)` for all `u, v ∈ Σ` if `X`
  is a length space.
* `LipschitzOnWith.extend_triangulation_isCAT0`: Theorem 1.3 for length spaces, constant
  `D N^(10 log n)`.
* `LipschitzOnWith.extend_triangulation_isCAT0'`: Theorem 1.3 with the usual convention
  `D⁻¹ |u - v| ≤ d(h u, h v) ≤ D |u - v|`, constant `D² N^(10 log n)`.
* `LipschitzOnWith.extend_riemannian_triangulation_isCAT0` (and `'`): the same for Riemannian
  manifolds.

## Implementation notes

* As explained in item 4 of the errata, with the usual convention
  `D⁻¹ |u - v| ≤ d(h u, h v) ≤ D |u - v|` the bound of Theorem 1.3 has to be replaced by
  `D² N^(10 log n)`; this is the special case `s = D⁻¹` with `D²` in place of `D`.
* Riemannian manifolds are in the sense of Mathlib (`IsRiemannianManifold`: the distance is the
  infimum of the lengths of `C¹` paths). The only property of the manifold used in the proof is
  that it is a length space (`isLengthSpace_of_isRiemannianManifold`). In particular no
  smoothness is needed, and compactness and connectedness are automatic (the carrier of a finite
  complex is compact and length spaces are path connected), so these hypotheses of the paper are
  omitted.

## Proof outline

* Upper bound: join `u` and `v` by a polygonal path of length `≤ N^(10 log n) |u - v|` whose
  segments lie in `n`-simplices (Lemma 5.2, `Triangulation.PureComplex.exists_polygonal`) and
  apply the upper bound on each segment.
* Lower bound (the inverse part of Corollary 4.3 of Basso–Wenger–Young): since the `n`-simplices
  are closed and finitely many, every `u ∈ Σ` has a neighbourhood in `Σ` all of whose points share
  an `n`-simplex with `u`; as `h` is a homeomorphism, the same holds for `h⁻¹` near every
  `x ∈ X`, so `lip h⁻¹ ≤ s⁻¹` at every point of `X`, and Lemma 2.1 for length spaces
  (`IsLengthSpace.dist_le_of_lipLowerLE`) gives the claim.
* Theorem 1.3: `f ∘ h` is `s D N^(10 log n)`-Lipschitz on `h⁻¹(A) ⊆ Σ ⊆ ℓ₂(V)` (`Σ` is connected
  since `X` is a length space, hence path connected), so by Kirszbraun's theorem for CAT(0)
  targets (Lang–Schroeder, `LipschitzOnWith.extend_innerProductSpace_isCAT0`) it extends to an
  `s D N^(10 log n)`-Lipschitz map `G : ℓ₂(V) → Y`, and `F = G ∘ h⁻¹` works since `h⁻¹` is
  `s⁻¹`-Lipschitz (this is Lemma 2.4 of G. Basso, *Absolute Lipschitz extendability and linear
  projection constants*, used in the paper).

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
* G. Basso, S. Wenger and R. Young, *Undistorted fillings in subsets of metric spaces*,
  Adv. Math. 423 (2023), 109024
* U. Lang and V. Schroeder, *Kirszbraun's theorem and metric spaces of bounded curvature*,
  Geom. Funct. Anal. 7 (1997), 535–560
-/

open Set Metric Filter Topology

namespace LipschitzExtension

namespace Triangulation

variable {V : Type*} [Fintype V] {n : ℕ} {X : Type*} [MetricSpace X]

/-- `h : Σ → X` satisfies `s |u - v| ≤ d(h u, h v) ≤ s D |u - v|` whenever `u, v` lie in a common
`n`-simplex of `K`. -/
def IsSimplexwiseBilip (K : PureComplex V n) (h : K.carrier → X) (s D : ℝ) : Prop :=
  ∀ σ ∈ K.facets, ∀ u v : K.carrier, (u : EuclideanSpace ℝ V) ∈ face σ →
    (v : EuclideanSpace ℝ V) ∈ face σ →
      s * dist u v ≤ dist (h u) (h v) ∧ dist (h u) (h v) ≤ s * D * dist u v

/-- A simplexwise bi-Lipschitz map on a nonempty complex of dimension `n ≥ 1` has `D ≥ 1`
(compare two distinct vertices of an `n`-simplex). -/
theorem IsSimplexwiseBilip.one_le {K : PureComplex V n} {h : K.carrier → X} {s D : ℝ}
    (hh : IsSimplexwiseBilip K h s D) (hs : 0 < s) (hn : 1 ≤ n) (u : K.carrier) : 1 ≤ D := by
  classical
  obtain ⟨σ, hσ, -⟩ := Set.mem_iUnion₂.1 u.2
  have hcard : 1 < σ.card := by rw [K.card_eq σ hσ]; omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hcard
  have hmem : ∀ k ∈ σ, EuclideanSpace.single k (1 : ℝ) ∈ K.carrier := fun k hk ↦
    Set.mem_iUnion₂.2 ⟨σ, hσ, single_mem_face hk⟩
  have hab : 0 < dist (⟨_, hmem i hi⟩ : K.carrier) ⟨_, hmem j hj⟩ := by
    rw [dist_pos]
    intro heq
    have := congrArg (fun w : K.carrier ↦ (w : EuclideanSpace ℝ V) i) heq
    simp [hij] at this
  obtain ⟨h1, h2⟩ := hh σ hσ ⟨_, hmem i hi⟩ ⟨_, hmem j hj⟩ (single_mem_face hi)
    (single_mem_face hj)
  have : s * dist (⟨_, hmem i hi⟩ : K.carrier) ⟨_, hmem j hj⟩ * 1 ≤
      s * dist (⟨_, hmem i hi⟩ : K.carrier) ⟨_, hmem j hj⟩ * D := by linarith
  exact le_of_mul_le_mul_left this (mul_pos hs hab)

/-- The upper bound: `d(h u, h v) ≤ s D N^(10 log n) |u - v|` on a connected complex. -/
theorem IsSimplexwiseBilip.dist_le {K : PureComplex V n} {h : K.carrier → X}
    {s D : ℝ} (hh : IsSimplexwiseBilip K h s D) (hs : 0 < s) (hn : 2 ≤ n) {N : ℕ}
    (hN : K.facets.card ≤ N) (hK : IsConnected K.carrier) (u v : K.carrier) :
    dist (h u) (h v) ≤ s * D * (N : ℝ) ^ (10 * Real.log n) * dist u v := by
  have hD : 0 ≤ s * D := mul_nonneg hs.le (zero_le_one.trans (hh.one_le hs (by omega) u))
  obtain ⟨l, p, hp0, hpl, hseg, hsum⟩ := K.exists_polygonal hn hN hK u.2 v.2
  -- the vertices of the polygonal path, as points of `Σ`
  have hpK : ∀ i ≤ l, p i ∈ K.carrier := by
    intro i hi
    rcases hi.lt_or_eq with hi | rfl
    · obtain ⟨σ, hσ, h1, -⟩ := hseg i hi
      exact Set.mem_iUnion₂.2 ⟨σ, hσ, h1⟩
    · rw [hpl]
      exact v.2
  let q : ℕ → K.carrier := fun i ↦ if hi : i ≤ l then ⟨p i, hpK i hi⟩ else u
  have hq : ∀ i ≤ l, (q i : EuclideanSpace ℝ V) = p i := fun i hi ↦ by simp [q, hi]
  have hq0 : q 0 = u := Subtype.ext ((hq 0 (Nat.zero_le _)).trans hp0)
  have hql : q l = v := Subtype.ext ((hq l le_rfl).trans hpl)
  calc dist (h u) (h v) = dist (h (q 0)) (h (q l)) := by rw [hq0, hql]
    _ ≤ ∑ i ∈ Finset.range l, dist (h (q i)) (h (q (i + 1))) :=
        dist_le_range_sum_dist (fun i ↦ h (q i)) l
    _ ≤ ∑ i ∈ Finset.range l, s * D * dist (p i) (p (i + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        obtain ⟨σ, hσ, h1, h2⟩ := hseg i hi
        have e1 := hq i hi.le
        have e2 := hq (i + 1) hi
        have := (hh σ hσ (q i) (q (i + 1)) (by rw [e1]; exact h1) (by rw [e2]; exact h2)).2
        rwa [Subtype.dist_eq, e1, e2] at this
    _ = s * D * ∑ i ∈ Finset.range l, dist (p i) (p (i + 1)) := by rw [Finset.mul_sum]
    _ ≤ s * D * ((N : ℝ) ^ (10 * Real.log n) * dist (u : EuclideanSpace ℝ V) v) := by gcongr
    _ = s * D * (N : ℝ) ^ (10 * Real.log n) * dist u v := by rw [Subtype.dist_eq]; ring

/-- Every point `u` has a neighbourhood all of whose points in `Σ` share an `n`-simplex with `u`
(the union of the finitely many closed `n`-simplices not containing `u` is closed). -/
private theorem exists_pos_forall_mem_face (K : PureComplex V n) (u : EuclideanSpace ℝ V) :
    ∃ r > 0, ∀ w ∈ K.carrier, dist u w < r → ∃ σ ∈ K.facets, u ∈ face σ ∧ w ∈ face σ := by
  classical
  set B := ⋃ σ ∈ K.facets.filter (fun σ ↦ u ∉ face σ), face σ
  have hBc : IsClosed B := isClosed_biUnion_finset fun σ _ ↦ isClosed_face σ
  have huB : u ∉ B := by
    intro hu
    obtain ⟨σ, hσ, huσ⟩ := Set.mem_iUnion₂.1 hu
    exact (Finset.mem_filter.1 hσ).2 huσ
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hBc.isOpen_compl u huB
  refine ⟨r, hr, fun w hw hdist ↦ ?_⟩
  obtain ⟨σ, hσ, hwσ⟩ := Set.mem_iUnion₂.1 hw
  refine ⟨σ, hσ, ?_, hwσ⟩
  by_contra huσ
  exact hball (mem_ball'.2 hdist) (Set.mem_iUnion₂.2 ⟨σ, Finset.mem_filter.2 ⟨hσ, huσ⟩, hwσ⟩)

/-- The lower bound: `s |u - v| ≤ d(h u, h v)` if `h` is a homeomorphism onto a length space. -/
theorem IsSimplexwiseBilip.le_dist {K : PureComplex V n} {h : K.carrier ≃ₜ X} {s D : ℝ}
    (hh : IsSimplexwiseBilip K h s D) (hs : 0 < s) (hX : IsLengthSpace X) (u v : K.carrier) :
    s * dist u v ≤ dist (h u) (h v) := by
  -- `lip h⁻¹ ≤ s⁻¹` at every point of `X`
  have hlip : ∀ x : X, LipLowerLE h.symm x s⁻¹ := by
    intro x
    refine LipAt.lipLowerLE (lipAt_of_eventually_le ?_) (inv_nonneg.2 hs.le)
    obtain ⟨r, hr, hnear⟩ := exists_pos_forall_mem_face K (h.symm x : EuclideanSpace ℝ V)
    have hcont : ∀ᶠ x' in 𝓝 x, dist (h.symm x) (h.symm x') < r :=
      (Metric.tendsto_nhds.1 (h.symm.continuous.tendsto x) r hr).mono fun x' hx' ↦ by
        rwa [dist_comm]
    filter_upwards [hcont] with x' hx'
    obtain ⟨σ, hσ, h1, h2⟩ := hnear _ (h.symm x').2 hx'
    have := (hh σ hσ (h.symm x) (h.symm x') h1 h2).1
    rw [h.apply_symm_apply, h.apply_symm_apply] at this
    rw [← div_eq_inv_mul, le_div_iff₀ hs]
    linarith
  have := hX.dist_le_of_lipLowerLE (inv_nonneg.2 hs.le) hlip (h u) (h v)
  rw [h.symm_apply_apply, h.symm_apply_apply] at this
  calc s * dist u v ≤ s * (s⁻¹ * dist (h u) (h v)) := by gcongr
    _ = dist (h u) (h v) := by rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

/-- A nonempty length space is path connected. -/
private theorem pathConnectedSpace_of_isLengthSpace {Z : Type*} [PseudoMetricSpace Z]
    (hZ : IsLengthSpace Z) (z : Z) : PathConnectedSpace Z := by
  refine ⟨⟨z⟩, fun x y ↦ ?_⟩
  obtain ⟨γ, hγc, h0, h1, -⟩ := hZ x y 1 one_pos
  exact ⟨⟨⟨fun t ↦ γ t, hγc.comp_continuous continuous_subtype_val fun t ↦ t.2⟩, h0, h1⟩⟩

end Triangulation

end LipschitzExtension

open LipschitzExtension LipschitzExtension.Triangulation

namespace LipschitzOnWith

variable {V : Type*} [Fintype V] {n : ℕ} {Y : Type*} [MetricSpace Y] [CompleteSpace Y]

/-- **Theorem 1.3** (metric form, with item 4 of the errata): let `X` be a length space with a
triangulation `h : Σ → X` by a pure `n`-dimensional complex, `n ≥ 2`, with at most `N`
`n`-simplices, such that `s |u - v| ≤ d(h u, h v) ≤ s D |u - v|` whenever `u, v` lie in a common
`n`-simplex. Then every `1`-Lipschitz map from `A ⊆ X` to a complete CAT(0) space extends to a
`D N^(10 log n)`-Lipschitz map on `X`. -/
theorem extend_triangulation_isCAT0 {X : Type*} [MetricSpace X] {A : Set X} {f : X → Y}
    (hf : LipschitzOnWith 1 f A) (hX : IsLengthSpace X) (K : PureComplex V n) (hn : 2 ≤ n)
    {N : ℕ} (hN : K.facets.card ≤ N) (h : K.carrier ≃ₜ X) {s D : ℝ} (hs : 0 < s)
    (hh : IsSimplexwiseBilip K h s D) (hY : IsCAT0 Y) :
    ∃ F : X → Y, LipschitzWith (D * (N : ℝ) ^ (10 * Real.log n)).toNNReal F ∧ EqOn f F A := by
  classical
  refine exists_lipschitzWith_eqOn_of_nonempty fun _ ↦ ?_
  suffices h : ∃ F : X → Y, EqOn F f A ∧
      ∀ x y, dist (F x) (F y) ≤ D * (N : ℝ) ^ (10 * Real.log n) * dist x y by
    obtain ⟨F, hFA, hF⟩ := h
    exact ⟨F, LipschitzWith.of_dist_le' hF, hFA.symm⟩
  rcases isEmpty_or_nonempty X with hXe | hXne
  · exact ⟨f, fun x _ ↦ rfl, fun x ↦ isEmptyElim x⟩
  obtain ⟨x₀⟩ := hXne
  have hD : 1 ≤ D := hh.one_le hs (by omega) (h.symm x₀)
  -- `Σ` is connected since `X` is path connected
  have hK : IsConnected K.carrier := by
    have := pathConnectedSpace_of_isLengthSpace hX x₀
    exact isConnected_iff_connectedSpace.2 (h.symm.surjective.connectedSpace h.symm.continuous)
  set c : ℝ := (N : ℝ) ^ (10 * Real.log n)
  have hc0 : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hL : 0 ≤ s * D * c := mul_nonneg (mul_nonneg hs.le (zero_le_one.trans hD)) hc0
  -- `f ∘ h` on `h⁻¹(A) ⊆ Σ ⊆ ℓ₂(V)` is `s D c`-Lipschitz
  let g : EuclideanSpace ℝ V → Y := fun u ↦ if hu : u ∈ K.carrier then f (h ⟨u, hu⟩) else f x₀
  let A' : Set (EuclideanSpace ℝ V) := {u | ∃ hu : u ∈ K.carrier, h ⟨u, hu⟩ ∈ A}
  have hg : ∀ u ∈ A', ∀ v ∈ A', dist (g u) (g v) ≤ s * D * c * dist u v := by
    rintro u ⟨hu, huA⟩ v ⟨hv, hvA⟩
    simp only [g, dite_eq_left hu, dite_eq_left hv]
    calc dist (f (h ⟨u, hu⟩)) (f (h ⟨v, hv⟩)) ≤ dist (h ⟨u, hu⟩) (h ⟨v, hv⟩) := by
          simpa using hf.dist_le_mul _ huA _ hvA
      _ ≤ s * D * c * dist (⟨u, hu⟩ : K.carrier) ⟨v, hv⟩ := hh.dist_le hs hn hN hK _ _
      _ = s * D * c * dist u v := rfl
  -- Kirszbraun's theorem for CAT(0) targets, then compose with `h⁻¹`
  obtain ⟨G, hG, hGA⟩ := (LipschitzOnWith.of_dist_le' hg).extend_innerProductSpace_isCAT0 hY
  refine ⟨fun x ↦ G (h.symm x), fun x hx ↦ ?_, fun x y ↦ ?_⟩
  · have hmem : ((h.symm x : K.carrier) : EuclideanSpace ℝ V) ∈ A' :=
      ⟨(h.symm x).2, by simpa using hx⟩
    change G (h.symm x) = f x
    rw [← hGA hmem]
    simp [g]
  · have h1 := hG.dist_le_mul (h.symm x) (h.symm y)
    rw [Real.coe_toNNReal _ hL] at h1
    have h2 := hh.le_dist hs hX (h.symm x) (h.symm y)
    rw [h.apply_symm_apply, h.apply_symm_apply] at h2
    calc dist (G (h.symm x)) (G (h.symm y)) ≤ s * D * c * dist (h.symm x) (h.symm y) := h1
      _ ≤ s * D * c * (s⁻¹ * dist x y) := by
          gcongr
          rw [← div_eq_inv_mul, le_div_iff₀ hs]
          linarith
      _ = D * c * dist x y := by
          rw [show s * D * c * (s⁻¹ * dist x y) = s * s⁻¹ * (D * c * dist x y) by ring,
            mul_inv_cancel₀ hs.ne', one_mul]

/-- **Theorem 1.3** with the usual convention `D⁻¹ |u - v| ≤ d(h u, h v) ≤ D |u - v|` on every
`n`-simplex (item 4 of the errata): the extension constant is `D² N^(10 log n)`. -/
theorem extend_triangulation_isCAT0' {X : Type*} [MetricSpace X] {A : Set X} {f : X → Y}
    (hf : LipschitzOnWith 1 f A) (hX : IsLengthSpace X) (K : PureComplex V n) (hn : 2 ≤ n)
    {N : ℕ} (hN : K.facets.card ≤ N) (h : K.carrier ≃ₜ X) {D : ℝ} (hD : 0 < D)
    (hh : ∀ σ ∈ K.facets, ∀ u v : K.carrier, (u : EuclideanSpace ℝ V) ∈ face σ →
      (v : EuclideanSpace ℝ V) ∈ face σ →
        D⁻¹ * dist u v ≤ dist (h u) (h v) ∧ dist (h u) (h v) ≤ D * dist u v)
    (hY : IsCAT0 Y) :
    ∃ F : X → Y, LipschitzWith (D ^ 2 * (N : ℝ) ^ (10 * Real.log n)).toNNReal F ∧ EqOn f F A := by
  have hDD : D⁻¹ * D ^ 2 = D := by
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hD.ne', one_mul]
  refine hf.extend_triangulation_isCAT0 hX K hn hN h (inv_pos.2 hD)
    (fun σ hσ u v hu hv ↦ ⟨(hh σ hσ u v hu hv).1, ?_⟩) hY
  rw [hDD]
  exact (hh σ hσ u v hu hv).2

section Riemannian

open Manifold Bundle
open scoped ContDiff

/-- **Theorem 1.3** (with item 4 of the errata) for Riemannian `n`-manifolds `M`, `n ≥ 2`, with a
simplexwise bi-Lipschitz triangulation as in `extend_triangulation_isCAT0`: extensions into complete
CAT(0) spaces with constant `D N^(10 log n)`. -/
theorem extend_riemannian_triangulation_isCAT0 {M : Type*} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] [IsRiemannianManifold (𝓡 n) M]
    {A : Set M} {f : M → Y} (hf : LipschitzOnWith 1 f A) (K : PureComplex V n) (hn : 2 ≤ n)
    {N : ℕ} (hN : K.facets.card ≤ N) (h : K.carrier ≃ₜ M) {s D : ℝ} (hs : 0 < s)
    (hh : IsSimplexwiseBilip K h s D) (hY : IsCAT0 Y) :
    ∃ F : M → Y, LipschitzWith (D * (N : ℝ) ^ (10 * Real.log n)).toNNReal F ∧ EqOn f F A :=
  hf.extend_triangulation_isCAT0 (isLengthSpace_of_isRiemannianManifold (𝓡 n)) K hn hN h hs hh hY

/-- **Theorem 1.3** for Riemannian manifolds with the usual convention
`D⁻¹ |u - v| ≤ d(h u, h v) ≤ D |u - v|` on every `n`-simplex (item 4 of the errata): constant
`D² N^(10 log n)`. -/
theorem extend_riemannian_triangulation_isCAT0' {M : Type*} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] [IsRiemannianManifold (𝓡 n) M]
    {A : Set M} {f : M → Y} (hf : LipschitzOnWith 1 f A) (K : PureComplex V n) (hn : 2 ≤ n)
    {N : ℕ} (hN : K.facets.card ≤ N) (h : K.carrier ≃ₜ M) {D : ℝ} (hD : 0 < D)
    (hh : ∀ σ ∈ K.facets, ∀ u v : K.carrier, (u : EuclideanSpace ℝ V) ∈ face σ →
      (v : EuclideanSpace ℝ V) ∈ face σ →
        D⁻¹ * dist u v ≤ dist (h u) (h v) ∧ dist (h u) (h v) ≤ D * dist u v)
    (hY : IsCAT0 Y) :
    ∃ F : M → Y, LipschitzWith (D ^ 2 * (N : ℝ) ^ (10 * Real.log n)).toNNReal F ∧ EqOn f F A :=
  hf.extend_triangulation_isCAT0' (isLengthSpace_of_isRiemannianManifold (𝓡 n)) K hn hN h hD hh
    hY

end Riemannian

end LipschitzOnWith
