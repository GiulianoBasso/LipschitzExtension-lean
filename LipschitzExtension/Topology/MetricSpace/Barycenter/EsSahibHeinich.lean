/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Bicombing.Midpoint

/-!
# Barycenters of finite multisets (Es-Sahib–Heinich)

This file proves **Theorem 6.1** of Descombes' thesis, after A. Es-Sahib and H. Heinich and
A. Navas. Let `m` be a conical midpoint map on a complete metric space `X` (in the thesis
`m(x, y) = σ_{xy}(½)` for a reversible bicombing `σ`). For every nonempty finite multiset `M` of
points there is a barycenter `baryM M ∈ X` such that

* (i) `baryM M` lies in every closed `m`-convex set containing the points of `M`;
* (ii) `baryM M` does not depend on the order of the points (built in: `M` is a multiset);
* (iv) `d(baryM M, baryM N) ≤ (1/n) ∑ᵢ d(xᵢ, yᵢ)` whenever `M = {x₁, …, xₙ}`,
  `N = {y₁, …, yₙ}`; we state this for a multiset `P` of pairs `(xᵢ, yᵢ)` (a coupling).

We also record `baryM M = baryM T(M)` for `#M ≥ 3`, where `T(M) = {baryM (M - {a}) : a ∈ M}`
(used in Lemma 6.2), and `baryM {x, …, x} = x`.

## Main definitions

* `ConicalMidpointMap.baryM`: the Es-Sahib–Heinich barycenter of a finite multiset of points.

## Main statements

* `ConicalMidpointMap.baryM_mem`: Theorem 6.1 (i).
* `ConicalMidpointMap.dist_baryM_le`: Theorem 6.1 (iv).
* `ConicalMidpointMap.baryM_singleton`, `ConicalMidpointMap.baryM_pair`,
  `ConicalMidpointMap.baryM_replicate`: `baryM {x} = x`, `baryM {x, y} = m x y` and
  `baryM {x, …, x} = x`.
* `ConicalMidpointMap.baryM_eq_baryM_map_erase`: `baryM M = baryM T(M)` for `#M ≥ 3` (the relation
  after the proof of Theorem 6.1).

## Implementation notes

* The equivariance statement (iii) of Theorem 6.1 (`γ(bar(x₁, …, xₙ)) = bar(γ(x₁), …, γ(xₙ))` for
  isometries `γ` for which `σ` is `γ`-equivariant) is not formalized; it is not needed.
* The definition assumes `[Nonempty X]` only to have a junk value for the empty multiset.

## Proof outline

Put `baryM {x} = x`, `baryM {x, y} = m x y`, and for `#M = n ≥ 3` let
`T(M) = {baryM (M - {a}) : a ∈ M}` (a multiset with `n` elements, built from barycenters of
`n - 1` points). Then `diam T(M) ≤ diam(M)/(n - 1)` by (iv) for `n - 1` points, and
`baryM M` is the common limit of the points of `Tᵏ(M)`. Property (iv) passes to the limit since
the average cost of the coupling does not increase under `T` (sum (iv) over the `n` removed
points: every pair is counted `n - 1` times).

## References

* D. Descombes, *Spaces with convex geodesic bicombings*, PhD thesis, ETH Zürich, 2015
-/

open Set Metric Filter Topology

namespace LipschitzExtension

namespace ConicalMidpointMap

/-! ### Auxiliary constructions

For a map `f` defined on multisets with `N` elements we consider `T(M) = {f (M - {a}) : a ∈ M}`
on multisets with `N + 1` elements, and `limBar f M`, the limit of (chosen) points of `Tᵏ(M)`.
The properties (i) and (iv) at level `N` (`ConvexProp`, `CouplingProp`) pass to `limBar f` at
level `N + 1` when `N ≥ 2`. -/

section Pick

variable {X : Type*} [Nonempty X]

/-- Some point of `M` (a junk value if `M = 0`). -/
private noncomputable def pick (M : Multiset X) : X :=
  Classical.epsilon (· ∈ M)

private theorem pick_mem {M : Multiset X} (hM : M ≠ 0) : pick M ∈ M :=
  Classical.epsilon_spec (Multiset.exists_mem_of_ne_zero hM)

private theorem pick_singleton (a : X) : pick ({a} : Multiset X) = a :=
  Multiset.mem_singleton.1 (pick_mem (Multiset.singleton_ne_zero a))

end Pick

section Step

variable {X : Type*} [DecidableEq X] {f : Multiset X → X}

/-- The map `T(M) = {f (M - {a}) : a ∈ M}`. -/
private def stepT (f : Multiset X → X) (M : Multiset X) : Multiset X :=
  M.map fun a ↦ f (M.erase a)

private theorem card_stepT (M : Multiset X) :
    Multiset.card (stepT f M) = Multiset.card M :=
  Multiset.card_map _ _

private theorem card_iterate_stepT (M : Multiset X) (k : ℕ) :
    Multiset.card ((stepT f)^[k] M) = Multiset.card M := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', card_stepT, ih]

private theorem cons_singleton_erase (a b : X) : (a ::ₘ {b}).erase b = {a} := by
  rcases eq_or_ne a b with rfl | h
  · exact Multiset.erase_cons_head a {a}
  · rw [Multiset.erase_cons_tail _ h, Multiset.erase_singleton, Multiset.cons_zero]

/-- The map `T` on couplings: `(T(P)).map Prod.fst = T(P.map Prod.fst)` and similarly for
`Prod.snd`. -/
private def stepT₂ (f : Multiset X → X) (P : Multiset (X × X)) : Multiset (X × X) :=
  P.map fun p ↦ (f ((P.erase p).map Prod.fst), f ((P.erase p).map Prod.snd))

private theorem map_fst_stepT₂ (P : Multiset (X × X)) :
    (stepT₂ f P).map Prod.fst = stepT f (P.map Prod.fst) := by
  rw [stepT₂, stepT, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun p hp ↦ ?_
  simp only [Function.comp_apply]
  rw [Multiset.map_erase_of_mem _ _ hp]

private theorem map_snd_stepT₂ (P : Multiset (X × X)) :
    (stepT₂ f P).map Prod.snd = stepT f (P.map Prod.snd) := by
  rw [stepT₂, stepT, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun p hp ↦ ?_
  simp only [Function.comp_apply]
  rw [Multiset.map_erase_of_mem _ _ hp]

private theorem map_fst_iterate_stepT₂ (P : Multiset (X × X)) (k : ℕ) :
    ((stepT₂ f)^[k] P).map Prod.fst = (stepT f)^[k] (P.map Prod.fst) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_fst_stepT₂, ih]

private theorem map_snd_iterate_stepT₂ (P : Multiset (X × X)) (k : ℕ) :
    ((stepT₂ f)^[k] P).map Prod.snd = (stepT f)^[k] (P.map Prod.snd) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_snd_stepT₂, ih]

private theorem card_iterate_stepT₂ (P : Multiset (X × X)) (k : ℕ) :
    Multiset.card ((stepT₂ f)^[k] P) = Multiset.card P := by
  rw [← Multiset.card_map Prod.fst, map_fst_iterate_stepT₂, card_iterate_stepT,
    Multiset.card_map]

end Step

section Aux

variable {X : Type*} [MetricSpace X] (m : ConicalMidpointMap X)

private theorem isConvex_closedBall (c : X) (r : ℝ) : m.IsConvex (closedBall c r) := by
  intro x hx y hy
  rw [mem_closedBall] at hx hy ⊢
  calc dist (m x y) c = dist (m x y) (m c c) := by rw [m.self]
    _ ≤ (dist x c + dist y c) / 2 := m.dist_le_add x y c c
    _ ≤ r := by linarith

private theorem isConvex_singleton (a : X) : m.IsConvex {a} := by
  intro x hx y hy
  rw [mem_singleton_iff] at hx hy ⊢
  rw [hx, hy, m.self]

/-- Property (iv) of Theorem 6.1 for multisets with `N` elements (multiplied by `N`). -/
private def CouplingProp (f : Multiset X → X) (N : ℕ) : Prop :=
  ∀ P : Multiset (X × X), Multiset.card P = N →
    (N : ℝ) * dist (f (P.map Prod.fst)) (f (P.map Prod.snd)) ≤ (P.map fun p ↦ dist p.1 p.2).sum

/-- Property (i) of Theorem 6.1 for multisets with `N` elements. -/
private def ConvexProp (f : Multiset X → X) (N : ℕ) : Prop :=
  ∀ M : Multiset X, Multiset.card M = N → ∀ C : Set X, IsClosed C → m.IsConvex C →
    (∀ a ∈ M, a ∈ C) → f M ∈ C

/-- All distances between points of `M` are at most `D`. -/
private def PairBound (M : Multiset X) (D : ℝ) : Prop :=
  ∀ a ∈ M, ∀ b ∈ M, dist a b ≤ D

private theorem exists_pairBound (M : Multiset X) : ∃ D, PairBound M D := by
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 (Multiset.finite_toSet M).isBounded
  exact ⟨D, fun a ha b hb ↦ hD ha hb⟩

section Estimates

variable [DecidableEq X] {f : Multiset X → X} {N : ℕ}

/-- `T` maps multisets in a closed `m`-convex set `C` to multisets in `C`. -/
private theorem mem_of_mem_stepT (hc : ConvexProp m f N) {M : Multiset X}
    (hM : Multiset.card M = N + 1) {C : Set X} (hC : IsClosed C) (hCm : m.IsConvex C)
    (hMC : ∀ a ∈ M, a ∈ C) : ∀ y ∈ stepT f M, y ∈ C := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hy
  refine hc (M.erase a) ?_ C hC hCm fun b hb ↦ hMC b (Multiset.mem_of_mem_erase hb)
  rw [Multiset.card_erase_of_mem ha, hM, Nat.pred_succ]

private theorem mem_of_mem_iterate_stepT (hc : ConvexProp m f N) {M : Multiset X}
    (hM : Multiset.card M = N + 1) {C : Set X} (hC : IsClosed C) (hCm : m.IsConvex C)
    (hMC : ∀ a ∈ M, a ∈ C) (k : ℕ) : ∀ y ∈ (stepT f)^[k] M, y ∈ C := by
  induction k with
  | zero => exact hMC
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact mem_of_mem_stepT m hc (by rw [card_iterate_stepT, hM]) hC hCm ih

/-- Removing two points `a, b` of `M`: `N * d(f (M - {a}), f (M - {b})) ≤ d(a, b)`. -/
private theorem mul_dist_erase_le (hf : CouplingProp f N) {M : Multiset X}
    (hM : Multiset.card M = N + 1) {a b : X} (ha : a ∈ M) (hb : b ∈ M) :
    (N : ℝ) * dist (f (M.erase a)) (f (M.erase b)) ≤ dist a b := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  have hb' : b ∈ M.erase a := (Multiset.mem_erase_of_ne hab.symm).2 hb
  have ha' : a ∈ M.erase b := (Multiset.mem_erase_of_ne hab).2 ha
  have h1 : (((b, a) ::ₘ ((M.erase a).erase b).map fun r ↦ (r, r)).map Prod.fst) =
      M.erase a := by
    simp only [Multiset.map_cons, Multiset.map_map, Function.comp_def, Multiset.map_id']
    exact Multiset.cons_erase hb'
  have h2 : (((b, a) ::ₘ ((M.erase a).erase b).map fun r ↦ (r, r)).map Prod.snd) =
      M.erase b := by
    simp only [Multiset.map_cons, Multiset.map_map, Function.comp_def, Multiset.map_id']
    rw [Multiset.erase_comm]
    exact Multiset.cons_erase ha'
  have hcard : Multiset.card ((b, a) ::ₘ ((M.erase a).erase b).map fun r ↦ (r, r)) = N := by
    rw [← Multiset.card_map Prod.fst, h1, Multiset.card_erase_of_mem ha, hM, Nat.pred_succ]
  have hcost : (((b, a) ::ₘ ((M.erase a).erase b).map fun r ↦ (r, r)).map
      fun p ↦ dist p.1 p.2).sum = dist b a := by
    simp [Multiset.map_map]
  have h := hf _ hcard
  rwa [h1, h2, hcost, dist_comm b a] at h

private theorem pairBound_stepT (hf : CouplingProp f N) (hN : 0 < N) {M : Multiset X}
    (hM : Multiset.card M = N + 1) {D : ℝ} (hD : PairBound M D) :
    PairBound (stepT f M) (D / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  intro y hy z hz
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hz
  rw [le_div_iff₀ hN0, mul_comm]
  exact (mul_dist_erase_le hf hM ha hb).trans (hD a ha b hb)

private theorem pairBound_iterate_stepT (hf : CouplingProp f N) (hN : 0 < N) {M : Multiset X}
    (hM : Multiset.card M = N + 1) {D : ℝ} (hD : PairBound M D) (k : ℕ) :
    PairBound ((stepT f)^[k] M) (D * (N : ℝ)⁻¹ ^ k) := by
  induction k with
  | zero => simpa using hD
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ, ← mul_assoc, ← div_eq_mul_inv]
    exact pairBound_stepT hf hN (by rw [card_iterate_stepT, hM]) ih

/-- The cost of a coupling does not increase under `T`. -/
private theorem cost_stepT₂_le (hf : CouplingProp f N) (hN : 0 < N) {P : Multiset (X × X)}
    (hP : Multiset.card P = N + 1) :
    ((stepT₂ f P).map fun q ↦ dist q.1 q.2).sum ≤ (P.map fun p ↦ dist p.1 p.2).sum := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) * ((stepT₂ f P).map fun q ↦ dist q.1 q.2).sum ≤
      (P.map fun p ↦ ((P.erase p).map fun q ↦ dist q.1 q.2).sum).sum := by
    rw [← Multiset.sum_map_mul_left, stepT₂, Multiset.map_map]
    refine Multiset.sum_map_le_sum_map _ _ fun p hp ↦ hf (P.erase p) ?_
    rw [Multiset.card_erase_of_mem hp, hP, Nat.pred_succ]
  have h2 : ∀ p ∈ P, dist p.1 p.2 + ((P.erase p).map fun q ↦ dist q.1 q.2).sum =
      (P.map fun p ↦ dist p.1 p.2).sum := fun p hp ↦
    Multiset.sum_map_erase (f := fun q : X × X ↦ dist q.1 q.2) hp
  have h3 := congrArg Multiset.sum (Multiset.map_congr rfl h2)
  rw [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, hP, nsmul_eq_mul]
    at h3
  push_cast at h3
  have h4 : (N : ℝ) * ((stepT₂ f P).map fun q ↦ dist q.1 q.2).sum ≤
      N * (P.map fun p ↦ dist p.1 p.2).sum := by linarith
  exact le_of_mul_le_mul_left h4 hN0

private theorem cost_iterate_stepT₂_le (hf : CouplingProp f N) (hN : 0 < N)
    {P : Multiset (X × X)} (hP : Multiset.card P = N + 1) (k : ℕ) :
    (((stepT₂ f)^[k] P).map fun q ↦ dist q.1 q.2).sum ≤ (P.map fun p ↦ dist p.1 p.2).sum := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (cost_stepT₂_le hf hN (by rw [card_iterate_stepT₂, hP])).trans ih

section Limit

variable [Nonempty X]

private theorem dist_pick_stepT_le (hc : ConvexProp m f N) {M : Multiset X}
    (hM : Multiset.card M = N + 1) {D : ℝ} (hD : PairBound M D) :
    dist (pick M) (pick (stepT f M)) ≤ D := by
  have hne : M ≠ 0 := Multiset.card_pos.1 (by omega)
  have hne' : stepT f M ≠ 0 := Multiset.card_pos.1 (by rw [card_stepT]; omega)
  have h := mem_of_mem_stepT m hc hM isClosed_closedBall (isConvex_closedBall m (pick M) D)
    (fun a ha ↦ mem_closedBall.2 (hD a ha _ (pick_mem hne))) _ (pick_mem hne')
  rw [dist_comm]
  exact mem_closedBall.1 h

variable [CompleteSpace X]

open scoped Classical in
/-- The limit of the points `pick (Tᵏ(M))` if they form a Cauchy sequence (a junk value
otherwise). -/
private noncomputable def limBar (f : Multiset X → X) (M : Multiset X) : X :=
  if h : CauchySeq fun k ↦ pick ((stepT f)^[k] M) then
    (cauchySeq_tendsto_of_complete h).choose
  else pick M

private theorem tendsto_limBar (hf : CouplingProp f N) (hc : ConvexProp m f N) (hN : 2 ≤ N)
    {M : Multiset X} (hM : Multiset.card M = N + 1) :
    Tendsto (fun k ↦ pick ((stepT f)^[k] M)) atTop (𝓝 (limBar f M)) := by
  obtain ⟨D, hD⟩ := exists_pairBound M
  have hr : (N : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < N))
  have hcs : CauchySeq fun k ↦ pick ((stepT f)^[k] M) := by
    refine cauchySeq_of_le_geometric (N : ℝ)⁻¹ D hr fun k ↦ ?_
    rw [Function.iterate_succ_apply']
    exact dist_pick_stepT_le m hc (by rw [card_iterate_stepT, hM])
      (pairBound_iterate_stepT hf (by omega) hM hD k)
  rw [limBar, dite_eq_left hcs]
  exact (cauchySeq_tendsto_of_complete hcs).choose_spec

private theorem limBar_mem (hf : CouplingProp f N) (hc : ConvexProp m f N) (hN : 2 ≤ N)
    {M : Multiset X} (hM : Multiset.card M = N + 1) {C : Set X} (hC : IsClosed C)
    (hCm : m.IsConvex C) (hMC : ∀ a ∈ M, a ∈ C) : limBar f M ∈ C := by
  refine hC.mem_of_tendsto (tendsto_limBar m hf hc hN hM) (Eventually.of_forall fun k ↦ ?_)
  refine mem_of_mem_iterate_stepT m hc hM hC hCm hMC k _ (pick_mem ?_)
  rw [← Multiset.card_pos, card_iterate_stepT, hM]
  exact Nat.succ_pos N

private theorem limBar_iterate_stepT (hf : CouplingProp f N) (hc : ConvexProp m f N)
    (hN : 2 ≤ N) {M : Multiset X} (hM : Multiset.card M = N + 1) (j : ℕ) :
    limBar f ((stepT f)^[j] M) = limBar f M := by
  have h := (tendsto_add_atTop_iff_nat j).2 (tendsto_limBar m hf hc hN hM)
  simp only [Function.iterate_add_apply] at h
  exact tendsto_nhds_unique (tendsto_limBar m hf hc hN (by rw [card_iterate_stepT, hM])) h

private theorem limBar_stepT (hf : CouplingProp f N) (hc : ConvexProp m f N)
    (hN : 2 ≤ N) {M : Multiset X} (hM : Multiset.card M = N + 1) :
    limBar f (stepT f M) = limBar f M :=
  limBar_iterate_stepT m hf hc hN hM 1

/-- The points of `Tᵏ(M)` are `D / Nᵏ`-close to `limBar f M`. -/
private theorem dist_limBar_le (hf : CouplingProp f N) (hc : ConvexProp m f N) (hN : 2 ≤ N)
    {M : Multiset X} (hM : Multiset.card M = N + 1) {D : ℝ} (hD : PairBound M D) (k : ℕ)
    {y : X} (hy : y ∈ (stepT f)^[k] M) : dist (limBar f M) y ≤ D * (N : ℝ)⁻¹ ^ k := by
  have hD' := pairBound_iterate_stepT hf (by omega) hM hD k
  have h := limBar_mem m hf hc hN (M := (stepT f)^[k] M) (by rw [card_iterate_stepT, hM])
    isClosed_closedBall (isConvex_closedBall m y _)
    fun a ha ↦ mem_closedBall.2 (hD' a ha y hy)
  rwa [limBar_iterate_stepT m hf hc hN hM, mem_closedBall] at h

private theorem convexProp_limBar (hf : CouplingProp f N) (hc : ConvexProp m f N)
    (hN : 2 ≤ N) : ConvexProp m (limBar f) (N + 1) :=
  fun _ hM _ hC hCm hMC ↦ limBar_mem m hf hc hN hM hC hCm hMC

private theorem couplingProp_limBar (hf : CouplingProp f N) (hc : ConvexProp m f N)
    (hN : 2 ≤ N) : CouplingProp (limBar f) (N + 1) := by
  intro P hP
  have h₁ : Multiset.card (P.map Prod.fst) = N + 1 := by rw [Multiset.card_map, hP]
  have h₂ : Multiset.card (P.map Prod.snd) = N + 1 := by rw [Multiset.card_map, hP]
  obtain ⟨D₁, hD₁⟩ := exists_pairBound (P.map Prod.fst)
  obtain ⟨D₂, hD₂⟩ := exists_pairBound (P.map Prod.snd)
  have key : ∀ k : ℕ, ((N + 1 : ℕ) : ℝ) *
      dist (limBar f (P.map Prod.fst)) (limBar f (P.map Prod.snd)) ≤
      ((N + 1 : ℕ) : ℝ) * (D₁ * (N : ℝ)⁻¹ ^ k + D₂ * (N : ℝ)⁻¹ ^ k) +
        (P.map fun p ↦ dist p.1 p.2).sum := by
    intro k
    have hQ : Multiset.card ((stepT₂ f)^[k] P) = N + 1 := by rw [card_iterate_stepT₂, hP]
    have hle : ∀ x ∈ ((stepT₂ f)^[k] P).map (fun q ↦ dist q.1 q.2),
        dist (limBar f (P.map Prod.fst)) (limBar f (P.map Prod.snd)) -
          (D₁ * (N : ℝ)⁻¹ ^ k + D₂ * (N : ℝ)⁻¹ ^ k) ≤ x := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hx
      have hq₁ : q.1 ∈ (stepT f)^[k] (P.map Prod.fst) := by
        rw [← map_fst_iterate_stepT₂]
        exact Multiset.mem_map_of_mem _ hq
      have hq₂ : q.2 ∈ (stepT f)^[k] (P.map Prod.snd) := by
        rw [← map_snd_iterate_stepT₂]
        exact Multiset.mem_map_of_mem _ hq
      have e₁ := dist_limBar_le m hf hc hN h₁ hD₁ k hq₁
      have e₂ := dist_limBar_le m hf hc hN h₂ hD₂ k hq₂
      have h := dist_triangle4 (limBar f (P.map Prod.fst)) q.1 q.2 (limBar f (P.map Prod.snd))
      rw [dist_comm q.2] at h
      linarith
    have h := Multiset.card_nsmul_le_sum hle
    rw [Multiset.card_map, hQ, nsmul_eq_mul, mul_sub] at h
    have hcost := cost_iterate_stepT₂_le hf (by omega) hP k
    linarith
  have hr : Tendsto (fun k : ℕ ↦ (N : ℝ)⁻¹ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < N)))
  have hlim : Tendsto (fun k : ℕ ↦ ((N + 1 : ℕ) : ℝ) *
      (D₁ * (N : ℝ)⁻¹ ^ k + D₂ * (N : ℝ)⁻¹ ^ k) + (P.map fun p ↦ dist p.1 p.2).sum)
      atTop (𝓝 (((N + 1 : ℕ) : ℝ) * (D₁ * 0 + D₂ * 0) + (P.map fun p ↦ dist p.1 p.2).sum)) :=
    (((hr.const_mul D₁).add (hr.const_mul D₂)).const_mul _).add_const _
  rw [mul_zero, mul_zero, add_zero, mul_zero, zero_add] at hlim
  exact ge_of_tendsto' hlim key

end Limit

end Estimates

end Aux

/-! ### The barycenters at each level -/

section Levels

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X] [DecidableEq X]

/-- The barycenter of multisets with `n` elements (junk values for other multisets). -/
private noncomputable def baryN (m : ConicalMidpointMap X) : ℕ → Multiset X → X
  | 0, _ => Classical.arbitrary X
  | 1, M => pick M
  | 2, M => m (pick M) (pick (M.erase (pick M)))
  | n + 3, M => limBar (baryN m (n + 2)) M

variable (m : ConicalMidpointMap X)

private theorem baryN_one (a : X) : baryN m 1 {a} = a :=
  pick_singleton a

private theorem baryN_two (a b : X) : baryN m 2 {a, b} = m a b := by
  have hp : pick ({a, b} : Multiset X) ∈ ({a, b} : Multiset X) := pick_mem (by simp)
  simp only [baryN]
  rw [Multiset.insert_eq_cons] at hp ⊢
  rw [Multiset.mem_cons, Multiset.mem_singleton] at hp
  rcases hp with h | h
  · rw [h, Multiset.erase_cons_head, pick_singleton]
  · rw [h, cons_singleton_erase, pick_singleton, m.comm]

private theorem couplingProp_one : CouplingProp (baryN m 1) 1 := by
  intro P hP
  obtain ⟨p, rfl⟩ := Multiset.card_eq_one.1 hP
  simp [baryN_one]

private theorem convexProp_one : ConvexProp m (baryN m 1) 1 := by
  intro M hM C _ _ hMC
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 hM
  rw [baryN_one]
  exact hMC a (Multiset.mem_singleton_self a)

private theorem couplingProp_two : CouplingProp (baryN m 2) 2 := by
  intro P hP
  obtain ⟨p, q, rfl⟩ := Multiset.card_eq_two.1 hP
  have h1 : ({p, q} : Multiset (X × X)).map Prod.fst = {p.1, q.1} := by simp
  have h2 : ({p, q} : Multiset (X × X)).map Prod.snd = {p.2, q.2} := by simp
  rw [h1, h2, baryN_two, baryN_two]
  have h := m.dist_le_add p.1 q.1 p.2 q.2
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, Nat.cast_ofNat]
  linarith

private theorem convexProp_two : ConvexProp m (baryN m 2) 2 := by
  intro M hM C _ hCm hMC
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 hM
  rw [baryN_two]
  exact hCm a (hMC a (by simp)) b (hMC b (by simp))

/-- Properties (i) and (iv) of Theorem 6.1 at every level `n + 1`. -/
private theorem good_baryN (n : ℕ) :
    CouplingProp (baryN m (n + 1)) (n + 1) ∧ ConvexProp m (baryN m (n + 1)) (n + 1) := by
  induction n with
  | zero => exact ⟨couplingProp_one m, convexProp_one m⟩
  | succ n ih =>
    rcases n with _ | n
    · exact ⟨couplingProp_two m, convexProp_two m⟩
    · exact ⟨couplingProp_limBar m ih.1 ih.2 (by omega),
        convexProp_limBar m ih.1 ih.2 (by omega)⟩

omit [DecidableEq X] in
private theorem baryN_congr (i₁ i₂ : DecidableEq X) (n : ℕ) (M : Multiset X) :
    @baryN X _ _ _ i₁ m n M = @baryN X _ _ _ i₂ m n M := by
  obtain rfl := Subsingleton.elim i₁ i₂
  rfl

end Levels

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X] (m : ConicalMidpointMap X)

/-- The Es-Sahib–Heinich barycenter of a finite multiset of points (Theorem 6.1 of Descombes'
thesis; junk value for `0`). -/
noncomputable def baryM (m : ConicalMidpointMap X) : Multiset X → X := by
  classical
  exact fun M ↦ baryN m (Multiset.card M) M

private theorem baryM_eq_baryN [DecidableEq X] (M : Multiset X) :
    m.baryM M = baryN m (Multiset.card M) M :=
  baryN_congr m _ _ _ _

/-- The barycenter of a single point is the point. -/
theorem baryM_singleton (a : X) : m.baryM {a} = a := by
  classical
  rw [baryM_eq_baryN, Multiset.card_singleton]
  exact baryN_one m a

/-- The barycenter of two points is their midpoint `m a b`. -/
theorem baryM_pair (a b : X) : m.baryM {a, b} = m a b := by
  classical
  rw [baryM_eq_baryN, Multiset.card_pair]
  exact baryN_two m a b

/-- **Theorem 6.1 (iv)** of Descombes' thesis: the barycenter map is `1`-Lipschitz for the
average cost of a pairing: if `P` is a nonempty multiset of pairs, then the barycenters of its two
marginals are at distance at most `(1/#P) ∑_{(a, b) ∈ P} d(a, b)`. -/
theorem dist_baryM_le (P : Multiset (X × X)) (hP : P ≠ 0) :
    dist (m.baryM (P.map Prod.fst)) (m.baryM (P.map Prod.snd)) ≤
      (P.map fun p ↦ dist p.1 p.2).sum / Multiset.card P := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, Multiset.card P = n + 1 :=
    ⟨Multiset.card P - 1, by have := Multiset.card_pos.2 hP; omega⟩
  rw [baryM_eq_baryN, baryM_eq_baryN, Multiset.card_map, Multiset.card_map, hn,
    le_div_iff₀ (by positivity)]
  have h := (good_baryN m n).1 P hn
  linarith

/-- **Theorem 6.1 (i)** of Descombes' thesis: the barycenter lies in every closed `m`-convex set
containing the points. -/
theorem baryM_mem {C : Set X} (hCc : IsClosed C) (hC : m.IsConvex C) {M : Multiset X}
    (hM : M ≠ 0) (hMC : ∀ a ∈ M, a ∈ C) : m.baryM M ∈ C := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, Multiset.card M = n + 1 :=
    ⟨Multiset.card M - 1, by have := Multiset.card_pos.2 hM; omega⟩
  rw [baryM_eq_baryN, hn]
  exact (good_baryN m n).2 M hn C hCc hC hMC

/-- The barycenter of `n ≥ 1` copies of `a` is `a`. -/
theorem baryM_replicate {n : ℕ} (hn : n ≠ 0) (a : X) :
    m.baryM (Multiset.replicate n a) = a :=
  m.baryM_mem isClosed_singleton (isConvex_singleton m a)
    (Multiset.card_pos.1 (by rw [Multiset.card_replicate]; omega))
    fun _ hb ↦ Multiset.eq_of_mem_replicate hb

/-- The barycenter of `M` equals the barycenter of `T(M) = {baryM (M - {a}) : a ∈ M}` when
`#M ≥ 3` (the relation after the proof of Theorem 6.1). -/
theorem baryM_eq_baryM_map_erase [DecidableEq X] {M : Multiset X}
    (hM : 3 ≤ Multiset.card M) :
    m.baryM M = m.baryM (M.map fun a ↦ m.baryM (M.erase a)) := by
  obtain ⟨n, hn⟩ : ∃ n, Multiset.card M = n + 2 + 1 := ⟨Multiset.card M - 3, by omega⟩
  have hgood := good_baryN m (n + 1)
  have hmap : (M.map fun a ↦ m.baryM (M.erase a)) = stepT (baryN m (n + 2)) M := by
    refine Multiset.map_congr rfl fun a ha ↦ ?_
    rw [baryM_eq_baryN, Multiset.card_erase_of_mem ha, hn, Nat.pred_succ]
  rw [hmap, baryM_eq_baryN, baryM_eq_baryN, card_stepT, hn]
  exact (limBar_stepT m hgood.1 hgood.2 (by omega) hn).symm

end ConicalMidpointMap

end LipschitzExtension
