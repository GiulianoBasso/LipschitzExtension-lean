/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Bicombing.Defs
import LipschitzExtension.Topology.MetricSpace.Barycenter.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Conical midpoint maps

A *conical midpoint map* on a metric space `X` is a map `m : X × X → X` with `m x y = m y x`,
`m x x = x` and `d(m x y, m x z) ≤ d(y, z) / 2`. This is exactly the data in the definition of a
space of *generalized non-positive curvature* (`IsGNPC`, Definition 1.3 of [Basso2024]). It
follows that `m x y` is a midpoint of `x` and `y` and that
`d(m x y, m x' y') ≤ (d(x, x') + d(y, y')) / 2`. For `n = 2` the barycenters of Theorem 6.1 of
Descombes' thesis are given by such a map ("symmetric midpoint assignment").

This file also proves **Lemma 3.3** of Basso–Miesch: if `X` is complete and `σ` is a conical
bicombing on `X`, then `X` admits a conical midpoint map. We also record that it takes values in
every closed `σ`-convex set containing `x` and `y`. In particular, every complete metric space
with a conical bicombing is of generalized non-positive curvature.

## Main definitions

* `ConicalMidpointMap X`: the conical midpoint maps on `X`.
* `ConicalMidpointMap.IsConvex`: `m`-convex sets, i.e. sets `C` with `m x y ∈ C` for all
  `x, y ∈ C`.
* `ConicalBicombing.midpointMap`: the conical midpoint map of a conical bicombing on a complete
  metric space (Lemma 3.3 of Basso–Miesch).

## Main statements

* `ConicalMidpointMap.dist_le_add`: `d(m x y, m x' y') ≤ (d(x, x') + d(y, y')) / 2`.
* `ConicalMidpointMap.dist_left`, `ConicalMidpointMap.dist_right`: `m x y` is a midpoint of `x`
  and `y`.
* `isGNPC_iff_nonempty_conicalMidpointMap`: a space is of generalized non-positive curvature if
  and only if it admits a conical midpoint map.
* `ConicalBicombing.isConvex_midpointMap`: closed `σ`-convex sets are convex for the midpoint map
  of Lemma 3.3 of Basso–Miesch.
* `ConicalBicombing.isGNPC`: a complete metric space with a conical bicombing is of generalized
  non-positive curvature.

## Proof outline

For Lemma 3.3 of Basso–Miesch let `x₀ = x`, `y₀ = y`, `x_{n+1} = σ(x_n, y_n, ½)` and
`y_{n+1} = σ(y_n, x_n, ½)`. The conical inequality against the constant geodesic at `y_{n+1}`
gives `d(x_{n+1}, y_{n+1}) ≤ ½ d(x_n, y_{n+1}) + ½ d(y_n, y_{n+1}) = ½ d(x_n, y_n)`, and
`d(x_{n+1}, x_n) = ½ d(x_n, y_n)`. Hence both sequences are Cauchy with a common limit `m(x, y)`.
Symmetry holds since the construction for `(y, x)` swaps the sequences, and by induction
`d(x_n, x'_n), d(y_n, y'_n) ≤ ½ d(x, x') + ½ d(y, y')` for `n ≥ 1`. Since `σ`-convex sets contain
all `x_n, y_n`, closed `σ`-convex sets contain `m(x, y)`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* G. Basso and B. Miesch, *Conical geodesic bicombings on subsets of normed vector spaces*,
  Adv. Geom. 19 (2019)
* D. Descombes, *Spaces with convex geodesic bicombings*, PhD thesis, ETH Zürich, 2015
-/

open Set Metric Filter Topology

namespace LipschitzExtension

/-- A *conical midpoint map*: a symmetric map `m` with `m x x = x` and
`d(m x y, m x z) ≤ d(y, z) / 2` (the data of Definition 1.3 of [Basso2024]). -/
structure ConicalMidpointMap (X : Type*) [PseudoMetricSpace X] where
  /-- The midpoint map `m`. -/
  toFun : X → X → X
  /-- `m` is symmetric: `m x y = m y x`. -/
  comm : ∀ x y, toFun x y = toFun y x
  /-- `m x x = x`. -/
  self : ∀ x, toFun x x = x
  /-- The conical inequality `d(m x y, m x z) ≤ d(y, z) / 2`. -/
  dist_le : ∀ x y z, dist (toFun x y) (toFun x z) ≤ dist y z / 2

namespace ConicalMidpointMap

/-- A conical midpoint map can be applied to two points. -/
instance instCoeFun {X : Type*} [PseudoMetricSpace X] :
    CoeFun (ConicalMidpointMap X) (fun _ ↦ X → X → X) :=
  ⟨ConicalMidpointMap.toFun⟩

variable {X : Type*} [MetricSpace X] (m : ConicalMidpointMap X)

/-- The conical inequality for midpoints: `d(m x y, m x' y') ≤ (d(x, x') + d(y, y')) / 2`. -/
theorem dist_le_add (x y x' y' : X) : dist (m x y) (m x' y') ≤ (dist x x' + dist y y') / 2 := by
  have h1 := m.dist_le x y y'
  have h2 := m.dist_le y' x x'
  rw [m.comm y' x, m.comm y' x'] at h2
  linarith [dist_triangle (m x y) (m x y') (m x' y')]

private theorem dist_left_le (x y : X) : dist x (m x y) ≤ dist x y / 2 := by
  have h := m.dist_le x x y
  rwa [m.self x] at h

private theorem dist_right_le (x y : X) : dist (m x y) y ≤ dist x y / 2 := by
  have h := m.dist_le y x y
  rwa [m.self y, m.comm y x] at h

/-- `m x y` is a midpoint of `x` and `y`: `d(x, m x y) = d(x, y) / 2`. -/
theorem dist_left (x y : X) : dist x (m x y) = dist x y / 2 := by
  have h1 := dist_left_le m x y
  have h2 := dist_right_le m x y
  linarith [dist_triangle x (m x y) y]

/-- `m x y` is a midpoint of `x` and `y`: `d(m x y, y) = d(x, y) / 2`. -/
theorem dist_right (x y : X) : dist (m x y) y = dist x y / 2 := by
  have h1 := dist_left_le m x y
  have h2 := dist_right_le m x y
  linarith [dist_triangle x (m x y) y]

/-- A set `C` is `m`-convex if `m x y ∈ C` for all `x, y ∈ C`. -/
def IsConvex (C : Set X) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, m x y ∈ C

end ConicalMidpointMap

/-- A space is of generalized non-positive curvature (Definition 1.3 of [Basso2024]) iff it
admits a conical midpoint map. -/
theorem isGNPC_iff_nonempty_conicalMidpointMap {X : Type*} [PseudoMetricSpace X] :
    IsGNPC X ↔ Nonempty (ConicalMidpointMap X) := by
  constructor
  · rintro ⟨m, hcomm, hself, hdist⟩
    exact ⟨⟨m, hcomm, hself, hdist⟩⟩
  · rintro ⟨m⟩
    exact ⟨m.toFun, m.comm, m.self, m.dist_le⟩

namespace ConicalBicombing

section Construction

variable {X : Type*} [MetricSpace X] (σ : ConicalBicombing X)

private theorem half_mem_Icc : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

/-- One step `(x, y) ↦ (σ(x, y, ½), σ(y, x, ½))` of the construction of Lemma 3.3. -/
private noncomputable def midStep (p : X × X) : X × X :=
  (σ p.1 p.2 (1 / 2), σ p.2 p.1 (1 / 2))

/-- The pair sequence `(x_n, y_n)` of Lemma 3.3. -/
private noncomputable def midSeq (x y : X) (n : ℕ) : X × X :=
  (midStep σ)^[n] (x, y)

private theorem midSeq_zero (x y : X) : midSeq σ x y 0 = (x, y) := rfl

private theorem midSeq_succ (x y : X) (n : ℕ) :
    midSeq σ x y (n + 1) = midStep σ (midSeq σ x y n) :=
  Function.iterate_succ_apply' _ _ _

/-- The construction for `(y, x)` swaps the two sequences. -/
private theorem midSeq_swap (x y : X) (n : ℕ) : midSeq σ y x n = (midSeq σ x y n).swap := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [midSeq_succ, midSeq_succ, ih]
    rfl

private theorem midSeq_self (x : X) (n : ℕ) : midSeq σ x x n = (x, x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [midSeq_succ, ih]
    exact Prod.ext (σ.toFun_self x half_mem_Icc) (σ.toFun_self x half_mem_Icc)

private theorem dist_midStep_fst (p : X × X) : dist (midStep σ p).1 p.1 = dist p.1 p.2 / 2 := by
  change dist (σ p.1 p.2 (1 / 2)) p.1 = _
  rw [dist_comm, σ.dist_toFun_left p.1 p.2 half_mem_Icc]
  ring

private theorem dist_midStep_snd (p : X × X) : dist (midStep σ p).2 p.2 = dist p.1 p.2 / 2 := by
  change dist (σ p.2 p.1 (1 / 2)) p.2 = _
  rw [dist_comm, σ.dist_toFun_left p.2 p.1 half_mem_Icc, dist_comm]
  ring

private theorem dist_midStep_snd_fst (p : X × X) :
    dist (midStep σ p).2 p.1 = dist p.1 p.2 / 2 := by
  change dist (σ p.2 p.1 (1 / 2)) p.1 = _
  rw [σ.dist_toFun_right p.2 p.1 half_mem_Icc, dist_comm]
  ring

/-- `d(x_{n+1}, y_{n+1}) ≤ ½ d(x_n, y_n)`: the conical inequality against the constant geodesic
at `y_{n+1}`. -/
private theorem dist_midStep_le (p : X × X) :
    dist (midStep σ p).1 (midStep σ p).2 ≤ dist p.1 p.2 / 2 := by
  have h := σ.dist_toFun_le p.1 p.2 (midStep σ p).2 half_mem_Icc
  rw [dist_comm p.1, dist_comm p.2, dist_midStep_snd_fst, dist_midStep_snd] at h
  change dist (σ p.1 p.2 (1 / 2)) (midStep σ p).2 ≤ _
  linarith

private theorem dist_midStep_fst_le (p q : X × X) :
    dist (midStep σ p).1 (midStep σ q).1 ≤ (dist p.1 q.1 + dist p.2 q.2) / 2 := by
  have h := σ.conical p.1 p.2 q.1 q.2 half_mem_Icc
  change dist (σ p.1 p.2 (1 / 2)) (σ q.1 q.2 (1 / 2)) ≤ _
  linarith

private theorem dist_midStep_snd_le (p q : X × X) :
    dist (midStep σ p).2 (midStep σ q).2 ≤ (dist p.1 q.1 + dist p.2 q.2) / 2 := by
  have h := σ.conical p.2 p.1 q.2 q.1 half_mem_Icc
  change dist (σ p.2 p.1 (1 / 2)) (σ q.2 q.1 (1 / 2)) ≤ _
  linarith

private theorem dist_midSeq_le (x y : X) (n : ℕ) :
    dist (midSeq σ x y n).1 (midSeq σ x y n).2 ≤ dist x y * (1 / 2) ^ n := by
  induction n with
  | zero =>
    rw [midSeq_zero, pow_zero, mul_one]
  | succ n ih =>
    rw [midSeq_succ, pow_succ]
    calc dist (midStep σ (midSeq σ x y n)).1 (midStep σ (midSeq σ x y n)).2
        ≤ dist (midSeq σ x y n).1 (midSeq σ x y n).2 / 2 := dist_midStep_le σ _
      _ ≤ dist x y * (1 / 2) ^ n / 2 := by gcongr
      _ = dist x y * ((1 / 2) ^ n * (1 / 2)) := by ring

private theorem dist_midSeq_succ_le (x y : X) (n : ℕ) :
    dist (midSeq σ x y n).1 (midSeq σ x y (n + 1)).1 ≤ dist x y / 2 * (1 / 2) ^ n := by
  rw [midSeq_succ, dist_comm, dist_midStep_fst]
  calc dist (midSeq σ x y n).1 (midSeq σ x y n).2 / 2 ≤ dist x y * (1 / 2) ^ n / 2 := by
        gcongr
        exact dist_midSeq_le σ x y n
    _ = dist x y / 2 * (1 / 2) ^ n := by ring

private theorem cauchySeq_midSeq (x y : X) : CauchySeq fun n ↦ (midSeq σ x y n).1 :=
  cauchySeq_of_le_geometric (1 / 2) (dist x y / 2) (by norm_num) (dist_midSeq_succ_le σ x y)

private theorem tendsto_dist_midSeq (x y : X) :
    Tendsto (fun n ↦ dist (midSeq σ x y n).1 (midSeq σ x y n).2) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).const_mul (dist x y)
  rw [mul_zero] at h
  exact squeeze_zero (fun _ ↦ dist_nonneg) (dist_midSeq_le σ x y) h

/-- `d(x_n, x'_n), d(y_n, y'_n) ≤ ½ d(x, x') + ½ d(y, y')` for `n ≥ 1`. -/
private theorem dist_midSeq_midSeq_le (x y x' y' : X) (n : ℕ) :
    dist (midSeq σ x y (n + 1)).1 (midSeq σ x' y' (n + 1)).1 ≤ (dist x x' + dist y y') / 2 ∧
      dist (midSeq σ x y (n + 1)).2 (midSeq σ x' y' (n + 1)).2 ≤
        (dist x x' + dist y y') / 2 := by
  induction n with
  | zero =>
    rw [midSeq_succ, midSeq_succ, midSeq_zero, midSeq_zero]
    exact ⟨dist_midStep_fst_le σ _ _, dist_midStep_snd_le σ _ _⟩
  | succ n ih =>
    rw [midSeq_succ σ x y (n + 1), midSeq_succ σ x' y' (n + 1)]
    constructor
    · refine (dist_midStep_fst_le σ _ _).trans ?_
      linarith [ih.1, ih.2]
    · refine (dist_midStep_snd_le σ _ _).trans ?_
      linarith [ih.1, ih.2]

/-- All `x_n, y_n` lie in every `σ`-convex set containing `x` and `y`. -/
private theorem mem_midSeq {C : Set X} (hC : σ.IsConvex C) {x y : X} (hx : x ∈ C) (hy : y ∈ C)
    (n : ℕ) : (midSeq σ x y n).1 ∈ C ∧ (midSeq σ x y n).2 ∈ C := by
  induction n with
  | zero => exact ⟨hx, hy⟩
  | succ n ih =>
    rw [midSeq_succ]
    exact ⟨hC _ ih.1 _ ih.2 _ half_mem_Icc, hC _ ih.2 _ ih.1 _ half_mem_Icc⟩

end Construction

variable {X : Type*} [MetricSpace X] [CompleteSpace X] (σ : ConicalBicombing X)

/-- The midpoint `m(x, y)` of Lemma 3.3: the limit of the Cauchy sequence `x_n`. -/
private noncomputable def midLim (x y : X) : X :=
  (cauchySeq_tendsto_of_complete (cauchySeq_midSeq σ x y)).choose

private theorem tendsto_midLim_fst (x y : X) :
    Tendsto (fun n ↦ (midSeq σ x y n).1) atTop (𝓝 (midLim σ x y)) :=
  (cauchySeq_tendsto_of_complete (cauchySeq_midSeq σ x y)).choose_spec

private theorem tendsto_midLim_snd (x y : X) :
    Tendsto (fun n ↦ (midSeq σ x y n).2) atTop (𝓝 (midLim σ x y)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have h := (tendsto_dist_midSeq σ x y).add
    (tendsto_iff_dist_tendsto_zero.1 (tendsto_midLim_fst σ x y))
  rw [add_zero] at h
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) h
  exact dist_triangle_left _ _ _

private theorem midLim_comm (x y : X) : midLim σ x y = midLim σ y x := by
  have h : Tendsto (fun n ↦ (midSeq σ y x n).1) atTop (𝓝 (midLim σ x y)) :=
    (tendsto_midLim_snd σ x y).congr fun n ↦ (congrArg Prod.fst (midSeq_swap σ x y n)).symm
  exact tendsto_nhds_unique h (tendsto_midLim_fst σ y x)

private theorem midLim_self (x : X) : midLim σ x x = x := by
  have h : Tendsto (fun n ↦ (midSeq σ x x n).1) atTop (𝓝 x) :=
    tendsto_const_nhds.congr fun n ↦ (congrArg Prod.fst (midSeq_self σ x n)).symm
  exact tendsto_nhds_unique (tendsto_midLim_fst σ x x) h

private theorem dist_midLim_le (x y x' y' : X) :
    dist (midLim σ x y) (midLim σ x' y') ≤ (dist x x' + dist y y') / 2 := by
  have h := ((tendsto_midLim_fst σ x y).comp (tendsto_add_atTop_nat 1)).dist
    ((tendsto_midLim_fst σ x' y').comp (tendsto_add_atTop_nat 1))
  exact le_of_tendsto' h fun n ↦ (dist_midSeq_midSeq_le σ x y x' y' n).1

/-- **Lemma 3.3** of Basso–Miesch: the symmetric conical midpoint map `m(x, y)` of a conical
bicombing `σ` on a complete metric space, obtained as the common limit of the sequences
`x₀ = x`, `y₀ = y`, `x_{n+1} = σ(x_n, y_n, ½)`, `y_{n+1} = σ(y_n, x_n, ½)`. -/
noncomputable def midpointMap (σ : ConicalBicombing X) : ConicalMidpointMap X where
  toFun := midLim σ
  comm := midLim_comm σ
  self := midLim_self σ
  dist_le x y z := by
    have h := dist_midLim_le σ x y x z
    rwa [dist_self, zero_add] at h

/-- Closed `σ`-convex sets are convex for the midpoint map of Lemma 3.3. -/
theorem isConvex_midpointMap {C : Set X} (hC : σ.IsConvex C) (hCc : IsClosed C) :
    σ.midpointMap.IsConvex C := by
  intro x hx y hy
  exact hCc.mem_of_tendsto (tendsto_midLim_fst σ x y)
    (Eventually.of_forall fun n ↦ (mem_midSeq σ hC hx hy n).1)

include σ in
/-- A complete metric space with a conical bicombing is of generalized non-positive curvature. -/
theorem isGNPC : IsGNPC X :=
  isGNPC_iff_nonempty_conicalMidpointMap.2 ⟨σ.midpointMap⟩

end ConicalBicombing

end LipschitzExtension
