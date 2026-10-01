/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Barycenter.Descombes
import LipschitzExtension.Topology.MetricSpace.Bicombing.OfBarycenter

/-!
# Barycenter maps on finitely supported measures

This file proves **Theorem 6.5** of Descombes' thesis, and Theorems 2.6 and 2.7 of
[Basso2024bicombings] for finitely supported probability measures: a complete metric space with a
conical midpoint map `m` admits a barycenter map `β` on finitely supported probability measures
(`β δ_x = x` and `d(β μ, β ν) ≤ W₁(μ, ν)`, Theorem 6.5 (iii)) with `β μ` in every closed
`m`-convex set containing the support of `μ` (Theorem 6.5 (i)). Applied to the midpoint map of a
conical bicombing `σ` (Lemma 3.3 of Basso–Miesch), this gives `β μ ∈ \overline{conv}_σ(spt μ)`.
The versions of Theorems 2.6 and 2.7 for barycenter maps on `P₁(X)` are deduced from these by a
density argument (`nonempty_conicalBicombing_iff_nonempty_contractingBarycenterMap`,
`ConicalBicombing.exists_contractingBarycenterMap`).

## Main definitions

* `ConicalMidpointMap.barycenterMap`: the barycenter map on finitely supported measures defined by
  a conical midpoint map on a complete metric space (Theorem 6.5; its field
  `BarycenterMap.dist_le_W1` is Theorem 6.5 (iii)).

## Main statements

* `ConicalMidpointMap.barycenterMap_mem`: Theorem 6.5 (i), `β μ` lies in every closed `m`-convex
  set containing the support of `μ`.
* `IsGNPC.nonempty_barycenterMap`: every complete gNPC space admits a barycenter map on finitely
  supported measures (the direction of **Theorem 2.4** of [Basso2024] that the proofs there use;
  Theorem 2.4 itself is `isGNPC_iff_nonempty_contractingBarycenterMap`).
* `ConicalBicombing.exists_barycenterMap`: for a conical bicombing `σ` on a complete space there
  is a barycenter map with `β μ ∈ \overline{conv}_σ(spt μ)` (Theorem 2.7, finitely supported
  version; the midpoint map is the one of Basso–Miesch, Lemma 3.3).
* `nonempty_conicalBicombing_iff_nonempty_barycenterMap`: Theorem 2.6, finitely supported
  version.
* `ConicalBicombing.exists_reversible`: **Proposition 1.3** of Basso–Miesch (a complete space with
  a conical bicombing admits a reversible one), with the inclusion of closed convex hulls used in
  the proof of Theorem 2.7.
* `isGNPC_iff_nonempty_conicalBicombing`: a complete metric space is of generalized non-positive
  curvature if and only if it admits a conical bicombing.

## Implementation notes

The equivariance statement Theorem 6.5 (ii) is not formalized; it is not needed.

## Proof outline

Construction of `β μ`: for `N ≥ 1` let `A_N(μ)` be a multiset of `N` points of the support of `μ`
whose uniform measure approximates `μ` (round the weights `N μ(y)` down and put the remaining
points at one support point), so that `W₁(unif A_N(μ), μ) → 0`. With Descombes' consistent
barycenters `ConicalMidpointMap.baryS`,
`d(baryS A_N, baryS A_{N'}) = d(baryS (N' • A_N), baryS (N • A_{N'})) ≤ W₁(unif A_N, unif A_{N'})`
(`ConicalMidpointMap.dist_baryS_le_W1'`), so `baryS A_N(μ)` is Cauchy; `β μ` is its limit.

## References

* D. Descombes, *Spaces with convex geodesic bicombings*, PhD thesis, ETH Zürich, 2015
* [G. Basso, *Extending and improving conical bicombings*][Basso2024bicombings]
* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* G. Basso and B. Miesch, *Conical geodesic bicombings on subsets of normed vector spaces*,
  Adv. Geom. 19 (2019)
-/

open Set Metric Filter Topology

namespace LipschitzExtension

/-- A sequence `u` with `d(u k, u l) ≤ a k + a l` for all `k`, `l`, where `a k → 0`, is
Cauchy. -/
theorem cauchySeq_of_dist_le_add {Y : Type*} [PseudoMetricSpace Y] {u : ℕ → Y}
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (h : ∀ k l, dist (u k) (u l) ≤ a k + a l) :
    CauchySeq u := by
  refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ha.eventually (gt_mem_nhds (half_pos hε)))
  exact ⟨N, fun n hn ↦ by linarith [h n N, hN n hn, hN N le_rfl]⟩

namespace FinProb

section Weights

variable {X : Type*}

/-- The support of a finitely supported probability measure is nonempty. -/
theorem support_nonempty (μ : FinProb X) : μ.w.support.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have h1 := μ.sum_eq_one
  rw [Finsupp.sum, h, Finset.sum_empty] at h1
  exact zero_ne_one h1

/-- The weights of `μ` sum to `1` over every finset containing the support. -/
theorem sum_eq_one_of_support_subset (μ : FinProb X) {S : Finset X} (hS : μ.w.support ⊆ S) :
    ∑ y ∈ S, μ.w y = 1 := by
  rw [← μ.sum_eq_one, Finsupp.sum]
  exact (Finset.sum_subset hS fun y _ hy ↦ Finsupp.notMem_support_iff.1 hy).symm

/-- `μ = ∑_{y ∈ S} μ(y) δ_y` for every finset `S` containing the support of `μ`. -/
theorem eq_ofWeights_id (μ : FinProb X) {S : Finset X} (hS : μ.w.support ⊆ S) :
    μ = ofWeights S id μ.w (fun y _ ↦ μ.nonneg y) (μ.sum_eq_one_of_support_subset hS) := by
  classical
  refine ext_w (Finsupp.ext fun z ↦ ?_)
  change μ.w z = (∑ y ∈ S, μ.w y • Finsupp.single (id y) (1 : ℝ)) z
  rw [Finsupp.finsetSum_apply]
  simp only [id, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq']
  split_ifs with hz
  · rfl
  · exact Finsupp.notMem_support_iff.1 fun h ↦ hz (hS h)

end Weights

section Approx

variable {X : Type*}

/-- A point of the support of `μ`. -/
private noncomputable def supportPt (μ : FinProb X) : X :=
  μ.support_nonempty.choose

private theorem supportPt_mem (μ : FinProb X) : μ.supportPt ∈ μ.w.support :=
  μ.support_nonempty.choose_spec

/-- The counts `⌊N μ(y)⌋₊`. -/
private noncomputable def floorCount (N : ℕ) (μ : FinProb X) : X →₀ ℕ :=
  μ.w.mapRange (fun a ↦ ⌊(N : ℝ) * a⌋₊) (by simp)

/-- `∑_y ⌊N μ(y)⌋₊`. -/
private noncomputable def floorSum (N : ℕ) (μ : FinProb X) : ℕ :=
  ∑ y ∈ μ.w.support, ⌊(N : ℝ) * μ.w y⌋₊

/-- The approximating multiset `A_N(μ)`: `⌊N μ(y)⌋₊` copies of every `y`, and the remaining
`N - ∑_y ⌊N μ(y)⌋₊` points at a fixed point of the support. -/
private noncomputable def approx (N : ℕ) (μ : FinProb X) : Multiset X :=
  Finsupp.toMultiset (floorCount N μ + Finsupp.single μ.supportPt (N - floorSum N μ))

private theorem floorSum_le (N : ℕ) (μ : FinProb X) : floorSum N μ ≤ N := by
  have h : (floorSum N μ : ℝ) ≤ N := by
    rw [floorSum, Nat.cast_sum]
    calc ∑ y ∈ μ.w.support, (⌊(N : ℝ) * μ.w y⌋₊ : ℝ)
        ≤ ∑ y ∈ μ.w.support, (N : ℝ) * μ.w y :=
          Finset.sum_le_sum fun y _ ↦ Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (μ.nonneg y))
      _ = N := by rw [← Finset.mul_sum, μ.sum_eq_one_of_support_subset subset_rfl, mul_one]
  exact_mod_cast h

private theorem le_floorSum_add (N : ℕ) (μ : FinProb X) :
    N ≤ floorSum N μ + μ.w.support.card := by
  have h : (N : ℝ) ≤ floorSum N μ + μ.w.support.card := by
    rw [floorSum, Nat.cast_sum, Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_add_distrib]
    calc (N : ℝ) = ∑ y ∈ μ.w.support, (N : ℝ) * μ.w y := by
          rw [← Finset.mul_sum, μ.sum_eq_one_of_support_subset subset_rfl, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun y _ ↦ by
          rw [Nat.cast_one]
          exact (Nat.lt_floor_add_one _).le
  exact_mod_cast h

private theorem count_approx [DecidableEq X] (N : ℕ) (μ : FinProb X) (y : X) :
    (approx N μ).count y =
      ⌊(N : ℝ) * μ.w y⌋₊ + if μ.supportPt = y then N - floorSum N μ else 0 := by
  rw [approx, Finsupp.count_toMultiset, Finsupp.add_apply, floorCount, Finsupp.mapRange_apply,
    Finsupp.single_apply]

private theorem card_approx (N : ℕ) (μ : FinProb X) : Multiset.card (approx N μ) = N := by
  rw [approx, map_add, Multiset.card_add, Finsupp.toMultiset_single, Multiset.card_nsmul,
    Multiset.card_singleton, mul_one, Finsupp.card_toMultiset, floorCount,
    Finsupp.sum_mapRange_index (fun _ ↦ rfl)]
  exact Nat.add_sub_cancel' (floorSum_le N μ)

private theorem approx_ne_zero {N : ℕ} (hN : N ≠ 0) (μ : FinProb X) : approx N μ ≠ 0 := by
  intro h
  have h1 := card_approx N μ
  rw [h, Multiset.card_zero] at h1
  exact hN h1.symm

private theorem mem_approx {N : ℕ} {μ : FinProb X} {y : X} (hy : y ∈ approx N μ) :
    y ∈ μ.w.support := by
  classical
  by_contra h
  rw [← Multiset.count_ne_zero, count_approx, Finsupp.notMem_support_iff.1 h, mul_zero,
    Nat.floor_zero, zero_add] at hy
  split_ifs at hy with e
  · exact h (e ▸ μ.supportPt_mem)
  · exact hy rfl

private theorem approx_dirac (N : ℕ) (x : X) : approx N (dirac x) = Multiset.replicate N x := by
  refine Multiset.eq_replicate.2 ⟨card_approx N _, fun b hb ↦ ?_⟩
  have h := mem_approx hb
  change b ∈ (Finsupp.single x (1 : ℝ)).support at h
  rwa [Finsupp.support_single x one_ne_zero, Finset.mem_singleton] at h

variable [PseudoMetricSpace X]

/-- The sum of the distances between points of the support of `μ`. -/
private noncomputable def diamSum (μ : FinProb X) : ℝ :=
  ∑ y ∈ μ.w.support, ∑ z ∈ μ.w.support, dist y z

/-- The error bound for `W₁(unif A_{k+1}(μ), μ)`. -/
private noncomputable def approxErr (μ : FinProb X) (k : ℕ) : ℝ :=
  μ.diamSum * (μ.w.support.card * (1 + μ.w.support.card)) * (1 / ((k : ℝ) + 1))

private theorem tendsto_approxErr (μ : FinProb X) : Tendsto μ.approxErr atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    (μ.diamSum * (μ.w.support.card * (1 + μ.w.support.card)))
  rwa [mul_zero] at h

private theorem W1_approx_le (μ : FinProb X) (k : ℕ) :
    W1 (ofMultiset (approx (k + 1) μ) (approx_ne_zero k.succ_ne_zero μ)) μ ≤ μ.approxErr k := by
  classical
  set S := μ.w.support
  set ν := ofMultiset (approx (k + 1) μ) (approx_ne_zero k.succ_ne_zero μ) with hν_def
  have hνS : ν.w.support ⊆ S := by
    intro y hy
    rw [hν_def, support_ofMultiset, Multiset.mem_toFinset] at hy
    exact mem_approx hy
  have hD0 : 0 ≤ μ.diamSum := Finset.sum_nonneg fun y _ ↦ Finset.sum_nonneg fun z _ ↦ dist_nonneg
  have hD : ∀ i ∈ S, ∀ j ∈ S, dist (id i) (id j) ≤ μ.diamSum := fun i hi j hj ↦
    (Finset.single_le_sum (fun z _ ↦ dist_nonneg) hj).trans
      (Finset.single_le_sum (f := fun y ↦ ∑ z ∈ S, dist y z)
        (fun y _ ↦ Finset.sum_nonneg fun z _ ↦ dist_nonneg) hi)
  have hN : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  -- every weight is off by at most `(1 + #S) / (k + 1)`
  have hterm : ∀ y ∈ S, |ν.w y - μ.w y| ≤ (1 + S.card) * (1 / ((k : ℝ) + 1)) := by
    intro y _
    obtain ⟨c, hc, hcount⟩ : ∃ c : ℕ, c ≤ S.card ∧
        (approx (k + 1) μ).count y = ⌊((k + 1 : ℕ) : ℝ) * μ.w y⌋₊ + c := by
      refine ⟨_, ?_, count_approx (k + 1) μ y⟩
      split_ifs
      · exact tsub_le_iff_left.2 (le_floorSum_add (k + 1) μ)
      · exact Nat.zero_le _
    have hfl := Nat.floor_le (mul_nonneg (Nat.cast_nonneg (k + 1)) (μ.nonneg y))
    have hfl' := Nat.lt_floor_add_one (((k + 1 : ℕ) : ℝ) * μ.w y)
    have hc' : (c : ℝ) ≤ S.card := by exact_mod_cast hc
    rw [hν_def, ofMultiset_w_apply, card_approx, hcount]
    push_cast at hfl hfl' ⊢
    have key : |(⌊((k : ℝ) + 1) * μ.w y⌋₊ + c : ℝ) - ((k : ℝ) + 1) * μ.w y| ≤ 1 + S.card :=
      abs_le.2 ⟨by linarith [Nat.cast_nonneg (α := ℝ) c], by linarith⟩
    have e : (⌊((k : ℝ) + 1) * μ.w y⌋₊ + c : ℝ) / ((k : ℝ) + 1) - μ.w y =
        ((⌊((k : ℝ) + 1) * μ.w y⌋₊ + c : ℝ) - ((k : ℝ) + 1) * μ.w y) * (1 / ((k : ℝ) + 1)) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (one_div_pos.2 hN)]
    exact mul_le_mul_of_nonneg_right key (one_div_pos.2 hN).le
  calc W1 ν μ = W1 (ofWeights S id ν.w (fun y _ ↦ ν.nonneg y)
          (ν.sum_eq_one_of_support_subset hνS))
        (ofWeights S id μ.w (fun y _ ↦ μ.nonneg y) (μ.sum_eq_one_of_support_subset subset_rfl)) :=
        congrArg₂ W1 (ν.eq_ofWeights_id hνS) (μ.eq_ofWeights_id subset_rfl)
    _ ≤ μ.diamSum / 2 * ∑ y ∈ S, |ν.w y - μ.w y| := W1_ofWeights_le S id _ _ _ _ hD
    _ ≤ μ.diamSum / 2 * ∑ y ∈ S, (1 + S.card) * (1 / ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (div_nonneg hD0 zero_le_two)
    _ ≤ μ.approxErr k := by
        rw [Finset.sum_const, nsmul_eq_mul, approxErr]
        have h1 : 0 ≤ (S.card : ℝ) * ((1 + S.card) * (1 / ((k : ℝ) + 1))) := by positivity
        nlinarith

end Approx

end FinProb

namespace ConicalMidpointMap

variable {X : Type*} [MetricSpace X] [CompleteSpace X] (m : ConicalMidpointMap X)

section Aux

variable [Nonempty X]

private theorem dist_baryS_approx_le (μ ν : FinProb X) (k l : ℕ) :
    dist (m.baryS (FinProb.approx (k + 1) μ)) (m.baryS (FinProb.approx (l + 1) ν)) ≤
      μ.approxErr k + FinProb.W1 μ ν + ν.approxErr l := by
  refine (m.dist_baryS_le_W1' (FinProb.approx_ne_zero k.succ_ne_zero μ)
    (FinProb.approx_ne_zero l.succ_ne_zero ν)).trans ?_
  have h1 := FinProb.W1_approx_le μ k
  have h2 := FinProb.W1_approx_le ν l
  rw [FinProb.W1_comm] at h2
  have h3 := FinProb.W1_triangle
    (FinProb.ofMultiset (FinProb.approx (k + 1) μ) (FinProb.approx_ne_zero k.succ_ne_zero μ)) μ
    (FinProb.ofMultiset (FinProb.approx (l + 1) ν) (FinProb.approx_ne_zero l.succ_ne_zero ν))
  have h4 := FinProb.W1_triangle μ ν
    (FinProb.ofMultiset (FinProb.approx (l + 1) ν) (FinProb.approx_ne_zero l.succ_ne_zero ν))
  linarith

/-- The barycenter `lim_k baryS (A_{k+1}(μ))`. -/
private noncomputable def baryAux (μ : FinProb X) : X :=
  limUnder atTop fun k : ℕ ↦ m.baryS (FinProb.approx (k + 1) μ)

private theorem tendsto_baryAux (μ : FinProb X) :
    Tendsto (fun k : ℕ ↦ m.baryS (FinProb.approx (k + 1) μ)) atTop (𝓝 (m.baryAux μ)) := by
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
  refine cauchySeq_of_dist_le_add (FinProb.tendsto_approxErr μ) fun k l ↦ ?_
  have h := m.dist_baryS_approx_le μ μ k l
  rwa [FinProb.W1_self, add_zero] at h

private theorem dist_baryAux_le (μ ν : FinProb X) :
    dist (m.baryAux μ) (m.baryAux ν) ≤ FinProb.W1 μ ν := by
  have h := ((FinProb.tendsto_approxErr μ).add_const (FinProb.W1 μ ν)).add
    (FinProb.tendsto_approxErr ν)
  rw [zero_add, add_zero] at h
  exact le_of_tendsto_of_tendsto' ((m.tendsto_baryAux μ).dist (m.tendsto_baryAux ν)) h
    fun k ↦ m.dist_baryS_approx_le μ ν k k

private theorem baryAux_dirac (x : X) : m.baryAux (FinProb.dirac x) = x := by
  refine tendsto_nhds_unique (m.tendsto_baryAux _) (tendsto_const_nhds.congr fun k ↦ ?_)
  rw [FinProb.approx_dirac, m.baryS_replicate k.succ_ne_zero]

private theorem baryAux_mem {C : Set X} (hCc : IsClosed C) (hC : m.IsConvex C) (μ : FinProb X)
    (hμ : (μ.w.support : Set X) ⊆ C) : m.baryAux μ ∈ C :=
  hCc.mem_of_tendsto (m.tendsto_baryAux μ) (Eventually.of_forall fun k ↦
    m.baryS_mem hCc hC (FinProb.approx_ne_zero k.succ_ne_zero μ) fun _ ha ↦
      hμ (FinProb.mem_approx ha))

end Aux

/-- **Theorem 6.5** of Descombes' thesis: the barycenter map on finitely supported measures
defined by a conical midpoint map on a complete space. The field `BarycenterMap.dist_le_W1` is
Theorem 6.5 (iii); (i) is `ConicalMidpointMap.barycenterMap_mem`. -/
noncomputable def barycenterMap (m : ConicalMidpointMap X) : BarycenterMap X where
  bary μ := haveI : Nonempty X := ⟨μ.supportPt⟩; m.baryAux μ
  bary_dirac x := haveI : Nonempty X := ⟨x⟩; m.baryAux_dirac x
  dist_le_W1 μ ν := haveI : Nonempty X := ⟨μ.supportPt⟩; m.dist_baryAux_le μ ν

/-- **Theorem 6.5 (i)** of Descombes' thesis: `β μ` lies in every closed `m`-convex set
containing the support of `μ`. -/
theorem barycenterMap_mem {C : Set X} (hCc : IsClosed C) (hC : m.IsConvex C) (μ : FinProb X)
    (hμ : (μ.w.support : Set X) ⊆ C) : m.barycenterMap.bary μ ∈ C := by
  have : Nonempty X := ⟨μ.supportPt⟩
  exact m.baryAux_mem hCc hC μ hμ

end ConicalMidpointMap

/-- **Theorem 2.4** of [Basso2024] (Es-Sahib–Heinich, Navas, Descombes), the direction used in
that paper: every complete metric space of generalized non-positive curvature admits a barycenter
map (on finitely supported measures). -/
theorem IsGNPC.nonempty_barycenterMap {X : Type*} [MetricSpace X] [CompleteSpace X]
    (h : IsGNPC X) : Nonempty (BarycenterMap X) := by
  obtain ⟨m⟩ := isGNPC_iff_nonempty_conicalMidpointMap.1 h
  exact ⟨m.barycenterMap⟩

/-- **Theorem 2.7** of [Basso2024bicombings], for finitely supported measures: a conical
bicombing `σ` on a complete metric space gives a barycenter map with
`β μ ∈ \overline{conv}_σ(spt μ)`. -/
theorem ConicalBicombing.exists_barycenterMap {X : Type*} [MetricSpace X] [CompleteSpace X]
    (σ : ConicalBicombing X) :
    ∃ β : BarycenterMap X, ∀ μ : FinProb X, β.bary μ ∈ closure (σ.convexHull μ.w.support) :=
  ⟨σ.midpointMap.barycenterMap, fun μ ↦ σ.midpointMap.barycenterMap_mem isClosed_closure
    (σ.isConvex_midpointMap (σ.isConvex_closure_convexHull _) isClosed_closure) μ
    ((σ.subset_convexHull _).trans subset_closure)⟩

/-- **Theorem 2.6** of [Basso2024bicombings], for finitely supported measures: a complete metric
space admits a conical bicombing iff it admits a barycenter map. -/
theorem nonempty_conicalBicombing_iff_nonempty_barycenterMap {X : Type*} [MetricSpace X]
    [CompleteSpace X] : Nonempty (ConicalBicombing X) ↔ Nonempty (BarycenterMap X) :=
  ⟨fun ⟨σ⟩ ↦ ⟨σ.midpointMap.barycenterMap⟩, fun ⟨β⟩ ↦ ⟨β.toConicalBicombing⟩⟩

/-- **Proposition 1.3** of G. Basso and B. Miesch, *Conical geodesic bicombings on subsets of
normed vector spaces* (Adv. Geom. 19 (2019)), with the inclusion of closed convex hulls used in the
proof of Theorem 2.7 of [Basso2024bicombings]: if `X` is complete, every conical bicombing `σ` on
`X` gives a reversible conical bicombing `τ` with `\overline{conv}_τ(A) ⊆ \overline{conv}_σ(A)`
for all `A ⊆ X`. We take `τ = σ_β` (Lemma 2.5 of [Basso2024bicombings]) for the barycenter map
`β` of `ConicalBicombing.exists_barycenterMap`; Basso–Miesch use
`τ(x, y, t) = m(σ(x, y, t), σ(y, x, 1 - t))` with the midpoint map `m` of their Lemma 3.3. -/
theorem ConicalBicombing.exists_reversible {X : Type*} [MetricSpace X] [CompleteSpace X]
    (σ : ConicalBicombing X) :
    ∃ τ : ConicalBicombing X, τ.IsReversible ∧
      ∀ A : Set X, closure (τ.convexHull A) ⊆ closure (σ.convexHull A) := by
  obtain ⟨β, hβ⟩ := σ.exists_barycenterMap
  refine ⟨β.toConicalBicombing, β.isReversible_toConicalBicombing, fun A ↦ ?_⟩
  refine β.toConicalBicombing.closure_convexHull_subset ?_ isClosed_closure
    ((σ.subset_convexHull A).trans subset_closure)
  intro x hx y hy t ht
  rw [BarycenterMap.toConicalBicombing_apply β x y ht]
  refine σ.closure_convexHull_subset (σ.isConvex_closure_convexHull A) isClosed_closure ?_ (hβ _)
  exact (FinProb.support_segment_subset x y t ht).trans
    (insert_subset_iff.2 ⟨hx, singleton_subset_iff.2 hy⟩)

/-- For complete metric spaces, being gNPC is equivalent to admitting a conical bicombing. -/
theorem isGNPC_iff_nonempty_conicalBicombing {X : Type*} [MetricSpace X] [CompleteSpace X] :
    IsGNPC X ↔ Nonempty (ConicalBicombing X) :=
  ⟨fun h ↦ nonempty_conicalBicombing_iff_nonempty_barycenterMap.2 h.nonempty_barycenterMap,
    fun ⟨σ⟩ ↦ σ.isGNPC⟩

end LipschitzExtension
