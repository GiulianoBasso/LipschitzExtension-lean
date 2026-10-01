/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Barycenter.Construction
import LipschitzExtension.MeasureTheory.Wasserstein.Density

/-!
# Contracting barycenter maps on `P₁(X)`

This file formalizes Section 2.2 of [Basso2024bicombings] for barycenter maps defined on all of
`P₁(X)`, and deduces Theorem 2.4 of [Basso2024]. Following Sturm (Definition 2.4 of
[Basso2024bicombings]), a `1`-Lipschitz map `β : P₁(X) → X` with `β(δ_x) = x` for all `x` is a
*contracting barycenter map*; `X` is *barycentric* if it admits one. Here `W₁` is defined in
Kantorovich–Rubinstein form (`P1.W1`); see the module docstring of
`LipschitzExtension.MeasureTheory.Wasserstein.Defs` for the comparison with the paper.

## Main definitions

* `ContractingBarycenterMap X`: contracting barycenter maps `P₁(X) → X` (Definition 2.4).
* `ContractingBarycenterMap.toBarycenterMap`: the restriction of a contracting barycenter map to
  finitely supported measures.
* `ContractingBarycenterMap.toConicalBicombing`: the conical bicombing
  `σ_β(x, y, t) = β((1 - t) δ_x + t δ_y)` of Lemma 2.5.
* `BarycenterMap.extend`: the extension of a barycenter map on finitely supported measures to
  `P₁(X)`, for complete `X`.

## Main statements

* `ContractingBarycenterMap.toConicalBicombing_apply`, `FinProb.toMeasure_toP1_segment`:
  `σ_β(x, y, t) = β((1 - t) δ_x + t δ_y)` for `t ∈ [0, 1]`.
* `ContractingBarycenterMap.isReversible_toConicalBicombing`: Lemma 2.5, `σ_β` is a reversible
  conical bicombing.
* `ConicalBicombing.exists_contractingBarycenterMap`: Theorem 2.7, if `X` is complete and `σ` is a
  conical bicombing on `X`, there is a contracting barycenter map `β_σ` with
  `β_σ(μ) ∈ \overline{conv}_σ(spt μ)` for all `μ ∈ P₁(X)` (the convex hull property).
* `nonempty_conicalBicombing_iff_nonempty_contractingBarycenterMap`: Theorem 2.6, a complete
  metric space admits a conical bicombing iff it is barycentric.
* `isGNPC_iff_nonempty_contractingBarycenterMap`: Theorem 2.4 of [Basso2024], a complete metric
  space is of generalized non-positive curvature iff it admits a barycenter map `P₁(X) → X`.

## Proof outline

The proof of Theorem 2.7 follows the paper: the barycenter map on finitely supported measures
(Descombes' Theorem 6.5, `ConicalBicombing.exists_barycenterMap`) extends to `P₁(X)` because `X`
is complete and finitely supported measures with atoms in `spt μ` are dense
(`P1.exists_finProb_W1_le`); the convex hull property passes to the limit since the closed hull is
closed and monotone in the set (`BarycenterMap.extend_mem`).

## References

* [G. Basso, *Extending and improving conical bicombings*][Basso2024bicombings]
* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* D. Descombes, *Spaces with convex geodesic bicombings*, PhD thesis, ETH Zürich, 2015
-/

open MeasureTheory Set Metric Filter Topology

namespace LipschitzExtension

/-- A *contracting barycenter map* on `X` (Definition 2.4 of [Basso2024bicombings], after
Sturm): a `1`-Lipschitz map `β : P₁(X) → X` with `β(δ_x) = x`. -/
structure ContractingBarycenterMap (X : Type*) [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] where
  /-- The barycenter map `β : P₁(X) → X`. -/
  toFun : P1 X → X
  /-- `β(δ_x) = x`. -/
  toFun_dirac : ∀ x, toFun (P1.dirac x) = x
  /-- `β` is `1`-Lipschitz with respect to `W₁`. -/
  dist_le_W1 : ∀ μ ν, dist (toFun μ) (toFun ν) ≤ P1.W1 μ ν

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The measure `FinProb.segment x y t ht` used in `ContractingBarycenterMap.toConicalBicombing`
is `(1 - t) δ_x + t δ_y`. -/
theorem FinProb.toMeasure_toP1_segment (x y : X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (FinProb.segment x y t ht).toP1.toMeasure =
      ENNReal.ofReal (1 - t) • Measure.dirac x + ENNReal.ofReal t • Measure.dirac y := by
  classical
  change (FinProb.segment x y t ht).w.sum (fun z a ↦ ENNReal.ofReal a • Measure.dirac z) = _
  have hsupp : (FinProb.segment x y t ht).w.support ⊆ {x, y} := by
    rw [← Finset.coe_subset, Finset.coe_insert, Finset.coe_singleton]
    exact FinProb.support_segment_subset x y t ht
  rw [Finsupp.sum_of_support_subset _ hsupp _ (fun z _ ↦ by simp)]
  by_cases hxy : x = y
  · subst hxy
    simp only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.sum_singleton,
      FinProb.segment_w, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
    rw [← add_smul, ← ENNReal.ofReal_add (sub_nonneg.2 ht.2) ht.1]
  · rw [Finset.sum_pair hxy, FinProb.segment_w]
    simp [hxy, Ne.symm hxy]

namespace ContractingBarycenterMap

/-- The restriction of a contracting barycenter map to finitely supported measures. -/
noncomputable def toBarycenterMap (β : ContractingBarycenterMap X) : BarycenterMap X where
  bary μ := β.toFun μ.toP1
  bary_dirac x := by rw [FinProb.toP1_dirac]; exact β.toFun_dirac x
  dist_le_W1 μ ν := by rw [← FinProb.W1_toP1]; exact β.dist_le_W1 _ _

/-- **Lemma 2.5** of [Basso2024bicombings]: the conical bicombing
`σ_β(x, y, t) = β((1 - t) δ_x + t δ_y)`. -/
noncomputable def toConicalBicombing (β : ContractingBarycenterMap X) : ConicalBicombing X :=
  β.toBarycenterMap.toConicalBicombing

/-- `σ_β(x, y, t) = β((1 - t) δ_x + t δ_y)` for `t ∈ [0, 1]`: the measure
`(FinProb.segment x y t ht).toP1` is `(1 - t) δ_x + t δ_y` by `FinProb.toMeasure_toP1_segment`. -/
theorem toConicalBicombing_apply (β : ContractingBarycenterMap X) (x y : X) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    β.toConicalBicombing x y t = β.toFun (FinProb.segment x y t ht).toP1 :=
  β.toBarycenterMap.toConicalBicombing_apply x y ht

/-- **Lemma 2.5** of [Basso2024bicombings]: `σ_β` is reversible. -/
theorem isReversible_toConicalBicombing (β : ContractingBarycenterMap X) :
    β.toConicalBicombing.IsReversible :=
  β.toBarycenterMap.isReversible_toConicalBicombing

end ContractingBarycenterMap

namespace BarycenterMap

/-- `X` is nonempty if `P₁(X)` is. -/
private theorem nonempty_of_P1 (μ : P1 X) : Nonempty X :=
  let ⟨x₀, _⟩ := μ.exists_integrable_dist
  ⟨x₀⟩

/-- Finitely supported measures `ν_k` with atoms in `spt μ` and `W₁(μ, ν_k) ≤ 1 / (k + 1)`. -/
private noncomputable def approxSeq (μ : P1 X) (k : ℕ) : FinProb X :=
  (P1.exists_finProb_W1_le μ (Nat.one_div_pos_of_nat (α := ℝ) (n := k))).choose

private theorem approxSeq_support (μ : P1 X) (k : ℕ) :
    ((approxSeq μ k).w.support : Set X) ⊆ μ.toMeasure.support :=
  (P1.exists_finProb_W1_le μ (Nat.one_div_pos_of_nat (α := ℝ) (n := k))).choose_spec.1

private theorem W1_approxSeq_le (μ : P1 X) (k : ℕ) :
    P1.W1 μ (approxSeq μ k).toP1 ≤ 1 / ((k : ℝ) + 1) :=
  (P1.exists_finProb_W1_le μ (Nat.one_div_pos_of_nat (α := ℝ) (n := k))).choose_spec.2

/-- `d(β ν, β ν') ≤ W₁(μ, ν) + W₁(μ, ν')`. -/
private theorem dist_bary_le_W1_add (β : BarycenterMap X) (μ : P1 X) (ν ν' : FinProb X) :
    dist (β.bary ν) (β.bary ν') ≤ P1.W1 μ ν.toP1 + P1.W1 μ ν'.toP1 := by
  calc dist (β.bary ν) (β.bary ν') ≤ FinProb.W1 ν ν' := β.dist_le_W1 _ _
    _ = P1.W1 ν.toP1 ν'.toP1 := (FinProb.W1_toP1 _ _).symm
    _ ≤ P1.W1 ν.toP1 μ + P1.W1 μ ν'.toP1 := P1.W1_triangle _ _ _
    _ = P1.W1 μ ν.toP1 + P1.W1 μ ν'.toP1 := by rw [P1.W1_comm ν.toP1]

variable [CompleteSpace X]

/-- The extension `β̄ μ = lim_k β ν_k`. -/
private noncomputable def extendFun (β : BarycenterMap X) (μ : P1 X) : X :=
  haveI := nonempty_of_P1 μ
  limUnder atTop fun k ↦ β.bary (approxSeq μ k)

private theorem tendsto_extendFun_approxSeq (β : BarycenterMap X) (μ : P1 X) :
    Tendsto (fun k ↦ β.bary (approxSeq μ k)) atTop (𝓝 (extendFun β μ)) := by
  have := nonempty_of_P1 μ
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
  refine cauchySeq_of_dist_le_add tendsto_one_div_add_atTop_nhds_zero_nat fun k l ↦ ?_
  exact (dist_bary_le_W1_add β μ _ _).trans
    (add_le_add (W1_approxSeq_le μ k) (W1_approxSeq_le μ l))

/-- If `W₁(μ, ν_k) → 0`, then `β ν_k → β̄ μ`. -/
private theorem tendsto_extendFun (β : BarycenterMap X) {μ : P1 X} {ν : ℕ → FinProb X}
    (hν : Tendsto (fun k ↦ P1.W1 μ (ν k).toP1) atTop (𝓝 0)) :
    Tendsto (fun k ↦ β.bary (ν k)) atTop (𝓝 (extendFun β μ)) := by
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  have h := (hν.add tendsto_one_div_add_atTop_nhds_zero_nat).add
    (tendsto_iff_dist_tendsto_zero.1 (tendsto_extendFun_approxSeq β μ))
  rw [add_zero, add_zero] at h
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ ?_) h
  calc dist (β.bary (ν k)) (extendFun β μ)
      ≤ dist (β.bary (ν k)) (β.bary (approxSeq μ k)) +
          dist (β.bary (approxSeq μ k)) (extendFun β μ) := dist_triangle _ _ _
    _ ≤ P1.W1 μ (ν k).toP1 + 1 / ((k : ℝ) + 1) +
          dist (β.bary (approxSeq μ k)) (extendFun β μ) := by
        gcongr
        exact (dist_bary_le_W1_add β μ _ _).trans (add_le_add le_rfl (W1_approxSeq_le μ k))

private theorem extendFun_toP1 (β : BarycenterMap X) (ν : FinProb X) :
    extendFun β ν.toP1 = β.bary ν := by
  have h : Tendsto (fun _ : ℕ ↦ P1.W1 ν.toP1 ν.toP1) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun _ ↦ (P1.W1_self _).symm
  exact tendsto_nhds_unique (tendsto_extendFun β (ν := fun _ ↦ ν) h) tendsto_const_nhds

private theorem dist_extendFun_le (β : BarycenterMap X) (μ ν : P1 X) :
    dist (extendFun β μ) (extendFun β ν) ≤ P1.W1 μ ν := by
  have h1 := (tendsto_extendFun_approxSeq β μ).dist (tendsto_extendFun_approxSeq β ν)
  have h2 := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).add_const (P1.W1 μ ν)).add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [zero_add, add_zero] at h2
  refine le_of_tendsto_of_tendsto' h1 h2 fun k ↦ ?_
  calc dist (β.bary (approxSeq μ k)) (β.bary (approxSeq ν k))
      ≤ FinProb.W1 (approxSeq μ k) (approxSeq ν k) := β.dist_le_W1 _ _
    _ = P1.W1 (approxSeq μ k).toP1 (approxSeq ν k).toP1 := (FinProb.W1_toP1 _ _).symm
    _ ≤ P1.W1 (approxSeq μ k).toP1 μ + (P1.W1 μ ν + P1.W1 ν (approxSeq ν k).toP1) :=
        (P1.W1_triangle _ μ _).trans (add_le_add le_rfl (P1.W1_triangle _ _ _))
    _ ≤ 1 / ((k : ℝ) + 1) + P1.W1 μ ν + 1 / ((k : ℝ) + 1) := by
        rw [P1.W1_comm (approxSeq μ k).toP1]
        linarith [W1_approxSeq_le μ k, W1_approxSeq_le ν k]

/-- The extension of a barycenter map on finitely supported measures to `P₁(X)` (by density,
`X` being complete). -/
noncomputable def extend (β : BarycenterMap X) : ContractingBarycenterMap X where
  toFun := extendFun β
  toFun_dirac x := by rw [← FinProb.toP1_dirac, extendFun_toP1, β.bary_dirac]
  dist_le_W1 := dist_extendFun_le β

/-- The extension agrees with `β` on finitely supported measures. -/
theorem extend_toP1 (β : BarycenterMap X) (μ : FinProb X) :
    β.extend.toFun μ.toP1 = β.bary μ :=
  extendFun_toP1 β μ

/-- If `β ν ∈ C` for all finitely supported `ν` with atoms in `S`, where `C` is closed, then the
extension maps every `μ ∈ P₁(X)` with `spt μ ⊆ S` into `C`. -/
theorem extend_mem (β : BarycenterMap X) {C S : Set X} (hC : IsClosed C)
    (h : ∀ ν : FinProb X, (ν.w.support : Set X) ⊆ S → β.bary ν ∈ C) {μ : P1 X}
    (hμ : μ.toMeasure.support ⊆ S) : β.extend.toFun μ ∈ C :=
  hC.mem_of_tendsto (tendsto_extendFun_approxSeq β μ)
    (Eventually.of_forall fun k ↦ h _ ((approxSeq_support μ k).trans hμ))

end BarycenterMap

/-- **Theorem 2.7** of [Basso2024bicombings]: a conical bicombing `σ` on a complete metric space
`X` yields a contracting barycenter map `β_σ : P₁(X) → X` with the convex hull property
`β_σ(μ) ∈ \overline{conv}_σ(spt μ)`. -/
theorem ConicalBicombing.exists_contractingBarycenterMap [CompleteSpace X]
    (σ : ConicalBicombing X) :
    ∃ β : ContractingBarycenterMap X,
      ∀ μ : P1 X, β.toFun μ ∈ closure (σ.convexHull μ.toMeasure.support) := by
  obtain ⟨β, hβ⟩ := σ.exists_barycenterMap
  exact ⟨β.extend, fun μ ↦ β.extend_mem isClosed_closure
    (fun ν hν ↦ σ.closure_convexHull_mono hν (hβ ν)) subset_rfl⟩

/-- **Theorem 2.6** of [Basso2024bicombings]: a complete metric space admits a conical bicombing
if and only if it is barycentric. -/
theorem nonempty_conicalBicombing_iff_nonempty_contractingBarycenterMap [CompleteSpace X] :
    Nonempty (ConicalBicombing X) ↔ Nonempty (ContractingBarycenterMap X) :=
  ⟨fun ⟨σ⟩ ↦ ⟨σ.exists_contractingBarycenterMap.choose⟩, fun ⟨β⟩ ↦ ⟨β.toConicalBicombing⟩⟩

/-- **Theorem 2.4** of [Basso2024] (Es-Sahib–Heinich, Navas, Descombes): a complete metric space
is of generalized non-positive curvature (Definition 1.3 there) if and only if it admits a
barycenter map `β : P₁(X) → X`, where `P₁(X)` carries the Kantorovich–Rubinstein distance `W₁` as
in that paper. -/
theorem isGNPC_iff_nonempty_contractingBarycenterMap [CompleteSpace X] :
    IsGNPC X ↔ Nonempty (ContractingBarycenterMap X) :=
  isGNPC_iff_nonempty_conicalBicombing.trans
    nonempty_conicalBicombing_iff_nonempty_contractingBarycenterMap

end LipschitzExtension
