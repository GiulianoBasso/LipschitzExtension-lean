/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.MeasureTheory.Wasserstein.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finitely supported measures are dense in `P₁(X)`

This file proves that for `μ ∈ P₁(X)` and `ε > 0` there is a finitely supported probability
measure `ν` with atoms in the support of `μ` and `W₁(μ, ν) ≤ ε`. This is the density statement
used at the end of the proof of Theorem 2.7 of [Basso2024bicombings] (there quoted from G. Basso,
*Fixed point theorems for metric spaces with a conical geodesic bicombing*, Proposition 3.2), with
the additional information on the atoms needed for the convex hull property.

## Main statements

* `P1.exists_finProb_W1_le`: finitely supported probability measures with atoms in `spt μ` are
  `W₁`-dense in `P₁(X)`.

## Proof outline

Fix `x₀ ∈ spt μ`. Since `x ↦ d(x, x₀)` is integrable, there is `η > 0` with
`∫_A d(x, x₀) dμ < ε/2` whenever `μ(A) < η`. By inner regularity there is a compact
`K ⊆ spt μ` with `μ(X \ K) < η` (the support has full measure). Cover `K` by finitely many
balls `B(cᵢ, ε/2)`, `cᵢ ∈ K`, disjointify them to Borel sets `Aᵢ ⊆ B(cᵢ, ε/2) ∩ K`, and put
`ν = ∑ᵢ μ(Aᵢ) δ_{cᵢ} + μ(X \ K) δ_{x₀}`. For `1`-Lipschitz `g`,
`∫ g dμ - ∫ g dν ≤ ∑ᵢ ∫_{Aᵢ} d(x, cᵢ) dμ + ∫_{X \ K} d(x, x₀) dμ ≤ ε/2 + ε/2`.

In the formalization, an auxiliary lemma gives the general estimate for a finite measurable
partition `(Aᵢ)` of `X` with points `yᵢ`: `ν = ∑ᵢ μ(Aᵢ) δ_{yᵢ}` satisfies
`W₁(μ, ν) ≤ ∑ᵢ ∫_{Aᵢ} d(x, yᵢ) dμ`. The partition `X \ K, A₁, …, A_N` is obtained by applying
`disjointed` to the family `X \ K, B(c₁, ε/2), …, B(c_N, ε/2)` indexed by `Fin (N + 1)`.

## References

* [G. Basso, *Extending and improving conical bicombings*][Basso2024bicombings]
* G. Basso, *Fixed point theorems for metric spaces with a conical geodesic bicombing*
-/

open MeasureTheory Set Metric
open scoped Function

namespace LipschitzExtension

namespace P1

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The weights of a finite measurable partition sum to `1`. -/
private theorem sum_measureReal_partition_eq_one (μ : P1 X) {ι : Type*} [Fintype ι] {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A))
    (hcov : ⋃ i, A i = univ) : ∑ i, μ.toMeasure.real (A i) = 1 := by
  rw [← measureReal_iUnion_fintype hdisj hA, hcov, probReal_univ]

/-- Replacing `μ` on each piece `A i` of a finite measurable partition by an atom at `y i`
costs at most `∑ᵢ ∫_{A i} d(x, y i) dμ`. -/
private theorem integral_sub_sum_partition_le (μ : P1 X) {ι : Type*} [Fintype ι] {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A))
    (hcov : ⋃ i, A i = univ) (y : ι → X) {g : X → ℝ} (hg : LipschitzWith 1 g) :
    ∫ x, g x ∂μ.toMeasure - ∑ i, g (y i) * μ.toMeasure.real (A i) ≤
      ∑ i, ∫ x in A i, dist x (y i) ∂μ.toMeasure := by
  have hgi := μ.integrable_of_lipschitzWith hg
  rw [← setIntegral_univ, ← hcov, integral_iUnion_fintype hA hdisj fun i ↦ hgi.integrableOn,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have h1 : ∫ x in A i, g x ∂μ.toMeasure ≤ ∫ x in A i, (g (y i) + dist x (y i)) ∂μ.toMeasure :=
    setIntegral_mono hgi.integrableOn
      ((integrable_const _).add (μ.integrable_dist (y i))).integrableOn
      fun x ↦ by linarith [FinProb.sub_le_dist_of_lipschitz hg x (y i)]
  rw [integral_add (integrable_const _) (μ.integrable_dist (y i)).integrableOn,
    setIntegral_const, smul_eq_mul] at h1
  linarith

/-- The finitely supported measure `∑ᵢ μ(A i) δ_{y i}` of a finite measurable partition `A`
approximates `μ` in `W₁` up to `∑ᵢ ∫_{A i} d(x, y i) dμ`. -/
private theorem exists_finProb_of_partition (μ : P1 X) {ι : Type*} [Fintype ι] {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Disjoint on A))
    (hcov : ⋃ i, A i = univ) (y : ι → X) :
    ∃ ν : FinProb X, (ν.w.support : Set X) ⊆ range y ∧
      W1 μ ν.toP1 ≤ ∑ i, ∫ x in A i, dist x (y i) ∂μ.toMeasure := by
  refine ⟨FinProb.ofWeights Finset.univ y (fun i ↦ μ.toMeasure.real (A i))
    (fun _ _ ↦ measureReal_nonneg) (sum_measureReal_partition_eq_one μ hA hdisj hcov), ?_, ?_⟩
  · intro z hz
    by_contra hzy
    apply Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hz)
    change (∑ i, μ.toMeasure.real (A i) • Finsupp.single (y i) (1 : ℝ)) z = 0
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne fun h ↦ hzy ⟨i, h.symm⟩, smul_zero]
  · refine W1_le fun g hg ↦ ?_
    rw [FinProb.integral_toP1]
    change _ - FinProb.integ g _ ≤ _
    rw [FinProb.integ_ofWeights]
    exact integral_sub_sum_partition_le μ hA hdisj hcov y hg

/-- The construction, given a measurable set `K` of almost full measure covered by finitely many
balls `B(c i, ε / 2)`: the pieces are `Kᶜ` (with atom `x₀`) and the disjointified balls. -/
private theorem exists_finProb_of_cover (μ : P1 X) {ε : ℝ} (hε : 0 < ε) (x₀ : X) {K : Set X}
    (hK : MeasurableSet K) {η : ENNReal} (hKc : μ.toMeasure Kᶜ < η)
    (htail : ∀ s, μ.toMeasure s < η → ∫ x in s, dist x x₀ ∂μ.toMeasure < ε / 2)
    {N : ℕ} (c : Fin N → X) (hcov : K ⊆ ⋃ i, ball (c i) (ε / 2)) :
    ∃ ν : FinProb X, (ν.w.support : Set X) ⊆ insert x₀ (range c) ∧ W1 μ ν.toP1 ≤ ε := by
  set B : Fin (N + 1) → Set X := Fin.cons Kᶜ fun i ↦ ball (c i) (ε / 2)
  have hB : ∀ i, MeasurableSet (B i) := by
    refine Fin.cases ?_ fun i ↦ ?_
    · simp only [B, Fin.cons_zero]
      exact hK.compl
    · simp only [B, Fin.cons_succ]
      exact measurableSet_ball
  have hA : ∀ i, MeasurableSet (disjointed B i) := fun i ↦
    disjointedRec (p := MeasurableSet) (fun _ j ht ↦ ht.diff (hB j)) (hB i)
  have hcovB : ⋃ i, disjointed B i = univ := by
    rw [iUnion_disjointed, eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hx)
      refine mem_iUnion.2 ⟨i.succ, ?_⟩
      simp only [B, Fin.cons_succ]
      exact hi
    · refine mem_iUnion.2 ⟨0, ?_⟩
      simp only [B, Fin.cons_zero]
      exact hx
  obtain ⟨ν, hνs, hν⟩ := exists_finProb_of_partition μ hA (disjoint_disjointed B) hcovB
    (Fin.cons x₀ c : Fin (N + 1) → X)
  refine ⟨ν, hνs.trans ?_, hν.trans ?_⟩
  · rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [Fin.cons_zero]
      exact mem_insert _ _
    · rw [Fin.cons_succ]
      exact mem_insert_of_mem _ (mem_range_self j)
  · have hsum := sum_measureReal_partition_eq_one μ hA (disjoint_disjointed B) hcovB
    rw [Fin.sum_univ_succ] at hsum ⊢
    have h0 : ∫ x in disjointed B 0, dist x x₀ ∂μ.toMeasure < ε / 2 := by
      refine htail _ ((measure_mono ?_).trans_lt hKc)
      refine (disjointed_subset B 0).trans ?_
      simp only [B, Fin.cons_zero]
      exact subset_rfl
    have h1 : ∀ j : Fin N, ∫ x in disjointed B j.succ, dist x (c j) ∂μ.toMeasure ≤
        ε / 2 * μ.toMeasure.real (disjointed B j.succ) := by
      intro j
      refine (Real.le_norm_self _).trans
        (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun x hx ↦ ?_)
      have := disjointed_subset B j.succ hx
      simp only [B, Fin.cons_succ, mem_ball] at this
      rw [Real.norm_of_nonneg dist_nonneg]
      exact this.le
    simp only [Fin.cons_zero, Fin.cons_succ]
    have h2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ h1 j
    rw [← Finset.mul_sum] at h2
    have h3 : 0 ≤ μ.toMeasure.real (disjointed B 0) := measureReal_nonneg
    have h4 : ε / 2 * ∑ j : Fin N, μ.toMeasure.real (disjointed B j.succ) ≤ ε / 2 :=
      mul_le_of_le_one_right (half_pos hε).le (by linarith)
    linarith

/-- Finitely supported measures with atoms in `spt μ` are `W₁`-dense in `P₁(X)` (the density
statement used in the proof of Theorem 2.7 of [Basso2024bicombings]). -/
theorem exists_finProb_W1_le (μ : P1 X) {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : FinProb X, (ν.w.support : Set X) ⊆ μ.toMeasure.support ∧ W1 μ ν.toP1 ≤ ε := by
  obtain ⟨x₀, hx₀⟩ := μ.support_nonempty
  -- absolute continuity of `s ↦ ∫_s d(x, x₀) dμ`
  have htend := (μ.integrable_dist x₀).tendsto_setIntegral_nhds_zero
    (l := Filter.comap μ.toMeasure (nhds 0)) (s := id) Filter.tendsto_comap
  obtain ⟨η, hη, htail⟩ := (ENNReal.nhds_zero_basis.comap _).eventually_iff.1
    ((tendsto_order.1 htend).2 (ε / 2) (half_pos hε))
  -- a compact set of almost full measure inside the support
  obtain ⟨K, hKs, hK, hμK⟩ :=
    (Measure.isClosed_support (μ := μ.toMeasure)).measurableSet.exists_isCompact_sdiff_lt
      (measure_ne_top μ.toMeasure _) hη.ne'
  have hKc : μ.toMeasure Kᶜ < η := by
    calc μ.toMeasure Kᶜ ≤ μ.toMeasure (μ.toMeasure.support \ K ∪ μ.toMeasure.supportᶜ) :=
          measure_mono fun x hx ↦ by
            by_cases h : x ∈ μ.toMeasure.support
            · exact Or.inl ⟨h, hx⟩
            · exact Or.inr h
      _ ≤ μ.toMeasure (μ.toMeasure.support \ K) + μ.toMeasure μ.toMeasure.supportᶜ :=
          measure_union_le _ _
      _ < η := by rwa [μ.measure_compl_support, add_zero]
  -- finitely many balls cover `K`
  obtain ⟨t, htK, htcov⟩ := hK.elim_nhds_subcover (fun x ↦ ball x (ε / 2))
    fun x _ ↦ ball_mem_nhds x (half_pos hε)
  have hcov : K ⊆ ⋃ i, ball (t.equivFin.symm i : X) (ε / 2) := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (htcov hx)
    refine mem_iUnion.2 ⟨t.equivFin ⟨z, hz⟩, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hxz
  obtain ⟨ν, hνs, hν⟩ := exists_finProb_of_cover μ hε x₀ hK.isClosed.measurableSet hKc
    (fun s hs ↦ htail hs) _ hcov
  refine ⟨ν, hνs.trans ?_, hν⟩
  rintro _ (rfl | ⟨i, rfl⟩)
  · exact hx₀
  · exact hKs (htK _ (t.equivFin.symm i).2)

end P1

end LipschitzExtension
