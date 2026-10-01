/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Geometry.SimplicialComplex.Euclidean
import LipschitzExtension.Topology.MetricSpace.PointwiseLipschitz.Lower
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Pure simplicial complexes are quasiconvex

This file proves Lemma 5.2 of [Basso2024] (with item 3) of the errata [BassoClaude2026]), which is
used in the proof of Theorem 1.3.

A finite pure `n`-dimensional simplicial complex in `ℓ₂(V)` (`V` finite) is given by its set of
`n`-simplices (`Triangulation.PureComplex`; the vertex sets `Triangulation.PureComplex.facets`
of the `n`-simplices are `(n+1)`-subsets of `V`); it is the union
`Triangulation.PureComplex.carrier` of the corresponding faces, equipped with the `ℓ₂`-metric.
(Every simplicial complex in `ℓ₂(I)` with finitely many simplices lives in `ℓ₂(V)` for its finite
vertex set `V`; the simplices of a pure `n`-dimensional complex are the faces of its
`n`-simplices.)

**Lemma 5.2.** Let `Σ` be a pure `n`-dimensional simplicial complex, `n ≥ 2`, with at most `N`
`n`-simplices. If `Σ` is connected, then `Σ` with the `ℓ₂`-metric is `N^(10 log n)`-quasiconvex.

## Main definitions

* `Triangulation.PureComplex V n`: finite pure `n`-dimensional simplicial complexes in `ℓ₂(V)`,
  given by their `n`-simplices.
* `Triangulation.PureComplex.carrier`: the underlying set `Σ ⊆ ℓ₂(V)` of such a complex.

## Main statements

* `Triangulation.PureComplex.isQuasiconvex`: Lemma 5.2.
* `Triangulation.PureComplex.exists_polygonal`: the polygonal-path form of Lemma 5.2, which is the
  form used in the proof of Theorem 1.3.

## Proof outline

We follow the proof of the paper, with item 3 of the errata. If `Σ` is connected, the graph on the
`n`-simplices (adjacent if they meet) is connected (a union of the simplices of a component is
closed, and different components give disjoint closed sets). For `x ∈ Δ`, `y ∈ Δ'` choose a
shortest chain `Δ = Δ_0, …, Δ_m = Δ'`; then `m + 1 ≤ N` and non-consecutive simplices are
disjoint. By `Triangulation.exists_polygonal_of_chain` with `k = ⌈log₂ N⌉` there is a polygonal
path from `x` to `y` in `Σ` of length `≤ (4√n)^k |x - y|`, and `(4√n)^⌈log₂ N⌉ ≤ N^(10 log n)`
for `n ≥ 2`. A polygonal path whose segments lie in `Σ` gives a continuous curve in `Σ` of at most
the same length.

## Implementation notes

The shortest chain is obtained with `Nat.find` (a chain with a repeated simplex or with two
non-consecutive simplices sharing a vertex can be shortened). The curve is obtained from the
polygonal path with `exists_curve_of_polygonal`, by induction on the number of segments, gluing
the curve for the first segments (on `[0, 1/2]`) with the last segment (on `[1/2, 1]`).

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
-/

open Set Finset

namespace LipschitzExtension

namespace Triangulation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite pure `n`-dimensional simplicial complex in `ℓ₂(V)`, given by its `n`-simplices. -/
structure PureComplex (V : Type*) [Fintype V] (n : ℕ) where
  /-- The vertex sets of the `n`-simplices. -/
  facets : Finset (Finset V)
  /-- Every `n`-simplex has `n + 1` vertices. -/
  card_eq : ∀ σ ∈ facets, σ.card = n + 1

namespace PureComplex

variable {n : ℕ}

/-- The underlying set `Σ ⊆ ℓ₂(V)` of the complex. -/
def carrier (K : PureComplex V n) : Set (EuclideanSpace ℝ V) :=
  ⋃ σ ∈ K.facets, face σ

omit [DecidableEq V] in
private theorem face_subset_closedBall (σ : Finset V) : face σ ⊆ Metric.closedBall 0 1 := by
  rintro x ⟨hx0, hx1, -⟩
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq, Real.sqrt_le_one]
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, x i := Finset.sum_le_sum fun i _ ↦ by
        have h1 : x i ≤ 1 := hx1 ▸ Finset.single_le_sum (fun j _ ↦ hx0 j) (Finset.mem_univ i)
        rw [Real.norm_eq_abs, sq_abs]
        nlinarith [hx0 i]
    _ = 1 := hx1

omit [DecidableEq V] in
/-- The carrier of a finite complex is compact. -/
theorem isCompact_carrier (K : PureComplex V n) : IsCompact K.carrier := by
  classical
  exact K.facets.isCompact_biUnion fun σ _ ↦ Metric.isCompact_of_isClosed_isBounded
    (isClosed_face σ) (Metric.isBounded_closedBall.subset (face_subset_closedBall σ))

omit [DecidableEq V] in
private theorem mem_carrier {K : PureComplex V n} {σ : Finset V} (hσ : σ ∈ K.facets)
    {x : EuclideanSpace ℝ V} (hx : x ∈ face σ) : x ∈ K.carrier :=
  Set.mem_iUnion₂.2 ⟨σ, hσ, hx⟩

omit [DecidableEq V] in
private theorem face_nonempty {K : PureComplex V n} {σ : Finset V} (hσ : σ ∈ K.facets) :
    (face σ).Nonempty := by
  classical
  exact (face_nonempty_iff σ).2 (Finset.card_pos.1 (by rw [K.card_eq σ hσ]; omega))

/-- `c 0, …, c m` is a chain of `n`-simplices of `K` in which consecutive simplices meet. -/
private def IsChain (K : PureComplex V n) (c : ℕ → Finset V) (m : ℕ) : Prop :=
  (∀ j ≤ m, c j ∈ K.facets) ∧ ∀ j < m, (face (c j) ∩ face (c (j + 1))).Nonempty

omit [DecidableEq V] in
/-- If the carrier is connected, then any two `n`-simplices are joined by a chain. -/
private theorem exists_chain (K : PureComplex V n) (hK : IsPreconnected K.carrier)
    {σ τ : Finset V} (hσ : σ ∈ K.facets) (hτ : τ ∈ K.facets) :
    ∃ m c, c 0 = σ ∧ c m = τ ∧ K.IsChain c m := by
  classical
  -- `R ρ`: the simplex `ρ` can be reached from `σ`
  let R : Finset V → Prop := fun ρ ↦ ∃ m c, c 0 = σ ∧ c m = ρ ∧ K.IsChain c m
  have hRσ : R σ := ⟨0, fun _ ↦ σ, rfl, rfl, fun _ _ ↦ hσ, fun _ hj ↦ absurd hj (by omega)⟩
  have hext : ∀ ρ ρ', R ρ → ρ' ∈ K.facets → (face ρ ∩ face ρ').Nonempty → R ρ' := by
    rintro ρ ρ' ⟨m, c, hc0, hcm, hcF, hcR⟩ hρ' hmeet
    refine ⟨m + 1, fun j ↦ if j ≤ m then c j else ρ', by simp [hc0], by simp, fun j hj ↦ ?_,
      fun j hj ↦ ?_⟩
    · dsimp only
      split_ifs with h
      · exact hcF j h
      · exact hρ'
    · dsimp only
      rcases Nat.lt_or_ge j m with h | h
      · rw [ite_eq_left h.le, ite_eq_left (by omega : j + 1 ≤ m)]
        exact hcR j h
      · obtain rfl : j = m := by omega
        rw [ite_eq_left le_rfl, ite_eq_right (by omega), hcm]
        exact hmeet
  by_contra hτR
  let A := ⋃ ρ ∈ K.facets.filter R, face ρ
  let B := ⋃ ρ ∈ K.facets.filter (fun ρ ↦ ¬ R ρ), face ρ
  have hA : IsClosed A := isClosed_biUnion_finset fun ρ _ ↦ isClosed_face ρ
  have hB : IsClosed B := isClosed_biUnion_finset fun ρ _ ↦ isClosed_face ρ
  have hcov : K.carrier ⊆ A ∪ B := by
    intro x hx
    obtain ⟨ρ, hρ, hxρ⟩ := Set.mem_iUnion₂.1 hx
    by_cases h : R ρ
    · exact Or.inl (Set.mem_iUnion₂.2 ⟨ρ, Finset.mem_filter.2 ⟨hρ, h⟩, hxρ⟩)
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨ρ, Finset.mem_filter.2 ⟨hρ, h⟩, hxρ⟩)
  obtain ⟨x, hx⟩ := face_nonempty hσ
  obtain ⟨y, hy⟩ := face_nonempty hτ
  obtain ⟨z, -, hzA, hzB⟩ := isPreconnected_closed_iff.1 hK A B hA hB hcov
    ⟨x, mem_carrier hσ hx, Set.mem_iUnion₂.2 ⟨σ, Finset.mem_filter.2 ⟨hσ, hRσ⟩, hx⟩⟩
    ⟨y, mem_carrier hτ hy, Set.mem_iUnion₂.2 ⟨τ, Finset.mem_filter.2 ⟨hτ, hτR⟩, hy⟩⟩
  obtain ⟨ρ, hρ, hzρ⟩ := Set.mem_iUnion₂.1 hzA
  obtain ⟨ρ', hρ', hzρ'⟩ := Set.mem_iUnion₂.1 hzB
  rw [Finset.mem_filter] at hρ hρ'
  exact hρ'.2 (hext ρ ρ' hρ.2 hρ'.1 ⟨z, hzρ, hzρ'⟩)

omit [DecidableEq V] in
/-- Shortcutting a chain: if `c i` and `c (j + 1)` meet (`i ≤ j < m`), then dropping
`c (i + 1), …, c j` gives a chain of length `m - (j - i)`. -/
private theorem IsChain.shortcut {K : PureComplex V n} {c : ℕ → Finset V} {m i j : ℕ}
    (hc : K.IsChain c m) (hij : i ≤ j) (hjm : j < m)
    (hmeet : (face (c i) ∩ face (c (j + 1))).Nonempty) :
    K.IsChain (fun t ↦ if t ≤ i then c t else c (t + (j - i))) (m - (j - i)) := by
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · dsimp only
    split_ifs with h
    · exact hc.1 t (by omega)
    · exact hc.1 _ (by omega)
  · dsimp only
    rcases Nat.lt_or_ge t i with h1 | h1
    · rw [ite_eq_left h1.le, ite_eq_left (by omega : t + 1 ≤ i)]
      exact hc.2 t (by omega)
    · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
      · rw [ite_eq_left h2.ge, ite_eq_right (by omega), show t + 1 + (j - i) = j + 1 by omega,
          ← h2]
        exact hmeet
      · rw [ite_eq_right (by omega), ite_eq_right (by omega),
          show t + 1 + (j - i) = t + (j - i) + 1 by omega]
        exact hc.2 _ (by omega)

omit [DecidableEq V] in
/-- A shortest chain between two `n`-simplices: non-consecutive simplices are disjoint and the
chain has at most as many members as `K` has `n`-simplices. -/
private theorem exists_short_chain (K : PureComplex V n) (hK : IsPreconnected K.carrier)
    {σ τ : Finset V} (hσ : σ ∈ K.facets) (hτ : τ ∈ K.facets) :
    ∃ m c, c 0 = σ ∧ c m = τ ∧ K.IsChain c m ∧
      (∀ i j, i + 2 ≤ j → j ≤ m → Disjoint (c i) (c j)) ∧ m + 1 ≤ K.facets.card := by
  classical
  have hP : ∃ m c, c 0 = σ ∧ c m = τ ∧ K.IsChain c m := exists_chain K hK hσ hτ
  obtain ⟨c, hc0, hcm, hc⟩ := Nat.find_spec hP
  set m := Nat.find hP
  have hmin : ∀ m' < m, ¬ ∃ c, c 0 = σ ∧ c m' = τ ∧ K.IsChain c m' := fun m' h ↦ Nat.find_min hP h
  have hshort : ∀ i j, i ≤ j → j < m → (face (c i) ∩ face (c (j + 1))).Nonempty → j = i := by
    intro i j hij hjm hmeet
    by_contra hne
    refine hmin (m - (j - i)) (by omega) ⟨_, ?_, ?_, hc.shortcut hij hjm hmeet⟩
    · simp [hc0]
    · rw [ite_eq_right (by omega), Nat.sub_add_cancel (by omega), hcm]
  refine ⟨m, c, hc0, hcm, hc, fun i j hij hjm ↦ ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hvi hvj
    have := hshort i (j - 1) (by omega) (by omega)
      (by rw [show j - 1 + 1 = j by omega]; exact ⟨_, single_mem_face hvi, single_mem_face hvj⟩)
    omega
  · have hinj : ∀ i j, i < j → j ≤ m → c i ≠ c j := by
      intro i j hij hjm heq
      rcases Nat.lt_or_ge j m with hjm' | hjm'
      · have := hshort i j hij.le hjm' (by rw [heq]; exact hc.2 j hjm')
        omega
      · obtain rfl : j = m := le_antisymm hjm hjm'
        exact hmin i hij ⟨c, hc0, by rw [heq, hcm],
          fun t ht ↦ hc.1 t (by omega), fun t ht ↦ hc.2 t (by omega)⟩
    have := Finset.card_le_card_of_injOn c (s := Finset.range (m + 1)) (t := K.facets)
      (fun t ht ↦ hc.1 t (by simpa [Nat.lt_succ_iff] using ht)) (fun a ha b hb hab ↦ ?_)
    · simpa using this
    · simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hinj a b h (by omega) hab
      · exact hinj b a h (by omega) hab.symm

/-- The numerical estimate `(4 √n)^⌈log₂ N⌉ ≤ N^(10 log n)` for `n ≥ 2`. -/
private theorem pow_clog_le_rpow {N : ℕ} (hn : 2 ≤ n) (hN : 1 ≤ N) :
    (4 * √(n : ℝ)) ^ Nat.clog 2 N ≤ (N : ℝ) ^ (10 * Real.log n) := by
  rcases Nat.eq_or_lt_of_le hN with rfl | hN2
  · simp
  set k := Nat.clog 2 N
  have hk1 : 1 ≤ k := Nat.clog_pos one_lt_two hN2
  have hkN : 2 ^ (k - 1) < N := by
    have := Nat.pow_pred_clog_lt_self one_lt_two hN2
    rwa [Nat.pred_eq_sub_one] at this
  have hl2 : 1 / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    linarith
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn'
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN'
  have hkl : (k : ℝ) * Real.log 2 ≤ 2 * Real.log N := by
    have h1 : ((2 : ℝ) ^ (k - 1)) < N := by exact_mod_cast hkN
    have h2 : ((k - 1 : ℕ) : ℝ) * Real.log 2 < Real.log N := by
      rw [← Real.log_pow]; exact Real.log_lt_log (by positivity) h1
    rw [Nat.cast_sub hk1, Nat.cast_one] at h2
    linarith
  have hpos : 0 < 4 * √(n : ℝ) := by positivity
  rw [← Real.exp_log (pow_pos hpos k), Real.rpow_def_of_pos (by positivity)]
  apply Real.exp_le_exp.2
  rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  -- `k (2 log 2 + log n / 2) ≤ log N · 10 log n`, using `k log 2 ≤ 2 log N` and `log 2 ≥ 1/2`
  have h1 : (k : ℝ) * Real.log 2 * (2 * Real.log 2 + Real.log n / 2) ≤
      2 * Real.log N * (2 * Real.log 2 + Real.log n / 2) :=
    mul_le_mul_of_nonneg_right hkl (by positivity)
  have h2 : 4 * Real.log 2 + Real.log n ≤ 10 * Real.log 2 * Real.log n := by
    nlinarith [mul_nonneg (sub_nonneg.2 hln) (by linarith : (0 : ℝ) ≤ 10 * Real.log 2 - 1)]
  have h3 : 0 < Real.log 2 := by linarith
  have h4 : 0 ≤ Real.log N := by linarith
  refine le_of_mul_le_mul_right ?_ h3
  nlinarith [mul_le_mul_of_nonneg_left h2 h4]

omit [DecidableEq V] in
/-- Polygonal paths in a connected pure complex (the core of Lemma 5.2 of [Basso2024]): if `n ≥ 2`
and `K` has at most `N` `n`-simplices, then any two points of `Σ` are joined by a polygonal path
with consecutive points in a common `n`-simplex, of length at most `N^(10 log n)` times their
distance. -/
theorem exists_polygonal (K : PureComplex V n) (hn : 2 ≤ n) {N : ℕ} (hN : K.facets.card ≤ N)
    (hK : IsConnected K.carrier) {x y : EuclideanSpace ℝ V} (hx : x ∈ K.carrier)
    (hy : y ∈ K.carrier) :
    ∃ (l : ℕ) (p : ℕ → EuclideanSpace ℝ V), p 0 = x ∧ p l = y ∧
      (∀ i < l, ∃ σ ∈ K.facets, p i ∈ face σ ∧ p (i + 1) ∈ face σ) ∧
      ∑ i ∈ range l, dist (p i) (p (i + 1)) ≤ (N : ℝ) ^ (10 * Real.log n) * dist x y := by
  classical
  obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.1 hx
  obtain ⟨τ, hτ, hyτ⟩ := Set.mem_iUnion₂.1 hy
  obtain ⟨m, c, hc0, hcm, hc, hdisj, hmN⟩ := exists_short_chain K hK.isPreconnected hσ hτ
  have hN1 : 1 ≤ N := le_trans (Finset.card_pos.2 ⟨σ, hσ⟩) hN
  have hk : m + 1 ≤ 2 ^ Nat.clog 2 N := (hmN.trans hN).trans (Nat.le_pow_clog one_lt_two N)
  obtain ⟨l, p, hp0, hpl, hseg, hsum⟩ := exists_polygonal_of_chain (by omega : 1 ≤ n) c
    (fun j hj ↦ K.card_eq _ (hc.1 j hj)) hc.2 hdisj hk (hc0 ▸ hxσ) (hcm ▸ hyτ)
  refine ⟨l, p, hp0, hpl, fun i hi ↦ ?_, hsum.trans ?_⟩
  · obtain ⟨j, hj, h1, h2⟩ := hseg i hi
    exact ⟨c j, hc.1 j hj, h1, h2⟩
  · exact mul_le_mul_of_nonneg_right (pow_clog_le_rpow hn hN1) dist_nonneg

omit [DecidableEq V] in
/-- **Lemma 5.2** of [Basso2024] (with errata item 3): a connected pure `n`-dimensional simplicial
complex (`n ≥ 2`) with at most `N` `n`-simplices is `N^(10 log n)`-quasiconvex for the
`ℓ₂`-metric. -/
theorem isQuasiconvex (K : PureComplex V n) (hn : 2 ≤ n) {N : ℕ} (hN : K.facets.card ≤ N)
    (hK : IsConnected K.carrier) :
    IsQuasiconvex ((N : ℝ) ^ (10 * Real.log n)) K.carrier := by
  classical
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨l, p, hp0, hpl, hseg, hsum⟩ := K.exists_polygonal hn hN hK hx hy
  obtain ⟨γ, hγc, hγ0, hγ1, hγC, hγv⟩ := exists_curve_of_polygonal (C := K.carrier) l p
    (hp0 ▸ hx) fun i hi t ht ↦ by
      obtain ⟨σ, hσ, h1, h2⟩ := hseg i hi
      exact mem_carrier hσ ((convex_face σ).lineMap_mem h1 h2 ht)
  -- reparametrize `γ` on `ℝ` (constant outside `[0, 1]`) so that it takes values in `Σ`
  refine ⟨fun t ↦ ⟨γ (Set.projIcc (0 : ℝ) 1 zero_le_one t),
    hγC (Set.projIcc (0 : ℝ) 1 zero_le_one t).2⟩,
    ?_, ?_, ?_, ?_⟩
  · exact (Continuous.subtype_mk (hγc.comp (continuous_subtype_val.comp continuous_projIcc))
      _).continuousOn
  · ext
    simp [Set.projIcc_left, hγ0, hp0]
  · ext
    simp [Set.projIcc_right, hγ1, hpl]
  · have heq : eVariationOn (fun t ↦ (⟨γ (Set.projIcc (0 : ℝ) 1 zero_le_one t),
        hγC (Set.projIcc (0 : ℝ) 1 zero_le_one t).2⟩ : K.carrier)) (Icc 0 1) =
        eVariationOn γ (Icc 0 1) := by
      change eVariationOn (fun t ↦ γ (Set.projIcc (0 : ℝ) 1 zero_le_one t)) (Icc 0 1) = _
      exact eVariationOn.eq_of_eqOn fun t ht ↦ by rw [Set.projIcc_of_mem _ ht]
    rw [heq]
    refine hγv.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Subtype.dist_eq]
    exact hsum

end PureComplex

end Triangulation

end LipschitzExtension
