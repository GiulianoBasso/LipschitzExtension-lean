/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Barycenter.EsSahibHeinich
import LipschitzExtension.Topology.MetricSpace.Barycenter.Assignment
import LipschitzExtension.Combinatorics.Hypergeometric

/-!
# Descombes' consistent barycenters

This file proves Lemma 6.2 and Proposition 6.4 of Descombes' thesis, and the first part of the
proof of Theorem 6.5 there. Let `m` be a conical midpoint map on a complete metric space and
`ConicalMidpointMap.baryM` the barycenters of finite multisets of Theorem 6.1 (Es-Sahib–Heinich).

* **Lemma 6.2.** For a finite family `(x_j)_{j ∈ J}`, `1 ≤ k ≤ #J` and `z ∈ X`,
  `d(z, bar(x)) ≤ C(#J, k)⁻¹ ∑_{I ⊆ J, #I = k} d(z, bar(x|_I))`.
* **Kantorovich–Rubinstein.** `d(baryM M, baryM N) ≤ W₁(unif M, unif N)` for `#M = #N`.
* **Proposition 6.4.** The barycenter of `M` with every point repeated `k` times does not depend
  much on `k`: `d(baryM (k • M), baryM ((k + l) • M)) ≤ D / (2 √k)`, where `D` bounds the
  distances between points of `M`.
* Consequently `k ↦ baryM ((k + 1) • M)` is Cauchy; its limit `baryS M` satisfies
  `baryS (j • M) = baryS M` for `j ≥ 1` (this is what makes the barycenter of a measure well
  defined) and lies in every closed `m`-convex set containing the points of `M`. Moreover
  `d(baryS M, baryS N) ≤ W₁(unif M, unif N)` for all nonempty `M`, `N`.

## Main definitions

* `ConicalMidpointMap.baryS`: Descombes' consistent barycenter `lim_k baryM (k • M)`.

## Main statements

* `ConicalMidpointMap.dist_baryM_le_sum_powersetCard`: Lemma 6.2.
* `ConicalMidpointMap.dist_baryM_le_W1`: `d(baryM M, baryM N) ≤ W₁(unif M, unif N)` for
  `#M = #N`.
* `ConicalMidpointMap.dist_baryM_nsmul_le`: Proposition 6.4 (quantitative form).
* `ConicalMidpointMap.cauchySeq_baryM_nsmul`, `ConicalMidpointMap.tendsto_baryS`:
  `k ↦ baryM ((k + 1) • M)` is a Cauchy sequence (Proposition 6.4) converging to `baryS M`.
* `ConicalMidpointMap.baryS_nsmul`: consistency, `baryS (j • M) = baryS M` for `j ≥ 1`.
* `ConicalMidpointMap.dist_baryS_le_W1'`: `d(baryS M, baryS N) ≤ W₁(unif M, unif N)` for all
  nonempty multisets `M`, `N`.
* `ConicalMidpointMap.baryS_mem`: `baryS M` lies in every closed `m`-convex set containing the
  points of `M`.

## Proof outline

* Lemma 6.2 is proved by induction on `#J`, using `bar(x) = bar({bar(x|_{J - j}) : j ∈ J})`,
  Theorem 6.1 (iv) against the constant family `z`, and the fact that every `k`-subset of `J`
  avoids exactly `#J - k` elements of `J`.
* The Kantorovich–Rubinstein estimate follows from Theorem 6.1 (iv) and
  `FinProb.exists_pairing_le_W1`.
* For Proposition 6.4, apply Lemma 6.2 with `z = baryM (k • M)`, `J` the `(k + l) n` positions of
  `(k + l) • M` and subsets of size `k n`. For a subset `I` containing `i_j` copies of `x_j`,
  `d(z, bar(x|_I)) ≤ W₁ ≤ (D / 2kn) ∑_j |i_j - k|` (by Lemma 2.5 of [Basso2024],
  `FinProb.W1_ofWeights_le`), and the average of `∑_j |i_j - k|` is at most `n √k`
  (`sum_abs_card_filter_sub_le`).
* The estimate `d(baryS M, baryS N) ≤ W₁(unif M, unif N)` is proved first for `#M = #N`
  (`ConicalMidpointMap.dist_baryS_le_W1`) and then, comparing `#N • M` with `#M • N`, for all
  nonempty `M`, `N`.

## References

* D. Descombes, *Spaces with convex geodesic bicombings*, PhD thesis, ETH Zürich, 2015
* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open Set Metric Filter Topology

namespace LipschitzExtension

namespace ConicalMidpointMap

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X] (m : ConicalMidpointMap X)

/-- `baryM M = baryM T(M)` also holds for `#M = 2`. -/
private theorem baryM_eq_baryM_map_erase' [DecidableEq X] {M : Multiset X}
    (hM : 2 ≤ Multiset.card M) :
    m.baryM M = m.baryM (M.map fun a ↦ m.baryM (M.erase a)) := by
  rcases hM.lt_or_eq with h | h
  · exact m.baryM_eq_baryM_map_erase h
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 h.symm
    have h2 : (a ::ₘ {b} : Multiset X).erase b = {a} := by
      by_cases hab : a = b
      · subst hab
        exact Multiset.erase_cons_head a {a}
      · rw [Multiset.erase_cons_tail _ hab, Multiset.erase_singleton]
        rfl
    rw [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.erase_cons_head, h2, m.baryM_singleton, m.baryM_singleton,
      ← Multiset.insert_eq_cons, ← Multiset.insert_eq_cons, m.baryM_pair, m.baryM_pair,
      m.comm]

/-- The first step of Lemma 6.2: `d(z, bar(x)) ≤ (1/#J) ∑_{j ∈ J} d(z, bar(x|_{J - j}))`. -/
private theorem dist_baryM_le_sum_erase {ι : Type*} [DecidableEq ι] (J : Finset ι) (x : ι → X)
    (z : X) (hJ : 2 ≤ J.card) :
    dist z (m.baryM (J.val.map x)) ≤
      (∑ j ∈ J, dist z (m.baryM ((J.erase j).val.map x))) / J.card := by
  classical
  have hbar : m.baryM (J.val.map x) =
      m.baryM (J.val.map fun j ↦ m.baryM ((J.erase j).val.map x)) := by
    rw [m.baryM_eq_baryM_map_erase' (by rwa [Multiset.card_map, Finset.card_val]),
      Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun j hj ↦ ?_
    rw [Function.comp_apply, Finset.erase_val, Multiset.map_erase_of_mem _ _ hj]
  set P : Multiset (X × X) := J.val.map fun j ↦ (z, m.baryM ((J.erase j).val.map x)) with hP
  have hP0 : P ≠ 0 := by
    rw [hP, Ne, Multiset.map_eq_zero, Finset.val_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty,
      ← Finset.card_pos]
    omega
  have h := m.dist_baryM_le P hP0
  have h1 : P.map Prod.fst = Multiset.replicate J.card z := by
    rw [hP, Multiset.map_map]
    exact (Multiset.map_const' _ _).trans (by rw [Finset.card_val])
  have h2 : P.map Prod.snd = J.val.map fun j ↦ m.baryM ((J.erase j).val.map x) := by
    rw [hP, Multiset.map_map]
    rfl
  rw [h1, h2, m.baryM_replicate (by omega), ← hbar, hP, Multiset.card_map, Finset.card_val,
    Multiset.map_map] at h
  exact h

/-- Every `k`-subset `I ⊆ J` avoids exactly `#J - k` elements of `J`. -/
private theorem sum_sum_powersetCard_erase {ι : Type*} [DecidableEq ι] (J : Finset ι) (k : ℕ)
    (f : Finset ι → ℝ) :
    ∑ j ∈ J, ∑ I ∈ (J.erase j).powersetCard k, f I =
      ((J.card - k : ℕ) : ℝ) * ∑ I ∈ J.powersetCard k, f I := by
  rw [Finset.sum_comm' (t' := J.powersetCard k) (s' := fun I ↦ J \ I), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun I hI ↦ ?_
    rw [Finset.mem_powersetCard] at hI
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff_of_subset hI.1, hI.2]
  · intro j I
    simp only [Finset.mem_powersetCard, Finset.subset_erase, Finset.mem_sdiff]
    tauto

/-- Lemma 6.2 for sets of a given size `N`, by induction on `N`. -/
private theorem dist_baryM_le_sum_powersetCard_aux {ι : Type*} (x : ι → X) (z : X) {k : ℕ}
    (hk : 1 ≤ k) (N : ℕ) (hkN : k ≤ N) :
    ∀ J : Finset ι, J.card = N → dist z (m.baryM (J.val.map x)) ≤
      ((N.choose k : ℕ) : ℝ)⁻¹ * ∑ I ∈ J.powersetCard k, dist z (m.baryM (I.val.map x)) := by
  classical
  induction N, hkN using Nat.le_induction with
  | base =>
    intro J hJ
    rw [← hJ, Finset.powersetCard_self, Finset.sum_singleton, Nat.choose_self, Nat.cast_one,
      inv_one, one_mul]
  | succ N hkN ih =>
    intro J hJ
    refine (m.dist_baryM_le_sum_erase J x z (by omega)).trans ?_
    have hle : ∑ j ∈ J, dist z (m.baryM ((J.erase j).val.map x)) ≤
        ∑ j ∈ J, ((N.choose k : ℕ) : ℝ)⁻¹ *
          ∑ I ∈ (J.erase j).powersetCard k, dist z (m.baryM (I.val.map x)) :=
      Finset.sum_le_sum fun j hj ↦ ih (J.erase j) (by rw [Finset.card_erase_of_mem hj, hJ]; rfl)
    rw [← Finset.mul_sum, sum_sum_powersetCard_erase, hJ] at hle
    have hrel := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_mul_succ_eq N k)
    push_cast at hrel
    have hC : (0 : ℝ) < (N.choose k : ℕ) := by exact_mod_cast Nat.choose_pos hkN
    have hC' : (0 : ℝ) < ((N + 1).choose k : ℕ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    set S := ∑ I ∈ J.powersetCard k, dist z (m.baryM (I.val.map x))
    set c : ℝ := ((N + 1 - k : ℕ) : ℝ)
    rw [hJ, div_le_iff₀ (by positivity)]
    refine hle.trans (le_of_eq ?_)
    have key : c / (N.choose k : ℕ) = ((N : ℝ) + 1) / ((N + 1).choose k : ℕ) := by
      rw [div_eq_div_iff hC.ne' hC'.ne']
      linarith
    rw [Nat.cast_add_one]
    calc _ = c / (N.choose k : ℕ) * S := by ring
      _ = _ := by rw [key]; ring

/-- **Lemma 6.2** of Descombes' thesis, for families indexed by a finset `J`: if `1 ≤ k ≤ #J`,
then `d(z, bar(x)) ≤ C(#J, k)⁻¹ ∑_{I ⊆ J, #I = k} d(z, bar(x|_I))`. -/
theorem dist_baryM_le_sum_powersetCard {ι : Type*} (J : Finset ι) (x : ι → X)
    (z : X) {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J.card) :
    dist z (m.baryM (J.val.map x)) ≤
      ((J.card.choose k : ℕ) : ℝ)⁻¹ * ∑ I ∈ J.powersetCard k, dist z (m.baryM (I.val.map x)) :=
  m.dist_baryM_le_sum_powersetCard_aux x z hk J.card hkJ J rfl

/-- The barycenters of two multisets of the same size are at most `W₁` of the uniform measures
apart. -/
theorem dist_baryM_le_W1 {M N : Multiset X} (hM : M ≠ 0) (hN : N ≠ 0)
    (hcard : Multiset.card M = Multiset.card N) :
    dist (m.baryM M) (m.baryM N) ≤
      FinProb.W1 (FinProb.ofMultiset M hM) (FinProb.ofMultiset N hN) := by
  obtain ⟨P, h1, h2, hle⟩ := FinProb.exists_pairing_le_W1 hM hN hcard
  have hP : P ≠ 0 := by
    rintro rfl
    exact hM (by rw [← h1, Multiset.map_zero])
  have h := m.dist_baryM_le P hP
  rw [h1, h2, ← Multiset.card_map Prod.fst P, h1] at h
  exact h.trans hle

private theorem bind_const_eq_nsmul {α β : Type*} (s : Multiset α) (t : Multiset β) :
    s.bind (fun _ ↦ t) = Multiset.card s • t := by
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.zero_bind, Multiset.card_zero, zero_nsmul]
  | cons a s ih => rw [Multiset.cons_bind, ih, Multiset.card_cons, succ_nsmul, add_comm]

/-- `a • {x₁, …, xₙ}` is the family `x ∘ Prod.snd` indexed by `Fin a × Fin n`. -/
private theorem univ_val_map_comp_snd {α : Type*} (a n : ℕ) (x : Fin n → α) :
    (Finset.univ : Finset (Fin a × Fin n)).val.map (x ∘ Prod.snd) =
      a • (Finset.univ : Finset (Fin n)).val.map x := by
  change (Multiset.product (Finset.univ : Finset (Fin a)).val
    (Finset.univ : Finset (Fin n)).val).map (x ∘ Prod.snd) = _
  have h : ∀ i : Fin a, ((Finset.univ : Finset (Fin n)).val.map (Prod.mk i)).map (x ∘ Prod.snd) =
      (Finset.univ : Finset (Fin n)).val.map x := fun i ↦ by
    rw [Multiset.map_map]
    rfl
  rw [Multiset.product, Multiset.map_bind, Multiset.bind_congr fun i _ ↦ h i,
    bind_const_eq_nsmul, Finset.card_val, Finset.card_univ, Fintype.card_fin]

private theorem card_filter_snd_eq (a n : ℕ) (j : Fin n) :
    ((Finset.univ : Finset (Fin a × Fin n)).filter fun b ↦ b.2 = j).card = a := by
  have h : ((Finset.univ : Finset (Fin a × Fin n)).filter fun b ↦ b.2 = j) =
      (Finset.univ : Finset (Fin a)) ×ˢ {j} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
  rw [h, Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_singleton,
    mul_one]

private theorem sum_card_filter_div_eq_one {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : Finset ι) (p : ι → κ) (hI : I.Nonempty) :
    ∑ j ∈ (Finset.univ : Finset κ), ((I.filter fun i ↦ p i = j).card : ℝ) / I.card = 1 := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum,
    ← Finset.card_eq_sum_card_fiberwise fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _),
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hI.card_pos.ne')]

/-- **Proposition 6.4** of Descombes' thesis (quantitative form): if `D` bounds the distances
between the points of `M`, then `d(baryM (k • M), baryM ((k + l) • M)) ≤ D / (2 √k)`. -/
theorem dist_baryM_nsmul_le {M : Multiset X} (hM : M ≠ 0) {D : ℝ}
    (hD : ∀ a ∈ M, ∀ b ∈ M, dist a b ≤ D) {k : ℕ} (hk : 1 ≤ k) (l : ℕ) :
    dist (m.baryM (k • M)) (m.baryM ((k + l) • M)) ≤ D / (2 * Real.sqrt k) := by
  obtain ⟨n, hMn⟩ : ∃ n, Multiset.card M = n := ⟨_, rfl⟩
  obtain ⟨x, rfl⟩ := Multiset.exists_fin_enum M hMn
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (by rw [Finset.univ_eq_empty, Finset.empty_val, Multiset.map_zero]) hM
    · exact h
  have hxM : ∀ i, x i ∈ (Finset.univ : Finset (Fin n)).val.map x :=
    fun i ↦ Multiset.mem_map_of_mem x (Finset.mem_univ_val i)
  have hDx : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j ∈ (Finset.univ : Finset (Fin n)),
      dist (x i) (x j) ≤ D := fun i _ j _ ↦ hD _ (hxM i) _ (hxM j)
  have hD0 : 0 ≤ D := by
    have h := hD _ (hxM ⟨0, hn⟩) _ (hxM ⟨0, hn⟩)
    rwa [dist_self] at h
  rw [← univ_val_map_comp_snd, ← univ_val_map_comp_snd]
  set z := m.baryM ((Finset.univ : Finset (Fin k × Fin n)).val.map (x ∘ Prod.snd))
  have hcard : ∀ a : ℕ, (Finset.univ : Finset (Fin a × Fin n)).card = a * n := fun a ↦ by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hkn : 1 ≤ k * n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hknl : k * n ≤ (k + l) * n := Nat.mul_le_mul_right _ (Nat.le_add_right k l)
  have h62 := m.dist_baryM_le_sum_powersetCard (Finset.univ : Finset (Fin (k + l) × Fin n))
    (x ∘ Prod.snd) z hkn (by rw [hcard]; exact hknl)
  rw [hcard] at h62
  refine h62.trans ?_
  have hterm : ∀ I ∈ (Finset.univ : Finset (Fin (k + l) × Fin n)).powersetCard (k * n),
      dist z (m.baryM (I.val.map (x ∘ Prod.snd))) ≤
        D / (2 * ((k * n : ℕ) : ℝ)) *
          ∑ j : Fin n, |((I.filter fun b ↦ b.2 = j).card : ℝ) - k| := by
    intro I hI
    have hIc : I.card = k * n := (Finset.mem_powersetCard.1 hI).2
    have hI0 : I.Nonempty := Finset.card_pos.1 (by omega)
    have hU0 : (Finset.univ : Finset (Fin k × Fin n)).Nonempty :=
      Finset.card_pos.1 (by rw [hcard]; omega)
    have hne1 : (Finset.univ : Finset (Fin k × Fin n)).val.map (x ∘ Prod.snd) ≠ 0 := by
      rw [Ne, Multiset.map_eq_zero, Finset.val_eq_zero]
      exact hU0.ne_empty
    have hne2 : I.val.map (x ∘ Prod.snd) ≠ 0 := by
      rw [Ne, Multiset.map_eq_zero, Finset.val_eq_zero]
      exact hI0.ne_empty
    have hW := m.dist_baryM_le_W1 hne1 hne2 (by
      rw [Multiset.card_map, Multiset.card_map, Finset.card_val, Finset.card_val, hcard, hIc])
    rw [FinProb.ofMultiset_map_comp_eq_ofWeights (Finset.univ : Finset (Fin k × Fin n)) Prod.snd
        x hne1 (fun j _ ↦ by positivity) (sum_card_filter_div_eq_one _ _ hU0),
      FinProb.ofMultiset_map_comp_eq_ofWeights I Prod.snd x hne2 (fun j _ ↦ by positivity)
        (sum_card_filter_div_eq_one _ _ hI0)] at hW
    refine hW.trans ((FinProb.W1_ofWeights_le _ _ _ _ _ _ hDx).trans (le_of_eq ?_))
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [card_filter_snd_eq, hIc, hcard, ← sub_div, abs_div, abs_sub_comm,
      abs_of_pos (by positivity : (0 : ℝ) < ((k * n : ℕ) : ℝ))]
    ring
  have hC : (0 : ℝ) < (((k + l) * n).choose (k * n) : ℕ) := by
    exact_mod_cast Nat.choose_pos hknl
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
  calc _ ≤ ((((k + l) * n).choose (k * n) : ℕ) : ℝ)⁻¹ *
        ∑ I ∈ (Finset.univ : Finset (Fin (k + l) × Fin n)).powersetCard (k * n),
          D / (2 * ((k * n : ℕ) : ℝ)) *
            ∑ j : Fin n, |((I.filter fun b ↦ b.2 = j).card : ℝ) - k| := by
        gcongr with I hI
        exact hterm I hI
    _ = ((((k + l) * n).choose (k * n) : ℕ) : ℝ)⁻¹ * (D / (2 * ((k * n : ℕ) : ℝ))) *
        ∑ I ∈ (Finset.univ : Finset (Fin (k + l) × Fin n)).powersetCard (k * n),
          ∑ j : Fin n, |((I.filter fun b ↦ b.2 = j).card : ℝ) - k| := by
        rw [← Finset.mul_sum, mul_assoc]
    _ ≤ ((((k + l) * n).choose (k * n) : ℕ) : ℝ)⁻¹ * (D / (2 * ((k * n : ℕ) : ℝ))) *
        (((((k + l) * n).choose (k * n) : ℕ) : ℝ) * n * Real.sqrt k) := by
        gcongr
        exact sum_abs_card_filter_sub_le k l n hk
    _ = D * Real.sqrt k / (2 * k) := by
        rw [Nat.cast_mul]
        field_simp
    _ = D / (2 * Real.sqrt k) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]
        linear_combination (2 * D) * hsk

/-- `k ↦ baryM ((k + 1) • M)` is a Cauchy sequence (by Proposition 6.4). -/
theorem cauchySeq_baryM_nsmul (M : Multiset X) :
    CauchySeq fun k : ℕ ↦ m.baryM ((k + 1) • M) := by
  rcases eq_or_ne M 0 with rfl | hM
  · simp only [nsmul_zero]
    exact cauchySeq_const _
  obtain ⟨D, hD⟩ : ∃ D, ∀ a ∈ M, ∀ b ∈ M, dist a b ≤ D := by
    obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 M.finite_toSet.isBounded
    exact ⟨D, fun a ha b hb ↦ hD ha hb⟩
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((D / (2 * ε)) ^ 2)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_comm]
  have h := m.dist_baryM_nsmul_le hM hD (k := N + 1) (by omega) (n - N)
  rw [show N + 1 + (n - N) = n + 1 by omega] at h
  refine h.trans_lt ?_
  have hs : D / (2 * ε) < Real.sqrt ((N + 1 : ℕ) : ℝ) :=
    Real.lt_sqrt_of_sq_lt (by push_cast; linarith)
  rw [div_lt_iff₀ (by positivity)] at hs ⊢
  linarith

/-- Descombes' consistent barycenter `bar*(M) = lim_k baryM (k • M)`. -/
noncomputable def baryS (M : Multiset X) : X :=
  limUnder atTop fun k : ℕ ↦ m.baryM ((k + 1) • M)

/-- `baryM ((k + 1) • M) → baryS M` as `k → ∞`. -/
theorem tendsto_baryS (M : Multiset X) :
    Tendsto (fun k : ℕ ↦ m.baryM ((k + 1) • M)) atTop (𝓝 (m.baryS M)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (m.cauchySeq_baryM_nsmul M))

/-- Consistency: repeating every point of `M` the same number `j ≥ 1` of times does not change
the barycenter. -/
theorem baryS_nsmul (M : Multiset X) {j : ℕ} (hj : j ≠ 0) : m.baryS (j • M) = m.baryS M := by
  have hle : ∀ k : ℕ, k + 1 ≤ (k + 1) * j := fun k ↦
    Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hj)
  have hφ : Tendsto (fun k : ℕ ↦ (k + 1) * j - 1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ by change k ≤ _; have := hle k; omega) tendsto_id
  refine tendsto_nhds_unique (m.tendsto_baryS (j • M)) ?_
  refine ((m.tendsto_baryS M).comp hφ).congr fun k ↦ ?_
  rw [Function.comp_apply, Nat.sub_add_cancel (by have := hle k; omega), mul_nsmul']

private theorem nsmul_ne_zero_of_ne_zero {α : Type*} {M : Multiset α} (hM : M ≠ 0) {k : ℕ}
    (hk : k ≠ 0) : k • M ≠ 0 :=
  Multiset.card_pos.1 (by
    rw [Multiset.card_nsmul]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hk) (Multiset.card_pos.2 hM))

/-- `d(baryS M, baryS N) ≤ W₁(unif M, unif N)` for nonempty multisets of the same size (see
`ConicalMidpointMap.dist_baryS_le_W1'` for multisets of different sizes). -/
theorem dist_baryS_le_W1 {M N : Multiset X} (hM : M ≠ 0) (hN : N ≠ 0)
    (hcard : Multiset.card M = Multiset.card N) :
    dist (m.baryS M) (m.baryS N) ≤
      FinProb.W1 (FinProb.ofMultiset M hM) (FinProb.ofMultiset N hN) := by
  refine le_of_tendsto' ((m.tendsto_baryS M).dist (m.tendsto_baryS N)) fun k ↦ ?_
  have h := m.dist_baryM_le_W1 (nsmul_ne_zero_of_ne_zero hM k.succ_ne_zero)
    (nsmul_ne_zero_of_ne_zero hN k.succ_ne_zero)
    (by rw [Multiset.card_nsmul, Multiset.card_nsmul, hcard])
  rwa [FinProb.ofMultiset_nsmul M hM, FinProb.ofMultiset_nsmul N hN] at h

/-- `d(baryS M, baryS N) ≤ W₁(unif M, unif N)` for all nonempty multisets `M`, `N` of possibly
different sizes: `#N • M` and `#M • N` have the same size, and by
`ConicalMidpointMap.baryS_nsmul` and `FinProb.ofMultiset_nsmul` the same consistent barycenters
and uniform measures as `M` and `N`. -/
theorem dist_baryS_le_W1' {M N : Multiset X} (hM : M ≠ 0) (hN : N ≠ 0) :
    dist (m.baryS M) (m.baryS N) ≤
      FinProb.W1 (FinProb.ofMultiset M hM) (FinProb.ofMultiset N hN) := by
  have hcM : Multiset.card M ≠ 0 := (Multiset.card_pos.2 hM).ne'
  have hcN : Multiset.card N ≠ 0 := (Multiset.card_pos.2 hN).ne'
  have h1 := nsmul_ne_zero_of_ne_zero hM hcN
  have h2 := nsmul_ne_zero_of_ne_zero hN hcM
  have h := m.dist_baryS_le_W1 h1 h2 (by rw [Multiset.card_nsmul, Multiset.card_nsmul, mul_comm])
  rwa [m.baryS_nsmul M hcN, m.baryS_nsmul N hcM, FinProb.ofMultiset_nsmul M hM h1,
    FinProb.ofMultiset_nsmul N hN h2] at h

/-- `baryS M` lies in every closed `m`-convex set containing the points of `M` (Theorem 6.1 (i)
passes to the limit). -/
theorem baryS_mem {C : Set X} (hCc : IsClosed C) (hC : m.IsConvex C) {M : Multiset X}
    (hM : M ≠ 0) (hMC : ∀ a ∈ M, a ∈ C) : m.baryS M ∈ C :=
  hCc.mem_of_tendsto (m.tendsto_baryS M) (Eventually.of_forall fun k ↦
    m.baryM_mem hCc hC (nsmul_ne_zero_of_ne_zero hM k.succ_ne_zero) fun a ha ↦
      hMC a (Multiset.mem_of_mem_nsmul ha))

/-- The consistent barycenter of `n ≥ 1` copies of `a` is `a`. -/
theorem baryS_replicate {n : ℕ} (hn : n ≠ 0) (a : X) :
    m.baryS (Multiset.replicate n a) = a := by
  refine tendsto_nhds_unique (m.tendsto_baryS _) (tendsto_const_nhds.congr fun k ↦ ?_)
  rw [Multiset.nsmul_replicate, m.baryM_replicate (Nat.mul_ne_zero k.succ_ne_zero hn)]

end ConicalMidpointMap

end LipschitzExtension
