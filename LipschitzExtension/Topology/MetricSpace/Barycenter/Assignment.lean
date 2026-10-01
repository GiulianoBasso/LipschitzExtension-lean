/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Barycenter.Uniform
import Mathlib.Combinatorics.Hall.Basic

/-!
# Optimal assignments and duality for uniform measures

This file proves **Egerváry's theorem** (duality for the assignment problem): for every real
`n × n` matrix `C` there are a permutation `e` and potentials `u, v` with `u i + v j ≤ C i j` for
all `i, j` and `∑ᵢ C i (e i) = ∑ᵢ u i + ∑ⱼ v j`. In particular `e` is an optimal assignment.

As a consequence we obtain the non-trivial inequality in Proposition 2.2 of
[Basso2024bicombings], i.e. Kantorovich–Rubinstein duality for uniform measures: for multisets
`M, N` of the same cardinality there is a pairing `P` of their points whose average cost is at
most `W₁(unif M, unif N)`.

## Main statements

* `exists_perm_potentials`: Egerváry's theorem.
* `Multiset.exists_fin_enum`: a multiset of cardinality `n` can be enumerated by `Fin n`.
* `FinProb.exists_pairing_le_W1`: two nonempty multisets of the same cardinality admit a pairing
  whose average cost is at most the `W₁`-distance of their uniform measures (the non-trivial
  inequality in Proposition 2.2 of [Basso2024bicombings]).

## Proof outline

Let `Φ(u) = ∑ᵢ uᵢ + ∑ⱼ minᵢ (C i j - uᵢ)`, so that `(u, v)` with `vⱼ = minᵢ (C i j - uᵢ)` is
feasible and `Φ` is its value. `Φ` is continuous, invariant under adding a constant to all `uᵢ`,
and tends to `-∞` when `max u - min u → ∞`; hence it attains its maximum at some `u`. Consider the
bipartite graph of tight pairs `u i + v j = C i j`. If it has a perfect matching `e` (Hall's
theorem, `Finset.all_card_le_biUnion_card_iff_exists_injective`), then
`∑ C i (e i) = ∑ u + ∑ v`. Otherwise there is a set `I` of rows whose set `N(I)` of tight
neighbours satisfies `#N(I) < #I`; increasing `uᵢ` (`i ∈ I`) by a small `ε > 0` and decreasing
`vⱼ` (`j ∈ N(I)`) by `ε` keeps the potentials feasible and increases the value by
`ε (#I - #N(I)) > 0`, a contradiction.

For the consequence, enumerate `M = {x₁, …, xₙ}` and `N = {y₁, …, yₙ}`, and take
`C i j = d(xᵢ, yⱼ)` and the potentials above. Then `f(z) = minⱼ (d(z, yⱼ) - vⱼ)` is
`1`-Lipschitz, `f(xᵢ) ≥ uᵢ` and `f(yⱼ) ≤ -vⱼ`, so the cost `∑ᵢ d(xᵢ, y_{e i}) = ∑ u + ∑ v` of the
assignment `e` is at most `∑ᵢ f(xᵢ) - ∑ⱼ f(yⱼ) ≤ n W₁(unif M, unif N)`.

## References

* [G. Basso, *Extending and improving conical bicombings*][Basso2024bicombings]
-/

open Set

namespace LipschitzExtension

namespace Egervary

variable {n : ℕ} (hne : (Finset.univ : Finset (Fin n)).Nonempty) (C : Fin n → Fin n → ℝ)

/-- The best dual potential `v u j = minᵢ (C i j - u i)` for given potentials `u`. -/
private noncomputable def vpot (u : Fin n → ℝ) (j : Fin n) : ℝ :=
  Finset.univ.inf' hne fun i ↦ C i j - u i

/-- The dual objective `Φ u = ∑ᵢ u i + ∑ⱼ v u j`. -/
private noncomputable def obj (u : Fin n → ℝ) : ℝ :=
  ∑ i, u i + ∑ j, vpot hne C u j

private theorem vpot_le (u : Fin n → ℝ) (i j : Fin n) : vpot hne C u j ≤ C i j - u i :=
  Finset.inf'_le (fun i ↦ C i j - u i) (Finset.mem_univ i)

private theorem le_vpot (u : Fin n → ℝ) (j : Fin n) {a : ℝ} (h : ∀ i, a ≤ C i j - u i) :
    a ≤ vpot hne C u j :=
  Finset.le_inf' hne _ fun i _ ↦ h i

private theorem add_vpot_le (u : Fin n → ℝ) (i j : Fin n) : u i + vpot hne C u j ≤ C i j := by
  have := vpot_le hne C u i j
  linarith

private theorem continuous_obj : Continuous (obj hne C) := by
  unfold obj vpot
  refine (continuous_finsetSum _ fun i _ ↦ continuous_apply i).add
    (continuous_finsetSum _ fun j _ ↦ ?_)
  exact Continuous.finset_inf'_apply hne fun i _ ↦ continuous_const.sub (continuous_apply i)

private theorem vpot_sub_const (u : Fin n → ℝ) (c : ℝ) (j : Fin n) :
    vpot hne C (fun i ↦ u i - c) j = vpot hne C u j + c := by
  apply le_antisymm
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' hne (fun i ↦ C i j - u i)
    calc vpot hne C (fun i ↦ u i - c) j ≤ C i j - (u i - c) := vpot_le hne C _ i j
      _ = vpot hne C u j + c := by unfold vpot; rw [hi]; ring
  · refine le_vpot hne C _ j fun i ↦ ?_
    have := vpot_le hne C u i j
    linarith

/-- `Φ` is invariant under subtracting a constant from all `u i`. -/
private theorem obj_sub_const (u : Fin n → ℝ) (c : ℝ) :
    obj hne C (fun i ↦ u i - c) = obj hne C u := by
  unfold obj
  simp only [vpot_sub_const, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- `Φ u ≤ ∑ⱼ C a j - (max u - u b)` if `u a = max u`. -/
private theorem obj_add_le (u : Fin n → ℝ) {a : Fin n} (ha : ∀ i, u i ≤ u a) (b : Fin n) :
    obj hne C u + (u a - u b) ≤ ∑ j, C a j := by
  have h1 : ∑ j, vpot hne C u j ≤ ∑ j, (C a j - u a) :=
    Finset.sum_le_sum fun j _ ↦ vpot_le hne C u a j
  have h2 : u a - u b ≤ ∑ i, (u a - u i) :=
    Finset.single_le_sum (f := fun i ↦ u a - u i) (fun i _ ↦ sub_nonneg.mpr (ha i))
      (Finset.mem_univ b)
  rw [Finset.sum_sub_distrib] at h1 h2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
  unfold obj
  linarith

/-- `Φ` attains a global maximum: maximize over the compact cube `[0, R]ⁿ` and use the
invariance under constant shifts together with `obj_add_le` for the other `u`. -/
private theorem exists_max : ∃ u, ∀ u', obj hne C u' ≤ obj hne C u := by
  obtain ⟨B, hB⟩ := (Set.finite_range fun p : Fin n × Fin n ↦ |C p.1 p.2|).bddAbove
  have hCB : ∀ i j, |C i j| ≤ B := fun i j ↦ hB ⟨(i, j), rfl⟩
  obtain ⟨i₀, -⟩ := id hne
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hCB i₀ i₀)
  set R : ℝ := 2 * n * B
  have hR0 : 0 ≤ R := by positivity
  let K : Set (Fin n → ℝ) := Set.pi univ fun _ ↦ Icc 0 R
  have hK : IsCompact K := isCompact_univ_pi fun _ ↦ isCompact_Icc
  have h0K : (0 : Fin n → ℝ) ∈ K := Set.mem_univ_pi.mpr fun _ ↦ ⟨le_rfl, hR0⟩
  obtain ⟨u, -, hmax⟩ := hK.exists_isMaxOn ⟨0, h0K⟩ (continuous_obj hne C).continuousOn
  rw [isMaxOn_iff] at hmax
  refine ⟨u, fun w ↦ ?_⟩
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ w hne
  obtain ⟨b, -, hb⟩ := Finset.exists_min_image Finset.univ w hne
  by_cases hab : w a - w b ≤ R
  · rw [← obj_sub_const hne C w (w b)]
    refine hmax _ (Set.mem_univ_pi.mpr fun i ↦ ⟨?_, ?_⟩)
    · exact sub_nonneg.mpr (hb i (Finset.mem_univ i))
    · linarith [ha i (Finset.mem_univ i)]
  · have h1 := obj_add_le hne C w (fun i ↦ ha i (Finset.mem_univ i)) b
    have h2 : ∑ j, C a j ≤ n * B := by
      calc ∑ j, C a j ≤ ∑ _j : Fin n, B :=
            Finset.sum_le_sum fun j _ ↦ (le_abs_self _).trans (hCB a j)
        _ = n * B := by simp
    have h3 : -(n * B) ≤ obj hne C 0 := by
      calc -(n * B) = ∑ _j : Fin n, -B := by simp
        _ ≤ ∑ j, vpot hne C 0 j := Finset.sum_le_sum fun j _ ↦
            le_vpot hne C 0 j fun i ↦ by
              have := neg_abs_le (C i j)
              have := hCB i j
              simp only [Pi.zero_apply, sub_zero]
              linarith
        _ = obj hne C 0 := by simp [obj]
    have h4 := hmax 0 h0K
    linarith

/-- At a global maximum `u` of `Φ` the tight pairs `u i + v j = C i j` contain a perfect matching
(otherwise Hall's condition fails for some rows `S`, and raising `u` on `S` increases `Φ`). -/
private theorem exists_perm_of_max (u : Fin n → ℝ) (hu : ∀ u', obj hne C u' ≤ obj hne C u) :
    ∃ e : Equiv.Perm (Fin n), ∑ i, C i (e i) = obj hne C u := by
  classical
  set v := vpot hne C u
  let T : Fin n → Finset (Fin n) := fun i ↦ Finset.univ.filter fun j ↦ u i + v j = C i j
  by_cases hall : ∀ S : Finset (Fin n), S.card ≤ (S.biUnion T).card
  · obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective T).mp hall
    let e : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
    refine ⟨e, ?_⟩
    have he : ∀ i, C i (e i) = u i + v (e i) := fun i ↦ ((Finset.mem_filter.mp (hf i)).2).symm
    rw [Finset.sum_congr rfl fun i _ ↦ he i, Finset.sum_add_distrib, Equiv.sum_comp e v]
    rfl
  · exfalso
    push Not at hall
    obtain ⟨S, hS⟩ := hall
    set N := S.biUnion T
    have hslack : ∀ i ∈ S, ∀ j ∉ N, 0 < C i j - u i - v j := by
      intro i hi j hj
      have hle := add_vpot_le hne C u i j
      have hne' : u i + v j ≠ C i j := fun h ↦
        hj (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩⟩)
      have := lt_of_le_of_ne hle hne'
      linarith
    let g : Fin n × Fin n → ℝ := fun p ↦
      if p.1 ∈ S ∧ p.2 ∉ N then C p.1 p.2 - u p.1 - v p.2 else 1
    have hne2 : (Finset.univ : Finset (Fin n × Fin n)).Nonempty := by
      obtain ⟨i₀, -⟩ := hne
      exact ⟨(i₀, i₀), Finset.mem_univ _⟩
    set ε := Finset.univ.inf' hne2 g
    have hε : 0 < ε := by
      refine (Finset.lt_inf'_iff _).mpr fun p _ ↦ ?_
      simp only [g]
      split_ifs with h
      · exact hslack _ h.1 _ h.2
      · exact one_pos
    have hεle : ∀ i ∈ S, ∀ j ∉ N, ε ≤ C i j - u i - v j := fun i hi j hj ↦ by
      have := Finset.inf'_le g (Finset.mem_univ (i, j))
      simp only [g, ite_eq_left (And.intro hi hj)] at this
      exact this
    let u' : Fin n → ℝ := fun i ↦ u i + if i ∈ S then ε else 0
    have hv1 : ∀ j, v j - (if j ∈ N then ε else 0) ≤ vpot hne C u' j := by
      intro j
      refine le_vpot hne C u' j fun i ↦ ?_
      have := vpot_le hne C u i j
      by_cases hj : j ∈ N
      · simp only [u', hj, ite_true]
        split_ifs <;> linarith
      · simp only [u', hj, ite_false]
        split_ifs with hi
        · have := hεle i hi j hj
          linarith
        · linarith
    have hsum_u : ∑ i, u' i = ∑ i, u i + S.card * ε := by
      simp only [u', Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul]
    have hsum_v : ∑ j, (v j - if j ∈ N then ε else 0) = ∑ j, v j - N.card * ε := by
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul]
    have key : obj hne C u + ((S.card : ℝ) - N.card) * ε ≤ obj hne C u' := by
      have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hv1 j
      rw [hsum_v] at this
      unfold obj
      rw [hsum_u]
      linarith
    have hcard : (0 : ℝ) < (S.card : ℝ) - N.card := by
      have : (N.card : ℝ) < S.card := by exact_mod_cast hS
      linarith
    have := hu u'
    have := mul_pos hcard hε
    linarith

end Egervary

/-- **Egerváry's theorem**: an optimal assignment together with optimal dual potentials. For every
real `n × n` matrix `C` there are a permutation `e` and potentials `u, v` with
`u i + v j ≤ C i j` for all `i, j` and `∑ᵢ C i (e i) = ∑ᵢ u i + ∑ⱼ v j`. -/
theorem exists_perm_potentials {n : ℕ} (C : Fin n → Fin n → ℝ) :
    ∃ (e : Equiv.Perm (Fin n)) (u v : Fin n → ℝ), (∀ i j, u i + v j ≤ C i j) ∧
      ∑ i, C i (e i) = ∑ i, u i + ∑ j, v j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, 0, 0, fun i ↦ i.elim0, by simp⟩
  · have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    obtain ⟨u, hu⟩ := Egervary.exists_max hne C
    obtain ⟨e, he⟩ := Egervary.exists_perm_of_max hne C u hu
    exact ⟨e, u, Egervary.vpot hne C u, Egervary.add_vpot_le hne C u, he⟩

/-- A multiset of cardinality `n` is the image of `Finset.univ` under a map `Fin n → α`, i.e. it
can be enumerated as `{x 0, …, x (n - 1)}`. -/
theorem Multiset.exists_fin_enum {α : Type*} (M : Multiset α) {n : ℕ}
    (h : Multiset.card M = n) : ∃ x : Fin n → α, Finset.univ.val.map x = M := by
  have hl : M.toList.length = n := by rw [Multiset.length_toList, h]
  subst hl
  exact ⟨M.toList.get, by rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]⟩

namespace FinProb

variable {X : Type*} [PseudoMetricSpace X]

/-- Kantorovich–Rubinstein duality for uniform measures: two multisets of the same cardinality
admit a pairing whose average cost is at most the `W₁`-distance of the uniform measures (the
non-trivial inequality in Proposition 2.2 of [Basso2024bicombings]). -/
theorem exists_pairing_le_W1 {M N : Multiset X} (hM : M ≠ 0) (hN : N ≠ 0)
    (hcard : Multiset.card M = Multiset.card N) :
    ∃ P : Multiset (X × X), P.map Prod.fst = M ∧ P.map Prod.snd = N ∧
      (P.map fun p ↦ dist p.1 p.2).sum / Multiset.card M ≤
        W1 (ofMultiset M hM) (ofMultiset N hN) := by
  obtain ⟨n, hn⟩ : ∃ n, Multiset.card M = n := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ := Multiset.exists_fin_enum M hn
  obtain ⟨y, hy⟩ := Multiset.exists_fin_enum N (hcard.symm.trans hn)
  obtain ⟨e, u, v, huv, he⟩ := exists_perm_potentials fun i j ↦ dist (x i) (y j)
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn ▸ Multiset.card_pos.mpr hM⟩, Finset.mem_univ _⟩
  -- the Kantorovich potential `f z = minⱼ (d(z, y j) - v j)`
  let f : X → ℝ := fun z ↦ Finset.univ.inf' hne fun j ↦ dist z (y j) - v j
  have hf : LipschitzWith 1 f := LipschitzWith.of_le_add fun z z' ↦ by
    have : f z - dist z z' ≤ f z' := Finset.le_inf' hne _ fun j _ ↦ by
      have h1 : f z ≤ dist z (y j) - v j := Finset.inf'_le _ (Finset.mem_univ j)
      have h2 := dist_triangle z z' (y j)
      linarith
    linarith
  have hfx : ∀ i, u i ≤ f (x i) := fun i ↦ Finset.le_inf' hne _ fun j _ ↦ by
    linarith [huv i j]
  have hfy : ∀ j, f (y j) ≤ -v j := fun j ↦
    (Finset.inf'_le _ (Finset.mem_univ j)).trans_eq (by rw [dist_self, zero_sub])
  refine ⟨Finset.univ.val.map fun i ↦ (x i, y (e i)), ?_, ?_, ?_⟩
  · rw [Multiset.map_map, ← hx]
    rfl
  · rw [Multiset.map_map, ← hy]
    change Finset.univ.val.map (y ∘ e) = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  · have hMf : (M.map f).sum = ∑ i, f (x i) := by
      rw [← hx, Multiset.map_map]
      rfl
    have hNf : (N.map f).sum = ∑ j, f (y j) := by
      rw [← hy, Multiset.map_map]
      rfl
    have hpair := pairing_le_W1 (ofMultiset M hM) (ofMultiset N hN) hf
    rw [pairing_ofMultiset f hM hN hcard, hMf, hNf] at hpair
    refine le_trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) hpair
    rw [Multiset.map_map]
    change ∑ i, dist (x i) (y (e i)) ≤ _
    rw [he]
    have h1 : ∑ i, u i ≤ ∑ i, f (x i) := Finset.sum_le_sum fun i _ ↦ hfx i
    have h2 : ∑ j, v j ≤ -∑ j, f (y j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun j _ ↦ by linarith [hfy j]
    linarith

end FinProb

end LipschitzExtension
