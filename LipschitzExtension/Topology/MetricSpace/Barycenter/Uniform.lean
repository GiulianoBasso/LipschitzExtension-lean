/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Barycenter.Defs

/-!
# Uniform measures on finite multisets

For a nonempty finite multiset `M` of points, `FinProb.ofMultiset M` is the uniform probability
measure `(1/#M) ∑_{a ∈ M} δ_a` (points are counted with multiplicity). These are exactly the
finitely supported probability measures with rational weights.

We also record the easy half of the formula of Proposition 2.2 of [Basso2024bicombings]: the
`W₁`-distance of two uniform measures is at most the average cost of any pairing (coupling) of the
points (`FinProb.W1_ofMultiset_le`; the other half is `FinProb.exists_pairing_le_W1`).

## Main definitions

* `FinProb.ofMultiset`: the uniform probability measure on a nonempty finite multiset.

## Main statements

* `FinProb.ofMultiset_w_apply`: the weight of `y` in the uniform measure on `M` is
  `count y M / #M`.
* `FinProb.ofMultiset_nsmul`: repeating every point `k` times does not change the uniform measure.
* `FinProb.ofMultiset_map_comp_eq_ofWeights`: the uniform measure on a family `x ∘ p`, written with
  counting weights on the index type of `x`.
* `FinProb.W1_ofMultiset_le`: the `W₁`-distance of the uniform measures on the two marginals of a
  multiset of pairs is at most the average distance of the pairs (the easy half of
  Proposition 2.2 of [Basso2024bicombings]).

## References

* [G. Basso, *Extending and improving conical bicombings*][Basso2024bicombings]
-/

open Set

namespace LipschitzExtension

namespace FinProb

variable {X : Type*}

/-- The weight at `y` of `∑_{a ∈ M} c δ_a` is `count y M * c`. -/
private theorem multiset_sum_single_apply [DecidableEq X] (M : Multiset X) (c : ℝ) (y : X) :
    (M.map fun a ↦ Finsupp.single a c).sum y = (M.count y : ℝ) * c := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply, ih, Multiset.count_cons,
      Finsupp.single_apply]
    by_cases h : a = y
    · rw [ite_eq_left h, ite_eq_left h.symm, Nat.cast_add, Nat.cast_one]
      ring
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), Nat.cast_add, Nat.cast_zero, add_zero,
        zero_add]

/-- Integration against `∑_{a ∈ M} c δ_a`. -/
private theorem multiset_sum_single_sum (M : Multiset X) (c : ℝ) (g : X → ℝ) :
    (M.map fun a ↦ Finsupp.single a c).sum.sum (fun y a ↦ g y * a) = (M.map g).sum * c := by
  rw [Finsupp.multiset_sum_sum_index _ _ (fun _ ↦ mul_zero _) (fun _ _ _ ↦ mul_add _ _ _),
    Multiset.map_map, ← Multiset.sum_map_mul_right]
  congr 1
  exact Multiset.map_congr rfl fun a _ ↦ Finsupp.sum_single_index (mul_zero _)

private theorem cast_card_ne_zero {M : Multiset X} (hM : M ≠ 0) :
    (Multiset.card M : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Multiset.card_pos.mpr hM).ne'

/-- The uniform probability measure `(1/#M) ∑_{a ∈ M} δ_a` on a nonempty multiset `M`. -/
noncomputable def ofMultiset (M : Multiset X) (hM : M ≠ 0) : FinProb X where
  w := (M.map fun a ↦ Finsupp.single a (1 / (Multiset.card M : ℝ))).sum
  nonneg := by
    classical
    intro y
    rw [multiset_sum_single_apply]
    positivity
  sum_eq_one := by
    have h := multiset_sum_single_sum M (1 / (Multiset.card M : ℝ)) (fun _ ↦ 1)
    simp only [one_mul] at h
    rw [h, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one, mul_one_div,
      div_self (cast_card_ne_zero hM)]

/-- The weight of `y` in the uniform measure on `M` is `count y M / #M`. -/
theorem ofMultiset_w_apply [DecidableEq X] (M : Multiset X) (hM : M ≠ 0) (y : X) :
    (ofMultiset M hM).w y = (M.count y : ℝ) / Multiset.card M :=
  (multiset_sum_single_apply M _ y).trans (mul_one_div _ _)

/-- The support of the uniform measure on `M` is the set of points of `M`. -/
theorem support_ofMultiset [DecidableEq X] (M : Multiset X) (hM : M ≠ 0) :
    (ofMultiset M hM).w.support = M.toFinset := by
  ext y
  rw [Finsupp.mem_support_iff, ofMultiset_w_apply, Multiset.mem_toFinset, div_ne_zero_iff,
    Nat.cast_ne_zero, Multiset.count_ne_zero]
  exact and_iff_left (cast_card_ne_zero hM)

/-- `ofMultiset M hM` only depends on `M`. -/
theorem ofMultiset_congr {M N : Multiset X} (h : M = N) (hM : M ≠ 0) (hN : N ≠ 0) :
    ofMultiset M hM = ofMultiset N hN := by
  subst h
  rfl

/-- Repeating every point `k` times does not change the uniform measure. -/
theorem ofMultiset_nsmul (M : Multiset X) (hM : M ≠ 0) {k : ℕ} (hkM : k • M ≠ 0) :
    ofMultiset (k • M) hkM = ofMultiset M hM := by
  classical
  have hk : (k : ℝ) ≠ 0 := by
    intro h
    rw [Nat.cast_eq_zero] at h
    subst h
    exact hkM (zero_nsmul M)
  refine ext_w (Finsupp.ext fun y ↦ ?_)
  rw [ofMultiset_w_apply, ofMultiset_w_apply, Multiset.count_nsmul, Multiset.card_nsmul,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hk]

/-- The uniform measure on `n` copies of `a` is `δ_a`. -/
theorem ofMultiset_replicate {n : ℕ} (a : X) (h : Multiset.replicate n a ≠ 0) :
    ofMultiset (Multiset.replicate n a) h = dirac a := by
  classical
  have hn : (n : ℝ) ≠ 0 := by
    intro hn
    rw [Nat.cast_eq_zero] at hn
    subst hn
    exact h (Multiset.replicate_zero a)
  refine ext_w (Finsupp.ext fun y ↦ ?_)
  rw [ofMultiset_w_apply, Multiset.count_replicate, Multiset.card_replicate]
  change _ = Finsupp.single a (1 : ℝ) y
  rw [Finsupp.single_apply]
  split_ifs
  · exact div_self hn
  · rw [Nat.cast_zero, zero_div]

/-- The uniform measure on a family `x ∘ p` indexed by a finset `I` is
`∑_j (#{i ∈ I | p i = j} / #I) δ_{x j}`, written with counting weights on the index type of
`x`. -/
theorem ofMultiset_map_comp_eq_ofWeights {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : Finset ι) (p : ι → κ) (x : κ → X) (hI : I.val.map (x ∘ p) ≠ 0)
    (h0 : ∀ j ∈ (Finset.univ : Finset κ), 0 ≤ ((I.filter fun i ↦ p i = j).card : ℝ) / I.card)
    (h1 : ∑ j ∈ (Finset.univ : Finset κ), ((I.filter fun i ↦ p i = j).card : ℝ) / I.card = 1) :
    ofMultiset (I.val.map (x ∘ p)) hI =
      ofWeights Finset.univ x (fun j ↦ ((I.filter fun i ↦ p i = j).card : ℝ) / I.card) h0 h1 := by
  classical
  refine ext_w (Finsupp.ext fun y ↦ ?_)
  -- `#{i ∈ I | x (p i) = y} = ∑_{j, x j = y} #{i ∈ I | p i = j}`
  have hmaps : Set.MapsTo p ↑(I.filter fun i ↦ y = (x ∘ p) i)
      ↑(Finset.univ.filter fun j ↦ x j = y) := by
    intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, hi.2.symm⟩
  have hcount : (Multiset.filter (fun a ↦ y = (x ∘ p) a) I.val).card =
      ∑ j ∈ Finset.univ with x j = y, (I.filter fun i ↦ p i = j).card := by
    rw [← Finset.filter_val, Finset.card_val, Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩)
    rw [Function.comp_apply, h, (Finset.mem_filter.mp hj).2]
  rw [ofMultiset_w_apply, Multiset.count_map, Multiset.card_map, hcount, Nat.cast_sum,
    Finset.card_val, div_eq_mul_inv, Finset.sum_mul]
  change _ = (∑ j ∈ Finset.univ, _ • Finsupp.single (x j) (1 : ℝ)) y
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ ↦ (div_eq_mul_inv _ _).symm

private theorem integ_ofMultiset (g : X → ℝ) (M : Multiset X) (hM : M ≠ 0) :
    integ g (ofMultiset M hM) = (M.map g).sum / Multiset.card M :=
  (multiset_sum_single_sum M _ g).trans (mul_one_div _ _)

variable [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
/-- `∫ g d(unif M - unif N) = (∑_{a ∈ M} g a - ∑_{b ∈ N} g b) / #M` if `#M = #N`. -/
theorem pairing_ofMultiset (g : X → ℝ) {M N : Multiset X} (hM : M ≠ 0) (hN : N ≠ 0)
    (hcard : Multiset.card M = Multiset.card N) :
    pairing g (ofMultiset M hM) (ofMultiset N hN) =
      ((M.map g).sum - (N.map g).sum) / Multiset.card M := by
  rw [pairing_eq_integ_sub, integ_ofMultiset, integ_ofMultiset, hcard, sub_div]

/-- The `W₁`-distance of the uniform measures on the two marginals of a multiset of pairs `P` is
at most the average distance `(1/#P) ∑_{(a, b) ∈ P} d(a, b)` (the easy half of Proposition 2.2 of
[Basso2024bicombings]). -/
theorem W1_ofMultiset_le (P : Multiset (X × X)) (h₁ : P.map Prod.fst ≠ 0)
    (h₂ : P.map Prod.snd ≠ 0) :
    W1 (ofMultiset (P.map Prod.fst) h₁) (ofMultiset (P.map Prod.snd) h₂) ≤
      (P.map fun p ↦ dist p.1 p.2).sum / Multiset.card P := by
  refine W1_le fun g hg ↦ ?_
  rw [pairing_ofMultiset g h₁ h₂ (by rw [Multiset.card_map, Multiset.card_map]),
    Multiset.card_map, Multiset.map_map, Multiset.map_map, ← Multiset.sum_map_sub]
  refine div_le_div_of_nonneg_right
    (Multiset.sum_map_le_sum_map _ _ fun p _ ↦ ?_) (Nat.cast_nonneg _)
  exact sub_le_dist_of_lipschitz hg p.1 p.2

end FinProb

end LipschitzExtension
