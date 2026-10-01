/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.WhitneyCovering.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.MeanInequalities
import LipschitzExtension.Topology.MetricSpace.PointwiseLipschitz.Basic

/-!
# Lipschitz partitions of unity subordinate to Whitney families

This file proves Lemma 3.2 of [Basso2024] (an idea of Johnson, Lindenstrauss and Schechtman),
with the constant `2e` of item 2) of the errata [BassoClaude2026], in a general form. Let `(B i)`
be a Whitney family for a nonempty set `A` (`IsWhitneyFamily A B r m α δ γ`) with `0 < δ < 1`,
and let `p > 1`. Then there is a partition of unity `(φ i)` on `{z | 0 < d(z, A)}`, subordinate to
the open sets `U i = N_{δ r i}(B i) = {z | infDist z (B i) < δ r i}` and with `φ i > 0` on `B i`,
such that at every point `z ∈ B j` the pointwise Lipschitz constants satisfy
`∑ i, Lip φ i (z) ≤ 2 p m^(1/p) / (δ r j)`.

In the paper `m = 3(n + 1)` is the multiplicity of the Whitney family of Proposition 3.1, and the
lemma states `∑ i, Lip φ i (z) ≤ 6 log(3(n + 1)) / (δ r j)`; by item 2) of the errata the proof
gives the constant `2e` instead of `6`. This is the case `p = log m`, for which `m^(1/p) = e`
(`IsWhitneyFamily.exists_partitionOfUnity_log`; note `2e ≤ 6`). In the proof of Theorem 6.1 one
can use `p = 2 log₂(n + 2)` for the multiplicity `m = n + 1`.

The proofs of the paper only use the pointwise Lipschitz constant of `z ↦ (φ i z)_i` with respect
to the `ℓ¹`-norm, which is at most `∑ i, Lip φ i (z)`: at every `z ∈ B j`,
`∑ i |φ i z - φ i z'| ≤ K d(z, z')` for `z'` near `z` and every `K > 2 p m^(1/p) / (δ r j)`.

## Main definitions

* `WhitneyPoU.Psi g p`, `WhitneyPoU.phi g p`: the functions `Ψ = ∑ᶠ i, g i ^ p` and
  `φ i = g i ^ p / Ψ` built from a family `g : ι → Z → ℝ`.
* `WhitneyPoU.distCompl B r δ`: the family `g i = d(·, (U i)ᶜ)` used for Lemma 3.2.

## Main statements

* `IsWhitneyFamily.exists_partitionOfUnity`: Lemma 3.2 for the pointwise Lipschitz constant of
  `z ↦ (φ i z)_i` in `ℓ¹`; this is the form used in the proofs of Theorems 1.2 and 6.1.
* `IsWhitneyFamily.exists_partitionOfUnity_lipAt`: Lemma 3.2 for the sum of the pointwise
  Lipschitz constants of the `φ i`, for every `p > 1`.
* `IsWhitneyFamily.exists_partitionOfUnity_log`: Lemma 3.2 as in the paper, with the constant
  `2e` of the errata: `∑ i, Lip φ i (z) ≤ 2e log m / (δ r j)` for `m ≥ 3`.
* `WhitneyPoU.eventually_sum_abs_phi_sub_le`, `WhitneyPoU.exists_lipAt_phi`: the corresponding
  estimates for an abstract family `g`.

## Proof outline

We follow the proof of the paper. Put `ψ i z = infDist z (U i)ᶜ ^ p`, `ψ = ∑ i, ψ i` and
`φ i = ψ i / ψ`. Note `(U i)ᶜ ⊇ A ≠ ∅` since `δ < 1`, and for `z ∈ B j` we have
`ψ z ≥ ψ j z ≥ (δ r j)^p > 0`.

* The `ℓ¹` estimate. One has `∑ i |φ i z - φ i z'| ≤ (2/ψ z) ∑ i |ψ i z - ψ i z'|`. For indices
  with `z ∈ U i` (at most `m`) use `|a^p - b^p| ≤ p max(a,b)^(p-1) |a - b|`; for indices with
  `z ∉ U i`, `z' ∈ U i` (at most `m`) use `ψ i z' ≤ d(z, z')^p = o(d(z,z'))` (here `p > 1` is
  used). Finally Hölder's inequality gives
  `∑_{i : z ∈ U i} ψ i z ^ ((p-1)/p) ≤ m^(1/p) ψ(z)^((p-1)/p)`.
* The sum of the pointwise Lipschitz constants. At `z` with `ψ_i(z) > 0` (at most `m` indices)
  one has `Lip ψ_i(z) ≤ p ψ_i(z)^((p-1)/p)` and, from
  `|φ_i(z) - φ_i(z')| ≤ |ψ_i(z) - ψ_i(z')|/ψ(z) + ψ_i(z') ∑_k |ψ_k(z) - ψ_k(z')| / (ψ(z) ψ(z'))`,
  `Lip φ_i(z) ≤ Lip ψ_i(z)/ψ(z) + ψ_i(z) S/ψ(z)²` with `S = ∑_k p ψ_k(z)^((p-1)/p)`. If
  `ψ_i(z) = 0` then `ψ_i(z') ≤ d(z, z')^p`, so `Lip φ_i(z) = 0` (here `p > 1` is used). Summing,
  `∑_i Lip φ_i(z) ≤ 2S/ψ(z) ≤ 2 p m^(1/p) ψ(z)^(-1/p) ≤ 2 p m^(1/p)/(δ r_j)` by Hölder's
  inequality and `ψ(z) ≥ ψ_j(z) ≥ (δ r_j)^p`.

## Implementation notes

The construction is carried out for an abstract family `g : ι → Z → ℝ` of nonnegative
`1`-Lipschitz functions (namespace `LipschitzExtension.WhitneyPoU`), with
`WhitneyPoU.Psi g p w = ∑ᶠ i, g i w ^ p` and `WhitneyPoU.phi g p i w = g i w ^ p / Psi g p w`.
The estimates `WhitneyPoU.eventually_sum_abs_phi_sub_le` (for `∑ i ∈ s, |φ i z - φ i z'|`, with
`K > 2 p m^(1/p) / c`) and `WhitneyPoU.exists_lipAt_phi` (for the sum of the pointwise Lipschitz
constants, bounded by `2 p m^(1/p) / c`) hold provided `0 < c ≤ g j z` for some `j` and, near
`z`, at most `m` of the `g i` are nonzero (and, for the first estimate, one of them is
positive). The index type may be infinite: all sums are over explicit finite sets of indices.
Lemma 3.2 is the case `g = WhitneyPoU.distCompl B r δ`, i.e. `g i w = infDist w (U i)ᶜ`.

Pointwise Lipschitz constants are expressed with `LipAt`: `LipAt f z L` means `Lip f (z) ≤ L`.
That the individual `φ i` are Lipschitz (which is never used) is not formalized.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
-/

open Set Metric Filter Topology

namespace LipschitzExtension

namespace WhitneyPoU

/-! ### Elementary real inequalities -/

/-- Tangent line inequality for `x ↦ x ^ p`, `p ≥ 1`: for `0 ≤ x ≤ y`,
`y ^ p - x ^ p ≤ p y ^ (p - 1) (y - x)` (a consequence of Bernoulli's inequality). -/
theorem rpow_sub_rpow_le_of_le {x y p : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hp : 1 ≤ p) :
    y ^ p - x ^ p ≤ p * y ^ (p - 1) * (y - x) := by
  rcases eq_or_lt_of_le (hx.trans hxy) with hy | hy
  · have hx0 : x = 0 := le_antisymm (hy ▸ hxy) hx
    subst hx0
    rw [← hy]
    simp
  · have hs : -1 ≤ x / y - 1 := by
      have : 0 ≤ x / y := div_nonneg hx hy.le
      linarith
    have hb := one_add_mul_self_le_rpow_one_add hs hp
    have e1 : 1 + (x / y - 1) = x / y := by ring
    rw [e1, Real.div_rpow hx hy.le] at hb
    have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy p
    rw [le_div_iff₀ hyp] at hb
    have key : y ^ p = y ^ (p - 1) * y := by
      rw [Real.rpow_sub_one hy.ne', div_mul_cancel₀ _ hy.ne']
    have e2 : (1 + p * (x / y - 1)) * y ^ p = y ^ p - p * y ^ (p - 1) * (y - x) := by
      rw [key]
      field_simp
      ring
    linarith

/-- `|a ^ p - b ^ p| ≤ p (a + d) ^ (p - 1) d` for `a, b ≥ 0`, `|a - b| ≤ d` and `p ≥ 1`. -/
theorem abs_rpow_sub_rpow_le {a b d p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : |a - b| ≤ d)
    (hp : 1 ≤ p) : |a ^ p - b ^ p| ≤ p * (a + d) ^ (p - 1) * d := by
  have hd : 0 ≤ d := (abs_nonneg _).trans hab
  have hp1 : 0 ≤ p - 1 := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hpad : 0 ≤ p * (a + d) ^ (p - 1) := mul_nonneg hp0 (Real.rpow_nonneg (by linarith) _)
  rw [abs_le] at hab
  rcases le_total a b with h | h
  · have hmono : a ^ p ≤ b ^ p := Real.rpow_le_rpow ha h hp0
    rw [abs_of_nonpos (by linarith)]
    have h2 : b ^ (p - 1) ≤ (a + d) ^ (p - 1) := Real.rpow_le_rpow hb (by linarith) hp1
    calc -(a ^ p - b ^ p) = b ^ p - a ^ p := by ring
      _ ≤ p * b ^ (p - 1) * (b - a) := rpow_sub_rpow_le_of_le ha h hp
      _ ≤ p * (a + d) ^ (p - 1) * d :=
        mul_le_mul (mul_le_mul_of_nonneg_left h2 hp0) (by linarith) (by linarith) hpad
  · have hmono : b ^ p ≤ a ^ p := Real.rpow_le_rpow hb h hp0
    rw [abs_of_nonneg (by linarith)]
    have h2 : a ^ (p - 1) ≤ (a + d) ^ (p - 1) := Real.rpow_le_rpow ha (by linarith) hp1
    calc a ^ p - b ^ p ≤ p * a ^ (p - 1) * (a - b) := rpow_sub_rpow_le_of_le hb h hp
      _ ≤ p * (a + d) ^ (p - 1) * d :=
        mul_le_mul (mul_le_mul_of_nonneg_left h2 hp0) (by linarith) (by linarith) hpad

/-- Hölder's inequality in the form needed:
`∑_{i ∈ s} x i ^ (p - 1) ≤ #s ^ (1/p) (∑_{i ∈ s} x i ^ p) ^ ((p - 1)/p)`. -/
theorem sum_rpow_sub_one_le {ι : Type*} (s : Finset ι) {x : ι → ℝ} (hx : ∀ i ∈ s, 0 ≤ x i)
    {p : ℝ} (hp : 1 < p) :
    ∑ i ∈ s, x i ^ (p - 1) ≤ (s.card : ℝ) ^ (1 / p) * (∑ i ∈ s, x i ^ p) ^ ((p - 1) / p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq (f := fun _ ↦ (1 : ℝ))
    (g := fun i ↦ x i ^ (p - 1)) (fun _ _ ↦ zero_le_one)
    (fun i hi ↦ Real.rpow_nonneg (hx i hi) _)
  simp only [one_mul, Real.one_rpow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have h2 : ∀ i ∈ s, (x i ^ (p - 1)) ^ Real.conjExponent p = x i ^ p := by
    intro i hi
    rw [← Real.rpow_mul (hx i hi), hpq.sub_one_mul_conj]
  rw [Finset.sum_congr rfl h2] at h
  have h3 : 1 / Real.conjExponent p = (p - 1) / p := by
    rw [Real.conjExponent, one_div_div]
  rwa [h3] at h

/-- The elementary estimate `∑ |a i / σ - b i / σ'| ≤ (2 / σ) ∑ |a i - b i|` for
`σ = ∑ a i > 0`, `σ' = ∑ b i > 0`, `b ≥ 0`. -/
theorem sum_abs_div_sub_div_le {ι : Type*} {T : Finset ι} {a b : ι → ℝ}
    (hb : ∀ i ∈ T, 0 ≤ b i) (ha' : 0 < ∑ i ∈ T, a i) (hb' : 0 < ∑ i ∈ T, b i) :
    ∑ i ∈ T, |a i / (∑ k ∈ T, a k) - b i / (∑ k ∈ T, b k)| ≤
      2 / (∑ k ∈ T, a k) * ∑ i ∈ T, |a i - b i| := by
  set σ := ∑ k ∈ T, a k with hσ
  set σ' := ∑ k ∈ T, b k with hσ'
  set D := ∑ i ∈ T, |a i - b i| with hD
  have hdiff : |σ' - σ| ≤ D := by
    rw [hσ, hσ', ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ ↦ abs_sub_comm _ _
  have hterm : ∀ i ∈ T,
      |a i / σ - b i / σ'| ≤ |a i - b i| / σ + b i * (|σ' - σ| / (σ * σ')) := by
    intro i hi
    have e : a i / σ - b i / σ' = (a i - b i) / σ + b i * ((σ' - σ) / (σ * σ')) := by
      field_simp
      ring
    rw [e]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos ha', abs_mul, abs_of_nonneg (hb i hi), abs_div,
      abs_of_pos (mul_pos ha' hb')]
  calc ∑ i ∈ T, |a i / σ - b i / σ'|
      ≤ ∑ i ∈ T, (|a i - b i| / σ + b i * (|σ' - σ| / (σ * σ'))) := Finset.sum_le_sum hterm
    _ = D / σ + σ' * (|σ' - σ| / (σ * σ')) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    _ = D / σ + |σ' - σ| / σ := by
      field_simp
    _ ≤ D / σ + D / σ := by gcongr
    _ = 2 / σ * D := by ring

/-- A set with at most `m` elements is the set of elements of a `Finset` with at most `m`
elements. -/
theorem exists_finset_of_encard_le {ι : Type*} {s : Set ι} {m : ℕ} (h : s.encard ≤ m) :
    ∃ S : Finset ι, (∀ i, i ∈ S ↔ i ∈ s) ∧ S.card ≤ m := by
  have hfin := Set.finite_of_encard_le_coe h
  refine ⟨hfin.toFinset, fun i ↦ hfin.mem_toFinset, ?_⟩
  rw [hfin.encard_eq_coe_toFinset_card] at h
  exact_mod_cast h

/-! ### The partition of unity `φ i = g i ^ p / ∑ᶠ k, g k ^ p` -/

section Abstract

variable {Z : Type*} {ι : Type*}

/-- The normalizing function `Ψ w = ∑ᶠ i, g i w ^ p` (a genuine finite sum wherever only finitely
many `g i w ≠ 0`). -/
noncomputable def Psi (g : ι → Z → ℝ) (p : ℝ) (w : Z) : ℝ := ∑ᶠ i, g i w ^ p

/-- The partition of unity `φ i w = g i w ^ p / Ψ w` built from the family `g`. -/
noncomputable def phi (g : ι → Z → ℝ) (p : ℝ) (i : ι) (w : Z) : ℝ := g i w ^ p / Psi g p w

variable {g : ι → Z → ℝ} {p : ℝ}

theorem Psi_nonneg (hg0 : ∀ i w, 0 ≤ g i w) (w : Z) : 0 ≤ Psi g p w :=
  finsum_nonneg fun i ↦ Real.rpow_nonneg (hg0 i w) p

/-- If all `g i w` with `i ∉ s` vanish, then `Ψ w = ∑ i ∈ s, g i w ^ p`. -/
theorem Psi_eq_sum (hp : p ≠ 0) {w : Z} {s : Finset ι}
    (hs : {i | g i w ≠ 0} ⊆ ↑s) : Psi g p w = ∑ i ∈ s, g i w ^ p := by
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply hs
  intro h0
  apply hi
  simp only [h0, Real.zero_rpow hp]

theorem le_Psi (hg0 : ∀ i w, 0 ≤ g i w) (hp : p ≠ 0) {w : Z} (hfin : {i | g i w ≠ 0}.Finite)
    (j : ι) : g j w ^ p ≤ Psi g p w := by
  classical
  have hs : {i | g i w ≠ 0} ⊆ ↑(insert j hfin.toFinset) := by
    intro i hi
    rw [Finset.coe_insert, Set.Finite.coe_toFinset]
    exact Set.mem_insert_of_mem _ hi
  rw [Psi_eq_sum hp hs]
  exact Finset.single_le_sum (f := fun i ↦ g i w ^ p)
    (fun i _ ↦ Real.rpow_nonneg (hg0 i w) p) (Finset.mem_insert_self j _)

theorem Psi_pos (hg0 : ∀ i w, 0 ≤ g i w) (hp : p ≠ 0) {w : Z} (hfin : {i | g i w ≠ 0}.Finite)
    {j : ι} (hj : 0 < g j w) : 0 < Psi g p w :=
  (Real.rpow_pos_of_pos hj p).trans_le (le_Psi hg0 hp hfin j)

theorem phi_nonneg (hg0 : ∀ i w, 0 ≤ g i w) (i : ι) (w : Z) : 0 ≤ phi g p i w :=
  div_nonneg (Real.rpow_nonneg (hg0 i w) p) (Psi_nonneg hg0 w)

theorem phi_eq_zero (hp : p ≠ 0) {i : ι} {w : Z} (h : g i w = 0) : phi g p i w = 0 := by
  simp [phi, h, Real.zero_rpow hp]

theorem phi_pos (hg0 : ∀ i w, 0 ≤ g i w) (hp : p ≠ 0) {w : Z} (hfin : {i | g i w ≠ 0}.Finite)
    {j : ι} (hj : 0 < g j w) : 0 < phi g p j w :=
  div_pos (Real.rpow_pos_of_pos hj p) (Psi_pos hg0 hp hfin hj)

/-- Where `Ψ w > 0`, the `φ i w` sum to `1` (over any finite set containing their support). -/
theorem sum_phi_eq_one (hg0 : ∀ i w, 0 ≤ g i w) (hp : p ≠ 0) {w : Z} (hpos : 0 < Psi g p w)
    {s : Finset ι} (hs : {i | phi g p i w ≠ 0} ⊆ ↑s) : ∑ i ∈ s, phi g p i w = 1 := by
  have hs' : {i | g i w ≠ 0} ⊆ ↑s := by
    intro i hi
    apply hs
    exact div_ne_zero ((Real.rpow_eq_zero (hg0 i w) hp).not.mpr hi) hpos.ne'
  simp only [phi]
  rw [← Finset.sum_div, ← Psi_eq_sum hp hs', div_self hpos.ne']

end Abstract

section Metric

variable {Z : Type*} [PseudoMetricSpace Z] {ι : Type*} {g : ι → Z → ℝ} {p : ℝ}

/-- The core estimate of Lemma 3.2 (in the `ℓ¹` form) for an abstract family `g i` of nonnegative
`1`-Lipschitz functions with locally bounded multiplicity: if near `z` at most `m` of the `g i` are
nonzero and one of them is positive, and `0 < c ≤ g j z` for some `j`, then for every
`K > 2 p m^(1/p) / c` and every `z'` close to `z`, `∑ i ∈ s, |φ i z - φ i z'| ≤ K d(z, z')` for
all finite `s`. -/
theorem eventually_sum_abs_phi_sub_le (hp : 1 < p) {m : ℕ} {z : Z} {c : ℝ} (hc : 0 < c)
    (hg0 : ∀ i w, 0 ≤ g i w) (hgLip : ∀ i w w', g i w ≤ g i w' + dist w w')
    (hsupp : ∀ᶠ w in 𝓝 z, {i | g i w ≠ 0}.encard ≤ m ∧ ∃ i, 0 < g i w)
    {j : ι} (hj : c ≤ g j z) {K : ℝ} (hK : 2 * p * (m : ℝ) ^ (1 / p) / c < K) :
    ∀ᶠ z' in 𝓝 z, ∀ s : Finset ι, ∑ i ∈ s, |phi g p i z - phi g p i z'| ≤ K * dist z z' := by
  classical
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hp1 : 0 < p - 1 := by linarith
  obtain ⟨hmz, -⟩ := hsupp.self_of_nhds
  have hfinz : {i | g i z ≠ 0}.Finite := Set.finite_of_encard_le_coe hmz
  -- `S`: the (at most `m`) indices with `g i z ≠ 0`
  obtain ⟨S, hS, hScard⟩ := exists_finset_of_encard_le hmz
  have hSsupp : {i | g i z ≠ 0} ⊆ ↑S := fun i hi ↦ Finset.mem_coe.mpr ((hS i).mpr hi)
  have hσpos : 0 < Psi g p z := Psi_pos hg0 hp0 hfinz (hc.trans_le hj)
  have hcσ : c ^ p ≤ Psi g p z :=
    (Real.rpow_le_rpow hc.le hj (by linarith)).trans (le_Psi hg0 hp0 hfinz j)
  have hσS : Psi g p z = ∑ i ∈ S, g i z ^ p := Psi_eq_sum hp0 hSsupp
  -- the difference quotients are bounded by `F (d(z, z'))`, where `F` is continuous and
  -- `F 0 ≤ 2 p m^(1/p) / c < K`
  set F : ℝ → ℝ := fun d ↦ 2 / Psi g p z * p *
    (∑ i ∈ S, (g i z + d) ^ (p - 1) + m * d ^ (p - 1)) with hF
  have hFcont : Continuous F := by
    refine continuous_const.mul ((continuous_finsetSum _ fun i _ ↦ ?_).add
      (continuous_const.mul ?_))
    · exact (continuous_const.add continuous_id).rpow_const fun _ ↦ Or.inr hp1.le
    · exact continuous_id.rpow_const fun _ ↦ Or.inr hp1.le
  have hF0 : F 0 ≤ 2 * p * (m : ℝ) ^ (1 / p) / c := by
    have e0 : F 0 = 2 / Psi g p z * p * ∑ i ∈ S, g i z ^ (p - 1) := by
      simp only [hF, add_zero, Real.zero_rpow hp1.ne', mul_zero]
    -- Hölder's inequality
    have hH := sum_rpow_sub_one_le S (x := fun i ↦ g i z) (fun i _ ↦ hg0 i z) hp
    rw [← hσS] at hH
    rw [e0]
    set σ := Psi g p z with hσ
    have hcle : c ≤ σ ^ (1 / p) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hc.le p) hcσ (by positivity : (0:ℝ) ≤ 1 / p)
      rwa [one_div, Real.rpow_rpow_inv hc.le hp0, ← one_div] at this
    have hprod : σ ^ (1 / p) * σ ^ ((p - 1) / p) = σ := by
      rw [← Real.rpow_add hσpos]
      have : 1 / p + (p - 1) / p = 1 := by field_simp; ring
      rw [this, Real.rpow_one]
    have hkey : c * σ ^ ((p - 1) / p) ≤ σ := by
      calc c * σ ^ ((p - 1) / p) ≤ σ ^ (1 / p) * σ ^ ((p - 1) / p) :=
            mul_le_mul_of_nonneg_right hcle (Real.rpow_nonneg hσpos.le _)
        _ = σ := hprod
    have hm : (S.card : ℝ) ^ (1 / p) ≤ (m : ℝ) ^ (1 / p) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hScard) (by positivity)
    have hmp : 0 ≤ (m : ℝ) ^ (1 / p) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h2σp : 0 ≤ 2 / σ * p := mul_nonneg (div_nonneg zero_le_two hσpos.le) (by linarith)
    rw [le_div_iff₀ hc]
    calc 2 / σ * p * (∑ i ∈ S, g i z ^ (p - 1)) * c
        ≤ 2 / σ * p * ((m : ℝ) ^ (1 / p) * σ ^ ((p - 1) / p)) * c := by
          apply mul_le_mul_of_nonneg_right _ hc.le
          apply mul_le_mul_of_nonneg_left _ h2σp
          exact hH.trans (mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hσpos.le _))
      _ = 2 * p * (m : ℝ) ^ (1 / p) * (c * σ ^ ((p - 1) / p)) / σ := by
          ring
      _ ≤ 2 * p * (m : ℝ) ^ (1 / p) * σ / σ := by
          apply div_le_div_of_nonneg_right _ hσpos.le
          exact mul_le_mul_of_nonneg_left hkey (mul_nonneg (by linarith) hmp)
      _ = 2 * p * (m : ℝ) ^ (1 / p) := mul_div_cancel_right₀ _ hσpos.ne'
  have hev : ∀ᶠ z' in 𝓝 z, F (dist z z') < K := by
    have h1 : Tendsto (fun z' ↦ dist z z') (𝓝 z) (𝓝 0) := by
      have := (continuous_const.dist continuous_id : Continuous fun z' : Z ↦ dist z z').tendsto z
      simpa using this
    exact ((hFcont.tendsto 0).comp h1).eventually_lt_const (hF0.trans_lt hK)
  filter_upwards [hsupp, hev] with z' hz' hFz'
  obtain ⟨hmz', i', hi'⟩ := hz'
  intro s
  have hfinz' : {i | g i z' ≠ 0}.Finite := Set.finite_of_encard_le_coe hmz'
  -- `S'`: the (at most `m`) indices with `g i z' ≠ 0`; all sums are over `T = S ∪ S'`
  obtain ⟨S', hS', hS'card⟩ := exists_finset_of_encard_le hmz'
  set T : Finset ι := S ∪ S' with hT
  have hST : {i | g i z ≠ 0} ⊆ ↑T :=
    hSsupp.trans (Finset.coe_subset.mpr Finset.subset_union_left)
  have hS'T : {i | g i z' ≠ 0} ⊆ ↑T := fun i hi ↦
    Finset.mem_coe.mpr (Finset.mem_union_right _ ((hS' i).mpr hi))
  have hσ' : 0 < Psi g p z' := Psi_pos hg0 hp0 hfinz' hi'
  have hσT : Psi g p z = ∑ i ∈ T, g i z ^ p := Psi_eq_sum hp0 hST
  have hσ'T : Psi g p z' = ∑ i ∈ T, g i z' ^ p := Psi_eq_sum hp0 hS'T
  set d := dist z z' with hd_def
  have hd : 0 ≤ d := dist_nonneg
  -- Step 1: only the indices in `T` contribute
  have step1 : ∑ i ∈ s, |phi g p i z - phi g p i z'| ≤
      ∑ i ∈ T, |phi g p i z - phi g p i z'| := by
    calc ∑ i ∈ s, |phi g p i z - phi g p i z'|
        = ∑ i ∈ s ∩ T, |phi g p i z - phi g p i z'| := by
          symm
          apply Finset.sum_subset Finset.inter_subset_left
          intro i his hiT
          have hiT' : i ∉ T := fun h ↦ hiT (Finset.mem_inter.mpr ⟨his, h⟩)
          have h1 : g i z = 0 := by
            by_contra h
            exact hiT' (hST h)
          have h2 : g i z' = 0 := by
            by_contra h
            exact hiT' (hS'T h)
          simp [phi_eq_zero hp0 h1, phi_eq_zero hp0 h2]
      _ ≤ ∑ i ∈ T, |phi g p i z - phi g p i z'| :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
            (fun _ _ _ ↦ abs_nonneg _)
  -- Step 2: `∑ |φ i z - φ i z'| ≤ (2 / ψ z) ∑ |ψ i z - ψ i z'|`
  have step2 : ∑ i ∈ T, |phi g p i z - phi g p i z'| ≤
      2 / Psi g p z * ∑ i ∈ T, |g i z ^ p - g i z' ^ p| := by
    have hpos1 : 0 < ∑ i ∈ T, g i z ^ p := hσT ▸ hσpos
    have hpos2 : 0 < ∑ i ∈ T, g i z' ^ p := hσ'T ▸ hσ'
    have h := sum_abs_div_sub_div_le (T := T) (a := fun i ↦ g i z ^ p)
      (b := fun i ↦ g i z' ^ p) (fun i _ ↦ Real.rpow_nonneg (hg0 i z') p) hpos1 hpos2
    simp only [phi]
    rw [hσT, hσ'T]
    exact h
  -- Step 3: `|ψ i z - ψ i z'| ≤ p (g i z + d) ^ (p - 1) d`
  have step3 : ∑ i ∈ T, |g i z ^ p - g i z' ^ p| ≤
      p * d * ∑ i ∈ T, (g i z + d) ^ (p - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hlip : |g i z - g i z'| ≤ d := by
      rw [abs_le]
      constructor
      · have := hgLip i z' z
        rw [dist_comm] at this
        linarith
      · have := hgLip i z z'
        linarith
    calc |g i z ^ p - g i z' ^ p| ≤ p * (g i z + d) ^ (p - 1) * d :=
          abs_rpow_sub_rpow_le (hg0 i z) (hg0 i z') hlip hp.le
      _ = p * d * (g i z + d) ^ (p - 1) := by ring
  -- Step 4: the (at most `m`) indices with `g i z = 0 ≠ g i z'` contribute `O(d ^ (p - 1))`
  have step4 : ∑ i ∈ T, (g i z + d) ^ (p - 1) ≤
      ∑ i ∈ S, (g i z + d) ^ (p - 1) + m * d ^ (p - 1) := by
    have hsub : S ⊆ T := Finset.subset_union_left
    rw [← Finset.sum_sdiff hsub]
    have h1 : ∀ i ∈ T \ S, (g i z + d) ^ (p - 1) = d ^ (p - 1) := by
      intro i hi
      have : g i z = 0 := by
        by_contra h
        exact (Finset.mem_sdiff.mp hi).2 ((hS i).mpr h)
      rw [this, zero_add]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((T \ S).card : ℝ) ≤ m := by
      have h2 : T \ S ⊆ S' := by
        intro i hi
        rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hi).1 with h | h
        · exact absurd h (Finset.mem_sdiff.mp hi).2
        · exact h
      exact_mod_cast (Finset.card_le_card h2).trans hS'card
    have hdp : 0 ≤ d ^ (p - 1) := Real.rpow_nonneg hd _
    linarith [mul_le_mul_of_nonneg_right hcard hdp]
  -- Combine
  calc ∑ i ∈ s, |phi g p i z - phi g p i z'|
      ≤ 2 / Psi g p z * ∑ i ∈ T, |g i z ^ p - g i z' ^ p| := step1.trans step2
    _ ≤ 2 / Psi g p z * (p * d * (∑ i ∈ S, (g i z + d) ^ (p - 1) + m * d ^ (p - 1))) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg zero_le_two hσpos.le)
        exact step3.trans (mul_le_mul_of_nonneg_left step4 (mul_nonneg (by linarith) hd))
    _ = F d * d := by
        simp only [hF]
        ring
    _ ≤ K * d := mul_le_mul_of_nonneg_right hFz'.le hd

/-! ### The family `g i = d(·, (U i)ᶜ)` of Lemma 3.2 -/

/-- The distance `d(w, (U i)ᶜ)` to the complement of
`U i = N_{δ r i}(B i) = {x | infDist x (B i) < δ * r i}`; these are the functions `g i` used for
Lemma 3.2. -/
noncomputable def distCompl (B : ι → Set Z) (r : ι → ℝ) (δ : ℝ) (i : ι) (w : Z) : ℝ :=
  infDist w {x | infDist x (B i) < δ * r i}ᶜ

variable {B : ι → Set Z} {r : ι → ℝ} {δ : ℝ}

theorem distCompl_nonneg (i : ι) (w : Z) : 0 ≤ distCompl B r δ i w := infDist_nonneg

theorem distCompl_le_add (i : ι) (w w' : Z) :
    distCompl B r δ i w ≤ distCompl B r δ i w' + dist w w' := infDist_le_infDist_add_dist

theorem distCompl_eq_zero {i : ι} {w : Z} (h : ¬ infDist w (B i) < δ * r i) :
    distCompl B r δ i w = 0 := infDist_zero_of_mem h

end Metric

end WhitneyPoU

namespace IsWhitneyFamily

variable {Z : Type*} [PseudoMetricSpace Z] {ι : Type*} {A : Set Z} {B : ι → Set Z}
  {r : ι → ℝ} {m : ℕ} {α δ γ : ℝ}

/-- `A` lies outside every `U i = N_{δ r i}(B i)` (as `δ < 1`); in particular `(U i)ᶜ ≠ ∅`. -/
theorem compl_nbhd_nonempty (hW : IsWhitneyFamily A B r m α δ γ) (hA : A.Nonempty)
    (hδ1 : δ < 1) (i : ι) : ({x | infDist x (B i) < δ * r i}ᶜ).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  refine ⟨a, fun h ↦ ?_⟩
  have h1 := hW.one_sub_mul_le_infDist h
  rw [infDist_zero_of_mem ha] at h1
  have := hW.r_pos i
  nlinarith

/-- For `x ∈ B i`, `δ r i ≤ d(x, (U i)ᶜ)`. -/
theorem le_distCompl (hW : IsWhitneyFamily A B r m α δ γ) (hA : A.Nonempty) (hδ1 : δ < 1)
    {i : ι} {x : Z} (hx : x ∈ B i) : δ * r i ≤ WhitneyPoU.distCompl B r δ i x := by
  rw [WhitneyPoU.distCompl, le_infDist (hW.compl_nbhd_nonempty hA hδ1 i)]
  intro y hy
  have h1 : δ * r i ≤ infDist y (B i) := not_lt.mp hy
  have h2 : infDist y (B i) ≤ infDist x (B i) + dist y x := infDist_le_infDist_add_dist
  rw [infDist_zero_of_mem hx, zero_add, dist_comm] at h2
  linarith

end IsWhitneyFamily

variable {Z : Type*} [MetricSpace Z] {ι : Type*} {A : Set Z} {B : ι → Set Z} {r : ι → ℝ}
  {m : ℕ} {α δ γ : ℝ}

/-- **Lemma 3.2** of [Basso2024] (general form, for the pointwise Lipschitz constant of
`z ↦ (φ i z)_i` in `ℓ¹`, which is the form used in the proofs): for a Whitney family with
multiplicity `m`, `0 < δ < 1` and `p > 1`, there are nonnegative functions `φ i` which on
`{z | 0 < d(z, A)}` form a partition of unity subordinate to the sets
`U i = N_{δ r i}(B i) = {z | infDist z (B i) < δ r i}`, with finitely many `φ i z ≠ 0` at every
such point `z` and `φ i > 0` on `B i`, such that for `z ∈ B j` and every
`K > 2 p m^(1/p) / (δ r j)` we have `∑ i |φ i z - φ i z'| ≤ K d(z, z')` for all `z'` near `z`. -/
theorem IsWhitneyFamily.exists_partitionOfUnity (hW : IsWhitneyFamily A B r m α δ γ)
    (hA : A.Nonempty) (hδ : 0 < δ) (hδ1 : δ < 1) {p : ℝ} (hp : 1 < p) :
    ∃ φ : ι → Z → ℝ,
      (∀ i z, 0 ≤ φ i z) ∧
      (∀ i z, 0 < infDist z A → φ i z ≠ 0 → infDist z (B i) < δ * r i) ∧
      (∀ i z, z ∈ B i → 0 < φ i z) ∧
      (∀ z, 0 < infDist z A → {i | φ i z ≠ 0}.Finite) ∧
      (∀ z, 0 < infDist z A → ∀ s : Finset ι, {i | φ i z ≠ 0} ⊆ ↑s → ∑ i ∈ s, φ i z = 1) ∧
      (∀ z j, z ∈ B j → ∀ K > 2 * p * (m : ℝ) ^ (1 / p) / (δ * r j),
        ∀ᶠ z' in 𝓝 z, ∀ s : Finset ι, ∑ i ∈ s, |φ i z - φ i z'| ≤ K * dist z z') := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  -- `g i = d(·, (U i)ᶜ)`, `ψ i = g i ^ p`, `φ i = ψ i / ∑ᶠ k, ψ k`
  set g := WhitneyPoU.distCompl B r δ
  have hg0 : ∀ i w, 0 ≤ g i w := WhitneyPoU.distCompl_nonneg
  have hsupp_sub : ∀ w, {i | g i w ≠ 0} ⊆ {i | infDist w (B i) < δ * r i} := by
    intro w i hi
    by_contra h
    exact hi (WhitneyPoU.distCompl_eq_zero h)
  have hgB : ∀ i x, x ∈ B i → 0 < g i x := fun i x hx ↦
    (mul_pos hδ (hW.r_pos i)).trans_le (hW.le_distCompl hA hδ1 hx)
  -- off `closure A`: at most `m` of the `g i` are nonzero, and one of them is positive
  have hgood : ∀ w, 0 < infDist w A → {i | g i w ≠ 0}.encard ≤ m ∧ ∃ i, 0 < g i w := by
    intro w hw
    refine ⟨(Set.encard_le_encard (hsupp_sub w)).trans (hW.mult_le w hw), ?_⟩
    obtain ⟨i, hi⟩ := hW.cover w hw
    exact ⟨i, hgB i w hi⟩
  have hfin : ∀ w, 0 < infDist w A → {i | g i w ≠ 0}.Finite := fun w hw ↦
    Set.finite_of_encard_le_coe (hgood w hw).1
  have hPsi : ∀ w, 0 < infDist w A → 0 < WhitneyPoU.Psi g p w := by
    intro w hw
    obtain ⟨i, hi⟩ := (hgood w hw).2
    exact WhitneyPoU.Psi_pos hg0 hp0 (hfin w hw) hi
  have hBpos : ∀ i z, z ∈ B i → 0 < infDist z A := fun i z hz ↦
    (hW.r_pos i).trans_le (hW.r_le_infDist hz)
  refine ⟨WhitneyPoU.phi g p, fun i z ↦ WhitneyPoU.phi_nonneg hg0 i z, ?_, ?_, ?_, ?_, ?_⟩
  · -- `φ i` vanishes outside `U i`
    intro i z _ h
    by_contra hc
    exact h (WhitneyPoU.phi_eq_zero hp0 (WhitneyPoU.distCompl_eq_zero hc))
  · -- `φ i > 0` on `B i`
    intro i z hz
    exact WhitneyPoU.phi_pos hg0 hp0 (hfin z (hBpos i z hz)) (hgB i z hz)
  · -- local finiteness
    intro z hz
    refine (hfin z hz).subset fun i hi ↦ ?_
    intro h0
    exact hi (WhitneyPoU.phi_eq_zero hp0 h0)
  · -- partition of unity
    intro z hz s hs
    exact WhitneyPoU.sum_phi_eq_one hg0 hp0 (hPsi z hz) hs
  · -- the Lipschitz estimate
    intro z j hz K hK
    have hev : ∀ᶠ w in 𝓝 z, 0 < infDist w A :=
      ((continuous_infDist_pt A).tendsto z).eventually_const_lt (hBpos j z hz)
    exact WhitneyPoU.eventually_sum_abs_phi_sub_le hp (mul_pos hδ (hW.r_pos j)) hg0
      WhitneyPoU.distCompl_le_add (hev.mono hgood) (hW.le_distCompl hA hδ1 hz) hK

end LipschitzExtension

/-! ### Lemma 3.2 with the sum of the pointwise Lipschitz constants

The statement of the paper bounds `∑ i, Lip φ i (z)`: at every `z ∈ B j` there are numbers
`L i ≥ 0` with `LipAt (φ i) z (L i)`, only finitely many of them nonzero, such that
`∑ i, L i ≤ 2 p m^(1/p) / (δ r j)` (`IsWhitneyFamily.exists_partitionOfUnity_lipAt`). The
partition of unity is the one of `IsWhitneyFamily.exists_partitionOfUnity`.
-/

open Set Metric Filter Topology

namespace LipschitzExtension

namespace WhitneyPoU

section Pointwise

variable {Z : Type*} [PseudoMetricSpace Z] {ι : Type*} {g : ι → Z → ℝ} {p : ℝ}

/-- The pointwise Lipschitz constant of a single `φ i` at `z`: if `S` is the set of indices with
`g k z ≠ 0` and `σ = ψ(z) > 0`, then
`Lip φ_i(z) ≤ p g_i(z)^(p-1)/σ + g_i(z)^p/σ² · p ∑_{k ∈ S} g_k(z)^(p-1)`. -/
private theorem lipAt_phi (hp : 1 < p) {m : ℕ} {z : Z}
    (hg0 : ∀ i w, 0 ≤ g i w) (hgLip : ∀ i w w', g i w ≤ g i w' + dist w w')
    (hsupp : ∀ᶠ w in 𝓝 z, {i | g i w ≠ 0}.encard ≤ m)
    {S : Finset ι} (hS : ∀ k, k ∈ S ↔ g k z ≠ 0) (hσ : 0 < Psi g p z) (i : ι) :
    LipAt (phi g p i) z (p * g i z ^ (p - 1) / Psi g p z +
      g i z ^ p / Psi g p z ^ 2 * (p * ∑ k ∈ S, g k z ^ (p - 1))) := by
  classical
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hppos : 0 < p := zero_lt_one.trans hp
  have hp1 : 0 < p - 1 := by linarith
  have hSsupp : {k | g k z ≠ 0} ⊆ ↑S := fun k hk ↦ Finset.mem_coe.mpr ((hS k).mpr hk)
  set σ := Psi g p z with hσdef
  set a := g i z with ha
  have ha0 : 0 ≤ a := hg0 i z
  -- `H d = ∑_{k ∈ S} (g_k(z) + d)^(p-1) + m d^(p-1)`
  set H : ℝ → ℝ := fun d ↦ ∑ k ∈ S, (g k z + d) ^ (p - 1) + m * d ^ (p - 1) with hH
  have hHc : Continuous H := by
    refine (continuous_finsetSum _ fun k _ ↦ ?_).add (continuous_const.mul ?_)
    · exact (continuous_const.add continuous_id).rpow_const fun _ ↦ Or.inr hp1.le
    · exact continuous_id.rpow_const fun _ ↦ Or.inr hp1.le
  have hH0 : H 0 = ∑ k ∈ S, g k z ^ (p - 1) := by
    simp only [hH, add_zero, Real.zero_rpow hp1.ne', mul_zero]
  -- `F d = p (a + d)^(p-1)/σ + (a + d)^p p H(d) / (σ (σ - p d H(d)))`
  set F : ℝ → ℝ := fun d ↦ p * (a + d) ^ (p - 1) / σ +
    (a + d) ^ p * (p * H d) / (σ * (σ - p * d * H d)) with hF
  have hFc : ContinuousAt F 0 := by
    refine ContinuousAt.add ?_ ?_
    · exact ((continuous_const.mul ((continuous_const.add continuous_id).rpow_const
        fun _ ↦ Or.inr hp1.le)).div_const σ).continuousAt
    · refine ContinuousAt.div₀ ?_ ?_ ?_
      · exact (((continuous_const.add continuous_id).rpow_const fun _ ↦ Or.inr hppos.le).mul
          (continuous_const.mul hHc)).continuousAt
      · exact (continuous_const.mul (continuous_const.sub
          ((continuous_const.mul continuous_id).mul hHc))).continuousAt
      · simp only [mul_zero, zero_mul, sub_zero]
        exact (mul_pos hσ hσ).ne'
  have hF0 : F 0 = p * a ^ (p - 1) / σ + a ^ p / σ ^ 2 * (p * ∑ k ∈ S, g k z ^ (p - 1)) := by
    simp only [hF, add_zero, mul_zero, zero_mul, sub_zero, hH0]
    ring
  have hDc : Continuous fun d ↦ σ - p * d * H d :=
    continuous_const.sub ((continuous_const.mul continuous_id).mul hHc)
  intro L' hL'
  have h1 : Tendsto (fun z' ↦ dist z z') (𝓝 z) (𝓝 0) := by
    have := (continuous_const.dist continuous_id : Continuous fun z' : Z ↦ dist z z').tendsto z
    simpa using this
  have ev1 : ∀ᶠ z' in 𝓝 z, F (dist z z') < L' :=
    (hFc.tendsto.comp h1).eventually_lt_const (by rwa [hF0])
  have ev2 : ∀ᶠ z' in 𝓝 z, 0 < σ - p * dist z z' * H (dist z z') := by
    have := (hDc.tendsto 0).comp h1
    simp only [mul_zero, zero_mul, sub_zero] at this
    exact this.eventually_const_lt hσ
  filter_upwards [hsupp, ev1, ev2] with z' hmz' hFz' hDz'
  obtain ⟨S', hS', hS'card⟩ := exists_finset_of_encard_le hmz'
  set T : Finset ι := S ∪ S'
  have hST : {k | g k z ≠ 0} ⊆ ↑T :=
    hSsupp.trans (Finset.coe_subset.mpr Finset.subset_union_left)
  have hS'T : {k | g k z' ≠ 0} ⊆ ↑T := fun k hk ↦
    Finset.mem_coe.mpr (Finset.mem_union_right _ ((hS' k).mpr hk))
  have hσT : σ = ∑ k ∈ T, g k z ^ p := Psi_eq_sum hp0 hST
  have hσ'T : Psi g p z' = ∑ k ∈ T, g k z' ^ p := Psi_eq_sum hp0 hS'T
  set σ' := Psi g p z' with hσ'def
  set d := dist z z'
  have hd : 0 ≤ d := dist_nonneg
  -- `|g_k(z) - g_k(z')| ≤ d`
  have hlip : ∀ k, |g k z - g k z'| ≤ d := by
    intro k
    rw [abs_le]
    constructor
    · have := hgLip k z' z
      rw [dist_comm] at this
      linarith
    · have := hgLip k z z'
      linarith
  -- `|σ - σ'| ≤ p d H(d)`
  have step3 : ∑ k ∈ T, |g k z ^ p - g k z' ^ p| ≤
      p * d * ∑ k ∈ T, (g k z + d) ^ (p - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    calc |g k z ^ p - g k z' ^ p| ≤ p * (g k z + d) ^ (p - 1) * d :=
          abs_rpow_sub_rpow_le (hg0 k z) (hg0 k z') (hlip k) hp.le
      _ = p * d * (g k z + d) ^ (p - 1) := by ring
  have step4 : ∑ k ∈ T, (g k z + d) ^ (p - 1) ≤ H d := by
    have hsub : S ⊆ T := Finset.subset_union_left
    rw [← Finset.sum_sdiff hsub]
    have h1 : ∀ k ∈ T \ S, (g k z + d) ^ (p - 1) = d ^ (p - 1) := by
      intro k hk
      have : g k z = 0 := by
        by_contra h
        exact (Finset.mem_sdiff.mp hk).2 ((hS k).mpr h)
      rw [this, zero_add]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((T \ S).card : ℝ) ≤ m := by
      have h2 : T \ S ⊆ S' := by
        intro k hk
        rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hk).1 with h | h
        · exact absurd h (Finset.mem_sdiff.mp hk).2
        · exact h
      exact_mod_cast (Finset.card_le_card h2).trans hS'card
    have hdp : 0 ≤ d ^ (p - 1) := Real.rpow_nonneg hd _
    simp only [hH]
    linarith [mul_le_mul_of_nonneg_right hcard hdp]
  have hdiff : |σ - σ'| ≤ p * d * H d := by
    calc |σ - σ'| = |∑ k ∈ T, (g k z ^ p - g k z' ^ p)| := by
          rw [hσT, hσ'T, Finset.sum_sub_distrib]
      _ ≤ ∑ k ∈ T, |g k z ^ p - g k z' ^ p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ p * d * ∑ k ∈ T, (g k z + d) ^ (p - 1) := step3
      _ ≤ p * d * H d := mul_le_mul_of_nonneg_left step4 (mul_nonneg hppos.le hd)
  have hσ'lb : σ - p * d * H d ≤ σ' := by
    have := le_abs_self (σ - σ')
    linarith
  have hσ'pos : 0 < σ' := hDz'.trans_le hσ'lb
  -- the estimates for `ψ_i = g_i ^ p`
  have hψ : |a ^ p - g i z' ^ p| ≤ p * (a + d) ^ (p - 1) * d :=
    abs_rpow_sub_rpow_le ha0 (hg0 i z') (hlip i) hp.le
  have hψ' : g i z' ^ p ≤ (a + d) ^ p := by
    apply Real.rpow_le_rpow (hg0 i z') _ hppos.le
    have := hgLip i z' z
    rw [dist_comm] at this
    linarith
  have hψ'0 : 0 ≤ g i z' ^ p := Real.rpow_nonneg (hg0 i z') p
  have hpdH : 0 ≤ p * d * H d := (abs_nonneg _).trans hdiff
  -- the main computation
  rw [Real.dist_eq]
  simp only [phi]
  rw [← hσdef, ← ha, ← hσ'def]
  have e : a ^ p / σ - g i z' ^ p / σ' =
      (a ^ p - g i z' ^ p) / σ + g i z' ^ p * ((σ' - σ) / (σ * σ')) := by
    field_simp
    ring
  have hdiff' : |σ' - σ| ≤ p * d * H d := (abs_sub_comm σ' σ).le.trans hdiff
  rw [e]
  calc |(a ^ p - g i z' ^ p) / σ + g i z' ^ p * ((σ' - σ) / (σ * σ'))|
      ≤ |a ^ p - g i z' ^ p| / σ + g i z' ^ p * (|σ' - σ| / (σ * σ')) := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_div, abs_of_pos hσ, abs_mul, abs_of_nonneg hψ'0, abs_div,
          abs_of_pos (mul_pos hσ hσ'pos)]
    _ ≤ p * (a + d) ^ (p - 1) * d / σ +
          (a + d) ^ p * (p * d * H d / (σ * (σ - p * d * H d))) := by
        refine add_le_add (div_le_div_of_nonneg_right hψ hσ.le) ?_
        refine mul_le_mul hψ' ?_ (by positivity) (Real.rpow_nonneg (by linarith) _)
        exact div_le_div₀ hpdH hdiff' (mul_pos hσ hDz')
          (mul_le_mul_of_nonneg_left hσ'lb hσ.le)
    _ = F d * d := by
        simp only [hF]
        field_simp
    _ ≤ L' * d := mul_le_mul_of_nonneg_right hFz'.le hd

/-- The abstract form of Lemma 3.2 for the sum of the pointwise Lipschitz constants: if near `z`
at most `m` of the (nonnegative, `1`-Lipschitz) `g i` are nonzero and `0 < c ≤ g j z` for some
`j`, then there are bounds `L i ≥ Lip φ_i(z)` (`LipAt (phi g p i) z (L i)`), vanishing outside a
finite set `s`, with `∑_{i ∈ s} L i ≤ 2 p m^(1/p) / c`. -/
theorem exists_lipAt_phi (hp : 1 < p) {m : ℕ} {z : Z} {c : ℝ} (hc : 0 < c)
    (hg0 : ∀ i w, 0 ≤ g i w) (hgLip : ∀ i w w', g i w ≤ g i w' + dist w w')
    (hsupp : ∀ᶠ w in 𝓝 z, {i | g i w ≠ 0}.encard ≤ m) {j : ι} (hj : c ≤ g j z) :
    ∃ (L : ι → ℝ) (s : Finset ι), (∀ i, 0 ≤ L i) ∧ (∀ i ∉ s, L i = 0) ∧
      (∀ i, LipAt (phi g p i) z (L i)) ∧ ∑ i ∈ s, L i ≤ 2 * p * (m : ℝ) ^ (1 / p) / c := by
  classical
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hppos : 0 < p := zero_lt_one.trans hp
  have hp1 : 0 < p - 1 := by linarith
  have hmz := hsupp.self_of_nhds
  have hfinz : {i | g i z ≠ 0}.Finite := Set.finite_of_encard_le_coe hmz
  -- `S`: the (at most `m`) indices with `g i z ≠ 0`
  obtain ⟨S, hS, hScard⟩ := exists_finset_of_encard_le hmz
  have hSsupp : {i | g i z ≠ 0} ⊆ ↑S := fun i hi ↦ Finset.mem_coe.mpr ((hS i).mpr hi)
  have hσpos : 0 < Psi g p z := Psi_pos hg0 hp0 hfinz (hc.trans_le hj)
  have hcσ : c ^ p ≤ Psi g p z :=
    (Real.rpow_le_rpow hc.le hj (by linarith)).trans (le_Psi hg0 hp0 hfinz j)
  have hσS : Psi g p z = ∑ i ∈ S, g i z ^ p := Psi_eq_sum hp0 hSsupp
  refine ⟨fun i ↦ p * g i z ^ (p - 1) / Psi g p z +
      g i z ^ p / Psi g p z ^ 2 * (p * ∑ k ∈ S, g k z ^ (p - 1)), S, fun i ↦ ?_, fun i hi ↦ ?_,
    fun i ↦ lipAt_phi hp hg0 hgLip hsupp hS hσpos i, ?_⟩
  · -- nonnegativity
    have h1 := Real.rpow_nonneg (hg0 i z) (p - 1)
    have h2 := Real.rpow_nonneg (hg0 i z) p
    have h3 : 0 ≤ ∑ k ∈ S, g k z ^ (p - 1) :=
      Finset.sum_nonneg fun k _ ↦ Real.rpow_nonneg (hg0 k z) _
    positivity
  · -- the bounds vanish outside `S`
    have h0 : g i z = 0 := by
      by_contra h
      exact hi ((hS i).mpr h)
    simp only [h0, Real.zero_rpow hp1.ne', Real.zero_rpow hp0, mul_zero, zero_div, zero_mul,
      zero_add]
  · -- `∑_{i ∈ S} L i = (2 / σ) p ∑_{i ∈ S} g_i(z)^(p-1)`, then Hölder's inequality
    set σ := Psi g p z
    have hsum : ∑ i ∈ S, (p * g i z ^ (p - 1) / σ +
        g i z ^ p / σ ^ 2 * (p * ∑ k ∈ S, g k z ^ (p - 1))) =
        2 / σ * p * ∑ i ∈ S, g i z ^ (p - 1) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul,
        ← Finset.sum_div, ← hσS]
      field_simp
      ring
    rw [hsum]
    have hH := sum_rpow_sub_one_le S (x := fun i ↦ g i z) (fun i _ ↦ hg0 i z) hp
    rw [← hσS] at hH
    have hcle : c ≤ σ ^ (1 / p) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hc.le p) hcσ (by positivity : (0:ℝ) ≤ 1 / p)
      rwa [one_div, Real.rpow_rpow_inv hc.le hp0, ← one_div] at this
    have hprod : σ ^ (1 / p) * σ ^ ((p - 1) / p) = σ := by
      rw [← Real.rpow_add hσpos]
      have : 1 / p + (p - 1) / p = 1 := by field_simp; ring
      rw [this, Real.rpow_one]
    have hkey : c * σ ^ ((p - 1) / p) ≤ σ := by
      calc c * σ ^ ((p - 1) / p) ≤ σ ^ (1 / p) * σ ^ ((p - 1) / p) :=
            mul_le_mul_of_nonneg_right hcle (Real.rpow_nonneg hσpos.le _)
        _ = σ := hprod
    have hm : (S.card : ℝ) ^ (1 / p) ≤ (m : ℝ) ^ (1 / p) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hScard) (by positivity)
    have hmp : 0 ≤ (m : ℝ) ^ (1 / p) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h2σp : 0 ≤ 2 / σ * p := mul_nonneg (div_nonneg zero_le_two hσpos.le) hppos.le
    rw [le_div_iff₀ hc]
    calc 2 / σ * p * (∑ i ∈ S, g i z ^ (p - 1)) * c
        ≤ 2 / σ * p * ((m : ℝ) ^ (1 / p) * σ ^ ((p - 1) / p)) * c := by
          apply mul_le_mul_of_nonneg_right _ hc.le
          apply mul_le_mul_of_nonneg_left _ h2σp
          exact hH.trans (mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hσpos.le _))
      _ = 2 * p * (m : ℝ) ^ (1 / p) * (c * σ ^ ((p - 1) / p)) / σ := by
          ring
      _ ≤ 2 * p * (m : ℝ) ^ (1 / p) * σ / σ := by
          apply div_le_div_of_nonneg_right _ hσpos.le
          exact mul_le_mul_of_nonneg_left hkey (mul_nonneg (by linarith) hmp)
      _ = 2 * p * (m : ℝ) ^ (1 / p) := mul_div_cancel_right₀ _ hσpos.ne'

end Pointwise

end WhitneyPoU

/-- `e < 3` (via `e^(1/6) ≤ 6/5`, from `1 - 1/6 ≤ e^(-1/6)`). -/
private lemma exp_one_lt_three_aux : Real.exp 1 < 3 := by
  have h1 : (5 / 6 : ℝ) ≤ Real.exp (-(1 / 6)) := by
    have := Real.add_one_le_exp (-(1 / 6))
    linarith
  have h2 : Real.exp (1 / 6) * Real.exp (-(1 / 6)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h3 : Real.exp (1 / 6) ≤ 6 / 5 := by
    nlinarith [Real.exp_pos (1 / 6)]
  have h4 : Real.exp 1 = Real.exp (1 / 6) ^ 6 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h4]
  calc Real.exp (1 / 6) ^ 6 ≤ (6 / 5) ^ 6 := pow_le_pow_left₀ (Real.exp_pos _).le h3 6
    _ < 3 := by norm_num

variable {Z : Type*} [MetricSpace Z] {ι : Type*} {A : Set Z} {B : ι → Set Z} {r : ι → ℝ}
  {m : ℕ} {α δ γ : ℝ}

/-- **Lemma 3.2** of [Basso2024] (general form, with the sum of the pointwise Lipschitz constants
of the `φ i`): for a Whitney family with multiplicity `m`, `0 < δ < 1` and `p > 1`, there is a
partition of unity as in `IsWhitneyFamily.exists_partitionOfUnity` (given by the same
construction) such that `∑ i, Lip φ_i(z) ≤ 2 p m^(1/p) / (δ r j)` at every `z ∈ B j`. -/
theorem IsWhitneyFamily.exists_partitionOfUnity_lipAt (hW : IsWhitneyFamily A B r m α δ γ)
    (hA : A.Nonempty) (hδ : 0 < δ) (hδ1 : δ < 1) {p : ℝ} (hp : 1 < p) :
    ∃ φ : ι → Z → ℝ,
      (∀ i z, 0 ≤ φ i z) ∧
      (∀ i z, 0 < infDist z A → φ i z ≠ 0 → infDist z (B i) < δ * r i) ∧
      (∀ i z, z ∈ B i → 0 < φ i z) ∧
      (∀ z, 0 < infDist z A → {i | φ i z ≠ 0}.Finite) ∧
      (∀ z, 0 < infDist z A → ∀ s : Finset ι, {i | φ i z ≠ 0} ⊆ ↑s → ∑ i ∈ s, φ i z = 1) ∧
      (∀ z j, z ∈ B j → ∃ (L : ι → ℝ) (s : Finset ι), (∀ i, 0 ≤ L i) ∧ (∀ i ∉ s, L i = 0) ∧
        (∀ i, LipAt (φ i) z (L i)) ∧ ∑ i ∈ s, L i ≤ 2 * p * (m : ℝ) ^ (1 / p) / (δ * r j)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  -- `g i = d(·, (U i)ᶜ)`, `ψ i = g i ^ p`, `φ i = ψ i / ∑ᶠ k, ψ k`
  set g := WhitneyPoU.distCompl B r δ
  have hg0 : ∀ i w, 0 ≤ g i w := WhitneyPoU.distCompl_nonneg
  have hsupp_sub : ∀ w, {i | g i w ≠ 0} ⊆ {i | infDist w (B i) < δ * r i} := by
    intro w i hi
    by_contra h
    exact hi (WhitneyPoU.distCompl_eq_zero h)
  have hgB : ∀ i x, x ∈ B i → 0 < g i x := fun i x hx ↦
    (mul_pos hδ (hW.r_pos i)).trans_le (hW.le_distCompl hA hδ1 hx)
  -- off `closure A`: at most `m` of the `g i` are nonzero, and one of them is positive
  have hgood : ∀ w, 0 < infDist w A → {i | g i w ≠ 0}.encard ≤ m ∧ ∃ i, 0 < g i w := by
    intro w hw
    refine ⟨(Set.encard_le_encard (hsupp_sub w)).trans (hW.mult_le w hw), ?_⟩
    obtain ⟨i, hi⟩ := hW.cover w hw
    exact ⟨i, hgB i w hi⟩
  have hfin : ∀ w, 0 < infDist w A → {i | g i w ≠ 0}.Finite := fun w hw ↦
    Set.finite_of_encard_le_coe (hgood w hw).1
  have hPsi : ∀ w, 0 < infDist w A → 0 < WhitneyPoU.Psi g p w := by
    intro w hw
    obtain ⟨i, hi⟩ := (hgood w hw).2
    exact WhitneyPoU.Psi_pos hg0 hp0 (hfin w hw) hi
  have hBpos : ∀ i z, z ∈ B i → 0 < infDist z A := fun i z hz ↦
    (hW.r_pos i).trans_le (hW.r_le_infDist hz)
  refine ⟨WhitneyPoU.phi g p, fun i z ↦ WhitneyPoU.phi_nonneg hg0 i z, ?_, ?_, ?_, ?_, ?_⟩
  · -- `φ i` vanishes outside `U i`
    intro i z _ h
    by_contra hc
    exact h (WhitneyPoU.phi_eq_zero hp0 (WhitneyPoU.distCompl_eq_zero hc))
  · -- `φ i > 0` on `B i`
    intro i z hz
    exact WhitneyPoU.phi_pos hg0 hp0 (hfin z (hBpos i z hz)) (hgB i z hz)
  · -- local finiteness
    intro z hz
    refine (hfin z hz).subset fun i hi ↦ ?_
    intro h0
    exact hi (WhitneyPoU.phi_eq_zero hp0 h0)
  · -- partition of unity
    intro z hz s hs
    exact WhitneyPoU.sum_phi_eq_one hg0 hp0 (hPsi z hz) hs
  · -- the pointwise Lipschitz constants
    intro z j hz
    have hev : ∀ᶠ w in 𝓝 z, 0 < infDist w A :=
      ((continuous_infDist_pt A).tendsto z).eventually_const_lt (hBpos j z hz)
    exact WhitneyPoU.exists_lipAt_phi hp (mul_pos hδ (hW.r_pos j)) hg0
      WhitneyPoU.distCompl_le_add (hev.mono fun w hw ↦ (hgood w hw).1)
      (hW.le_distCompl hA hδ1 hz)

/-- **Lemma 3.2** of [Basso2024] as in the paper, with the constant `2e` of errata item 2
(`2e ≤ 6`): for a Whitney family with multiplicity `m ≥ 3` (in the paper `m = 3(n + 1)`) and
`0 < δ < 1`, there is a partition of unity subordinate to the sets `U i = N_{δ r i}(B i)` with
`∑ i, Lip φ_i(z) ≤ 2e log m / (δ r j)` at every `z ∈ B j`. This is the case `p = log m` of
`IsWhitneyFamily.exists_partitionOfUnity_lipAt`, for which `m^(1/p) = e`. -/
theorem IsWhitneyFamily.exists_partitionOfUnity_log (hW : IsWhitneyFamily A B r m α δ γ)
    (hm : 3 ≤ m) (hA : A.Nonempty) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ φ : ι → Z → ℝ,
      (∀ i z, 0 ≤ φ i z) ∧
      (∀ i z, 0 < infDist z A → φ i z ≠ 0 → infDist z (B i) < δ * r i) ∧
      (∀ z, 0 < infDist z A → ∀ s : Finset ι, {i | φ i z ≠ 0} ⊆ ↑s → ∑ i ∈ s, φ i z = 1) ∧
      (∀ z j, z ∈ B j → ∃ (L : ι → ℝ) (s : Finset ι), (∀ i, 0 ≤ L i) ∧ (∀ i ∉ s, L i = 0) ∧
        (∀ i, LipAt (φ i) z (L i)) ∧
          ∑ i ∈ s, L i ≤ 2 * Real.exp 1 * Real.log m / (δ * r j)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlog : 1 < Real.log m := by
    rw [Real.lt_log_iff_exp_lt hm0]
    have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    exact exp_one_lt_three_aux.trans_le h3
  obtain ⟨φ, h1, h2, -, -, h5, h6⟩ := hW.exists_partitionOfUnity_lipAt hA hδ hδ1 hlog
  refine ⟨φ, h1, h2, h5, fun z j hz ↦ ?_⟩
  obtain ⟨L, s, hL0, hLs, hLip, hsum⟩ := h6 z j hz
  refine ⟨L, s, hL0, hLs, hLip, hsum.trans (le_of_eq ?_)⟩
  -- `m ^ (1 / log m) = e`
  have he : (m : ℝ) ^ (1 / Real.log m) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hm0, mul_one_div_cancel (zero_lt_one.trans hlog).ne']
  rw [he]
  ring

end LipschitzExtension
