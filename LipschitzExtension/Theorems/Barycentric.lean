/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.WhitneyCovering.Nagata
import LipschitzExtension.Topology.MetricSpace.WhitneyCovering.PartitionOfUnity
import LipschitzExtension.Topology.MetricSpace.Barycenter.Defs
import LipschitzExtension.Topology.MetricSpace.PointwiseLipschitz.Basic
import LipschitzExtension.Topology.MetricSpace.LocalExtension
import LipschitzExtension.Topology.MetricSpace.Barycenter.Construction
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import LipschitzExtension.Geometry.CAT0.GNPC

/-!
# The Lang–Schlichenmaier theorem for barycentric targets

This file proves Theorem 1.2 of [Basso2024] (which holds as stated by item 2 of the errata
[BassoClaude2026]): let `X` be a metric space and `A ⊆ X` a subset satisfying `Nagata(n, c)`, and
let `Y` be a complete metric space of generalized non-positive curvature. Then every `1`-Lipschitz
map `f : A → Y` admits a `1000 (c + 1) log₂(n + 2)`-Lipschitz extension `F : X → Y` (the bound
(1.4)).

By Theorem 2.4 of [Basso2024] (Es-Sahib–Heinich, Navas, Descombes), complete gNPC spaces are
exactly the complete metric spaces admitting a barycenter map, and the proof only uses a
barycenter map on finitely supported probability measures. We therefore prove the theorem for
targets with a `BarycenterMap`; this covers real Banach spaces (`BarycenterMap.ofNormedSpace`)
and complete CAT(0) spaces.

## Main statements

* `LipschitzOnWith.extend_nagata_isGNPC`: Theorem 1.2 for complete gNPC targets.
* `LipschitzOnWith.extend_nagata_barycenterMap`: the same for complete targets with a barycenter
  map.
* `LipschitzOnWith.extend_nagata_barycenterMap_of_isClosed`: the same for closed `A`, without
  completeness of `Y`.
* `LipschitzOnWith.extend_nagata_normedSpace`, `LipschitzOnWith.extend_nagata_isCAT0`: real
  Banach spaces and complete CAT(0) spaces as targets.
* `exists_lipAt_extension_of_nagata`: the construction of Section 3 of [Basso2024], an extension
  which is pointwise `1000 (c + 1) log₂(n + 2)`-Lipschitz off `A`.

## Implementation notes

* The extension is constructed on an isometric copy of `X` in a normed space, where it is
  pointwise Lipschitz off `A` (`localExtensionProperty_of_nagata`); the reduction of item 5 of
  the errata (`exists_lipschitz_extension_of_local_of_completeSpace`, and
  `exists_lipschitz_extension_of_local` for closed `A`) then gives the global bound.
* For gNPC targets we use `IsGNPC.nonempty_barycenterMap`: every complete gNPC space admits a
  barycenter map on finitely supported measures (see
  `isGNPC_iff_nonempty_contractingBarycenterMap` for Theorem 2.4 itself).
* In Definition 1.1 the constant `c` is positive; here no assumption on `c` is needed, since
  `Nagata(n, c)` for a nonempty set forces `c ≥ 0` (`Nagata.nonneg`).

## Proof outline

Let `A ⊆ Z` be nonempty and satisfy `Nagata(n, c)`, let `Y` admit a barycenter map `β` and let `f`
be `1`-Lipschitz on `A`. Take the Whitney family of Proposition 3.1 with `ρ = 5/4`
(`α = 3 + 29c/9`, `δ = 1/25`, `γ = 3/2`, multiplicity `m = 3(n+1)`,
`Nagata.exists_isWhitneyFamily'`), the partition of unity of Lemma 3.2 with `p = log(3(n+1))`
(so `m^(1/p) = e`), and points `a_i ∈ A` with `d(a_i, B_i) ≤ (1 + ε₀) r_i`, `ε₀ = 1/100` (using
`IsWhitneyFamily.exists_infDist_lt`). Define `F(z) = β(∑_i φ_i(z) δ_{f(a_i)})` if `0 < d(z, A)`
and `F(z) = f(z)` otherwise.

* For `φ_i(z) ≠ 0` (i.e. `z ∈ N_{δ r_i}(B_i)`): `d(a_i, z) ≤ (1 + ε₀ + α + δ) r_i` and
  `(1 - δ) r_i ≤ d(z, A)` (`IsWhitneyFamily.one_sub_mul_le_infDist`).
* Continuity at `A`: `d(F z, f a) ≤ W₁(∑ φ_i(z) δ_{f a_i}, δ_{f a}) ≤ ∑ φ_i(z) d(a_i, a)
  ≤ ((1 + ε₀ + α + δ)/(1 - δ) + 1) d(z, a)` (`FinProb.W1_ofWeights_dirac_le`).
* Pointwise Lipschitz bound at `z` with `0 < d(z, A)`, `z ∈ B_j`: for `z'` near `z`, write both
  measures over the common finite set `S = supp φ(z) ∪ supp φ(z')`; by Lemma 2.5
  (`FinProb.W1_ofWeights_le`) `d(F z, F z') ≤ (D/2) ∑_{i∈S} |φ_i(z) - φ_i(z')|` with
  `D = max_{i,i' ∈ S} d(a_i, a_i') ≤ 2 (1 + ε₀ + α + δ) (γ r_j + d(z,z'))/(1 - δ)`
  (use `d(z, A) ≤ γ r_j` and `(1-δ) r_i ≤ d(z', A) ≤ d(z, A) + d(z, z')`).
  With Lemma 3.2 this gives `Lip F(z) ≤ 2e log(3(n+1)) (1 + ε₀ + α + δ) γ / (δ (1 - δ))`, which is
  at most `1000 (c + 1) log₂(n + 2)` by an elementary numerical estimate.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
* U. Lang and T. Schlichenmaier, *Nagata dimension, quasisymmetric embeddings, and Lipschitz
  extensions*, Int. Math. Res. Not. 2005, no. 58, 3625–3655
-/

open Set Metric Filter Topology

namespace LipschitzExtension

/-! ### Auxiliary bounds on logarithms -/

/-- `log 3 ≤ (8/5) log 2`, from `3^5 = 243 ≤ 256 = 2^8`. -/
private lemma log_three_le : Real.log 3 ≤ 8 / 5 * Real.log 2 := by
  have h : Real.log ((3 : ℝ) ^ 5) ≤ Real.log ((2 : ℝ) ^ 8) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- `(19/12) log 2 ≤ log 3`, from `2^19 = 524288 ≤ 531441 = 3^12`. -/
private lemma log_three_ge : 19 / 12 * Real.log 2 ≤ Real.log 3 := by
  have h : Real.log ((2 : ℝ) ^ 19) ≤ Real.log ((3 : ℝ) ^ 12) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- `(9/4) log 2 ≤ log 5`, from `2^9 = 512 ≤ 625 = 5^4`. -/
private lemma log_five_ge : 9 / 4 * Real.log 2 ≤ Real.log 5 := by
  have h : Real.log ((2 : ℝ) ^ 9) ≤ Real.log ((5 : ℝ) ^ 4) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- `log(3(n+1)) ≤ (23/20) log₂(n + 2)` (used at the end of the proof of Theorem 1.2). -/
private theorem log_three_mul_le_logb (n : ℕ) :
    Real.log (3 * (n + 1)) ≤ 23 / 20 * Real.logb 2 (n + 2) := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl3 := log_three_le
  have hl3' := log_three_ge
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : Real.log 2 ≠ 0 := ha.ne'
  rw [Real.logb, mul_div_assoc', le_div_iff₀ ha]
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rcases (show n ≤ 3 ∨ 4 ≤ n by omega) with hn | hn
  · obtain rfl | rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    · -- `log 3 ≤ 23/20`
      norm_num
      nlinarith [mul_nonneg
        (show (0 : ℝ) ≤ 23 / 20 - Real.log 3 by norm_num at hl2; linarith) ha.le]
    · -- `log 6 · log 2 ≤ (23/20) log 3`
      norm_num
      rw [hlog6]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ Real.log 3 - 19 / 12 * Real.log 2 by linarith)
          (show (0 : ℝ) ≤ 23 / 20 - Real.log 2 by norm_num at hl2; linarith),
        mul_nonneg ha.le (show (0 : ℝ) ≤ 0.6931471808 - Real.log 2 by linarith)]
    · -- `log 9 · log 2 ≤ (23/20) log 4`
      norm_num
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow,
        Real.log_pow]
      push_cast
      nlinarith [mul_nonneg
        (show (0 : ℝ) ≤ 23 / 20 - Real.log 3 by norm_num at hl2; linarith) ha.le]
    · -- `log 12 · log 2 ≤ (23/20) log 5`
      norm_num
      have h5 := log_five_ge
      rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 8 / 5 * Real.log 2 - Real.log 3 by linarith) ha.le,
        mul_nonneg ha.le (show (0 : ℝ) ≤ 0.6931471808 - Real.log 2 by linarith)]
  · -- `n ≥ 4`: `log(3(n+1)) ≤ log 3 + log(n+2)` and `log(n+2) ≥ log 6`
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have h6 : Real.log 6 ≤ Real.log (n + 2) := Real.log_le_log (by norm_num) (by linarith)
    have hsplit : Real.log (3 * (n + 1)) ≤ Real.log 3 + Real.log (n + 2) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hsplit ha.le,
      mul_nonneg (show (0 : ℝ) ≤ Real.log (n + 2) - Real.log 2 - Real.log 3 by linarith)
        (show (0 : ℝ) ≤ 23 / 20 - Real.log 2 by norm_num at hl2; linarith),
      mul_nonneg (show (0 : ℝ) ≤ 8 / 5 * Real.log 2 - Real.log 3 by linarith)
        (show (0 : ℝ) ≤ 2 * Real.log 2 - 23 / 20 by norm_num at hl2'; linarith),
      mul_nonneg ha.le (show (0 : ℝ) ≤ 0.6931471808 - Real.log 2 by linarith)]

/-- Final estimate in the proof of Theorem 1.2 (errata, item 2), with `ε₀ = 1/100`. -/
private theorem langSchlichenmaier_numeric (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    2 * Real.exp 1 * Real.log (3 * (n + 1)) *
        ((1 + 1 / 100 + (3 + 29 / 9 * c) + 1 / 25) * (3 / 2) / (1 / 25 * (1 - 1 / 25))) ≤
      1000 * (c + 1) * Real.logb 2 (n + 2) := by
  have h := log_three_mul_le_logb n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlb : 0 ≤ Real.logb 2 ((n : ℝ) + 2) := Real.logb_nonneg (by norm_num) (by linarith)
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  -- the constant is `(81/20 + 29c/9) · 625/16`
  have hK : (1 + 1 / 100 + (3 + 29 / 9 * c) + 1 / 25) * (3 / 2) / (1 / 25 * (1 - 1 / 25)) =
      (81 / 20 + 29 / 9 * c) * (625 / 16) := by ring
  rw [hK]
  have hK0 : 0 ≤ 2 * Real.exp 1 * ((81 / 20 + 29 / 9 * c) * (625 / 16)) := by positivity
  have hconst : 2 * Real.exp 1 * ((81 / 20 + 29 / 9 * c) * (625 / 16)) * (23 / 20) ≤
      1000 * (c + 1) := by
    nlinarith [mul_nonneg hc (show (0 : ℝ) ≤ 2.7182818286 - Real.exp 1 by linarith)]
  calc 2 * Real.exp 1 * Real.log (3 * (n + 1)) * ((81 / 20 + 29 / 9 * c) * (625 / 16))
      = 2 * Real.exp 1 * ((81 / 20 + 29 / 9 * c) * (625 / 16)) * Real.log (3 * (n + 1)) := by
        ring
    _ ≤ 2 * Real.exp 1 * ((81 / 20 + 29 / 9 * c) * (625 / 16)) *
        (23 / 20 * Real.logb 2 (n + 2)) := mul_le_mul_of_nonneg_left h hK0
    _ = 2 * Real.exp 1 * ((81 / 20 + 29 / 9 * c) * (625 / 16)) * (23 / 20) *
        Real.logb 2 (n + 2) := by ring
    _ ≤ 1000 * (c + 1) * Real.logb 2 (n + 2) := mul_le_mul_of_nonneg_right hconst hlb


universe u v

/-! ### Auxiliary lemma on `FinProb.ofWeights` -/

namespace FinProb

variable {Y : Type*}

/-- Two finitely supported probability measures with the same weights are equal. -/
private theorem eq_of_w_eq {μ ν : FinProb Y} (h : μ.w = ν.w) : μ = ν := by
  cases μ; cases ν; cases h; rfl

/-- Adding indices of weight zero does not change `ofWeights`. -/
private theorem ofWeights_eq_of_subset {ι : Type*} {s s' : Finset ι} (y : ι → Y) {α : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ α i) (h1 : ∑ i ∈ s, α i = 1) (h0' : ∀ i ∈ s', 0 ≤ α i)
    (h1' : ∑ i ∈ s', α i = 1) (hss' : s ⊆ s') (hz : ∀ i ∈ s', i ∉ s → α i = 0) :
    ofWeights s y α h0 h1 = ofWeights s' y α h0' h1' := by
  apply eq_of_w_eq
  change ∑ i ∈ s, α i • Finsupp.single (y i) (1 : ℝ) =
    ∑ i ∈ s', α i • Finsupp.single (y i) (1 : ℝ)
  exact Finset.sum_subset hss' fun i hi his ↦ by rw [hz i hi his, zero_smul]

end FinProb

/-! ### The barycentric extension attached to a partition of unity -/

section BaryExt

variable {Z : Type*} [PseudoMetricSpace Z] {Y : Type*} [PseudoMetricSpace Y] {ι : Type*}

/-- `z ↦ β(∑ φ i z δ_{y i})` if `0 < d(z, A)`, and `f z` otherwise. -/
private noncomputable def baryExt (β : BarycenterMap Y) (A : Set Z) (f : Z → Y) (y : ι → Y)
    (φ : ι → Z → ℝ) (hφ0 : ∀ i z, 0 ≤ φ i z)
    (hfin : ∀ z, 0 < infDist z A → {i | φ i z ≠ 0}.Finite)
    (hsum : ∀ z, 0 < infDist z A → ∀ s : Finset ι, {i | φ i z ≠ 0} ⊆ ↑s → ∑ i ∈ s, φ i z = 1)
    (z : Z) : Y :=
  if h : 0 < infDist z A then
    β.bary (FinProb.ofWeights (hfin z h).toFinset y (fun i ↦ φ i z) (fun i _ ↦ hφ0 i z)
      (hsum z h _ (hfin z h).coe_toFinset.symm.subset))
  else f z

variable {β : BarycenterMap Y} {A : Set Z} {f : Z → Y} {y : ι → Y} {φ : ι → Z → ℝ}
  {hφ0 : ∀ i z, 0 ≤ φ i z} {hfin : ∀ z, 0 < infDist z A → {i | φ i z ≠ 0}.Finite}
  {hsum : ∀ z, 0 < infDist z A → ∀ s : Finset ι, {i | φ i z ≠ 0} ⊆ ↑s → ∑ i ∈ s, φ i z = 1}

private theorem baryExt_of_not_pos {z : Z} (hz : ¬ 0 < infDist z A) :
    baryExt β A f y φ hφ0 hfin hsum z = f z := by
  rw [baryExt, dite_eq_right hz]

/-- The measure defining the extension may be written over any finite set containing the
support of `φ · z`. -/
private theorem baryExt_eq {z : Z} (hz : 0 < infDist z A) (s : Finset ι)
    (hs : {i | φ i z ≠ 0} ⊆ ↑s) :
    baryExt β A f y φ hφ0 hfin hsum z =
      β.bary (FinProb.ofWeights s y (fun i ↦ φ i z) (fun i _ ↦ hφ0 i z) (hsum z hz s hs)) := by
  rw [baryExt, dite_eq_left hz]
  congr 1
  apply FinProb.ofWeights_eq_of_subset
  · intro i hi
    rw [Set.Finite.mem_toFinset] at hi
    exact Finset.mem_coe.mp (hs hi)
  · intro i _ hi
    rw [Set.Finite.mem_toFinset] at hi
    simpa using hi

/-- Lemma 2.5 applied to the extension. -/
private theorem dist_baryExt_le {z z' : Z} (hz : 0 < infDist z A) (hz' : 0 < infDist z' A)
    (s : Finset ι) (hs : {i | φ i z ≠ 0} ⊆ ↑s) (hs' : {i | φ i z' ≠ 0} ⊆ ↑s) {D : ℝ}
    (hD : ∀ i ∈ s, ∀ k ∈ s, dist (y i) (y k) ≤ D) :
    dist (baryExt β A f y φ hφ0 hfin hsum z) (baryExt β A f y φ hφ0 hfin hsum z') ≤
      D / 2 * ∑ i ∈ s, |φ i z - φ i z'| := by
  rw [baryExt_eq hz s hs, baryExt_eq hz' s hs']
  exact (β.dist_le_W1 _ _).trans (FinProb.W1_ofWeights_le s y _ _ _ _ hD)

/-- Comparison of the extension with a point: `d(F z, y₀) ≤ ∑ φ i z d(y i, y₀)`. -/
private theorem dist_baryExt_le_sum {z : Z} (hz : 0 < infDist z A) (s : Finset ι)
    (hs : {i | φ i z ≠ 0} ⊆ ↑s) (y₀ : Y) :
    dist (baryExt β A f y φ hφ0 hfin hsum z) y₀ ≤ ∑ i ∈ s, φ i z * dist (y i) y₀ := by
  rw [baryExt_eq hz s hs]
  calc dist (β.bary _) y₀ = dist (β.bary _) (β.bary (FinProb.dirac y₀)) := by rw [β.bary_dirac]
    _ ≤ _ := β.dist_le_W1 _ _
    _ ≤ _ := FinProb.W1_ofWeights_dirac_le s y _ _ y₀

end BaryExt

/-! ### The construction for an abstract Whitney family -/

/-- The construction of Section 3 for an abstract Whitney family (multiplicity `m`, parameters
`α, δ, γ`), points `a i` with `d(a i, B i) < (1 + ε₀) r i` and the partition of unity of
Lemma 3.2 with exponent `p`. -/
private theorem barycentric_extension_of_whitney {Z : Type*} [MetricSpace Z] {Y : Type*}
    [MetricSpace Y] (β : BarycenterMap Y) {A : Set Z} (hA : A.Nonempty) {f : Z → Y}
    (hf : LipschitzOnWith 1 f A) {ι : Type*} {B : ι → Set Z} {r : ι → ℝ} {m : ℕ} {α δ γ : ℝ}
    (hW : IsWhitneyFamily A B r m α δ γ) (hα : 0 ≤ α) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < γ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) {p : ℝ} (hp : 1 < p) :
    ∃ F : Z → Y, (∀ a ∈ A, F a = f a) ∧
      (∀ z, 0 < infDist z A →
        LipAt F z (2 * p * (m : ℝ) ^ (1 / p) * ((1 + ε₀ + α + δ) * γ / (δ * (1 - δ))))) ∧
      ∃ C : ℝ, ∀ a ∈ A, ∀ z, 0 < infDist z A → dist (F z) (f a) ≤ C * dist z a := by
  classical
  obtain ⟨φ, hφ0, hφU, -, hφfin, hφsum, hφLip⟩ := hW.exists_partitionOfUnity hA hδ hδ1 hp
  -- the points `a i ∈ A` with `d(x i, a i) < (1 + ε₀) r i` for some `x i ∈ B i`
  have hex : ∀ i, ∃ a ∈ A, ∃ x ∈ B i, dist x a < (1 + ε₀) * r i := by
    intro i
    obtain ⟨x, hx, hxA⟩ := hW.exists_infDist_lt i (mul_pos hε₀ (hW.r_pos i))
    obtain ⟨a, haA, hxa⟩ := (infDist_lt_iff hA).1 hxA
    exact ⟨a, haA, x, hx, by linarith⟩
  choose a haA x hxB hxa using hex
  set M := 1 + ε₀ + α + δ with hM
  have hM0 : 0 < M := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  -- `f` is `1`-Lipschitz on the points `a i`
  have hfa : ∀ i b, b ∈ A → dist (f (a i)) (f b) ≤ dist (a i) b := fun i b hb ↦ by
    simpa using hf.dist_le_mul (a i) (haA i) b hb
  -- for `φ i w ≠ 0`: `d(a i, w) ≤ M r i` and `(1 - δ) r i ≤ d(w, A)`
  have key : ∀ i w, 0 < infDist w A → φ i w ≠ 0 →
      dist (a i) w ≤ M * r i ∧ (1 - δ) * r i ≤ infDist w A := by
    intro i w hw hφ
    have hU := hφU i w hw hφ
    refine ⟨?_, hW.one_sub_mul_le_infDist hU⟩
    obtain ⟨b, hb, hwb⟩ := (infDist_lt_iff (hW.nonempty i)).1 hU
    have h1 := hxa i
    have h2 := hW.diam_le i (x i) (hxB i) b hb
    have h3 : dist (a i) w ≤ dist (a i) (x i) + dist (x i) b + dist b w := dist_triangle4 _ _ _ _
    rw [dist_comm (a i) (x i), dist_comm b w] at h3
    have e : M * r i = (1 + ε₀) * r i + α * r i + δ * r i := by rw [hM]; ring
    linarith
  refine ⟨baryExt β A f (fun i ↦ f (a i)) φ hφ0 hφfin hφsum, ?_, ?_, ?_⟩
  · -- `F = f` on `A`
    intro a' ha'
    apply baryExt_of_not_pos
    rw [infDist_zero_of_mem ha']
    exact lt_irrefl 0
  · -- the pointwise Lipschitz bound
    intro z hz L' hL'
    obtain ⟨j, hj⟩ := hW.cover z hz
    have hrj := hW.r_pos j
    have hzA : infDist z A ≤ γ * r j := hW.hd_le j z hj
    have hp0 : 0 < p := zero_lt_one.trans hp
    -- `T` is the threshold of Lemma 3.2 at `z`, `R₀ = M γ r j / (1 - δ)` bounds `d(a i, z)`
    obtain ⟨T, hT⟩ : ∃ T, T = 2 * p * (m : ℝ) ^ (1 / p) / (δ * r j) := ⟨_, rfl⟩
    obtain ⟨R₀, hR₀⟩ : ∃ R₀, R₀ = M * γ * r j / (1 - δ) := ⟨_, rfl⟩
    have hT0 : 0 ≤ T := by
      rw [hT]
      exact div_nonneg (mul_nonneg (mul_nonneg zero_le_two hp0.le)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (mul_pos hδ hrj).le
    have hR₀pos : 0 < R₀ := by
      rw [hR₀]
      exact div_pos (mul_pos (mul_pos hM0 hγ) hrj) h1δ
    have hTR : T * R₀ = 2 * p * (m : ℝ) ^ (1 / p) * (M * γ / (δ * (1 - δ))) := by
      rw [hT, hR₀]
      field_simp
    have hTL : T * R₀ < L' := hTR ▸ hL'
    -- choose `K` between the threshold `T` and `L' / R₀`
    obtain ⟨K, hK⟩ : ∃ K, K = (T + L' / R₀) / 2 := ⟨_, rfl⟩
    have hTR' : T < L' / R₀ := by rw [lt_div_iff₀ hR₀pos]; exact hTL
    have hTK : T < K := by rw [hK]; linarith
    have hKR : K * R₀ < L' := by
      have e : L' / R₀ * R₀ = L' := div_mul_cancel₀ _ hR₀pos.ne'
      rw [hK]
      nlinarith
    have hK0 : 0 < K := lt_of_le_of_lt hT0 hTK
    have ev1 := hφLip z j hj K (hT ▸ hTK)
    have ev2 : ∀ᶠ z' in 𝓝 z, 0 < infDist z' A :=
      ((continuous_infDist_pt A).tendsto z).eventually_const_lt hz
    have ev3 : ∀ᶠ z' in 𝓝 z, (M * (γ * r j + dist z z') / (1 - δ) + dist z z') * K < L' := by
      have hc : Continuous fun z' ↦ (M * (γ * r j + dist z z') / (1 - δ) + dist z z') * K := by
        fun_prop
      have h0 : (M * (γ * r j + dist z z) / (1 - δ) + dist z z) * K < L' := by
        rw [dist_self, add_zero, add_zero]
        calc M * (γ * r j) / (1 - δ) * K = K * R₀ := by rw [hR₀]; ring
          _ < L' := hKR
      exact (hc.tendsto z).eventually_lt_const h0
    filter_upwards [ev1, ev2, ev3] with z' hsumz' hz' hRK
    obtain ⟨d, hd⟩ : ∃ d, d = dist z z' := ⟨_, rfl⟩
    rw [← hd] at hsumz' hRK ⊢
    have hd0 : 0 ≤ d := hd ▸ dist_nonneg
    obtain ⟨R, hR⟩ : ∃ R, R = M * (γ * r j + d) / (1 - δ) + d := ⟨_, rfl⟩
    rw [← hR] at hRK
    have hR0 : 0 ≤ R := by
      rw [hR]
      exact add_nonneg (div_nonneg (mul_nonneg hM0.le
        (add_nonneg (mul_nonneg hγ.le hrj.le) hd0)) h1δ.le) hd0
    -- the common finite index set
    set S := (hφfin z hz).toFinset ∪ (hφfin z' hz').toFinset with hS
    have hSz : {i | φ i z ≠ 0} ⊆ ↑S := by
      intro i hi
      rw [hS, Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inl hi
    have hSz' : {i | φ i z' ≠ 0} ⊆ ↑S := by
      intro i hi
      rw [hS, Finset.coe_union, Set.Finite.coe_toFinset, Set.Finite.coe_toFinset]
      exact Or.inr hi
    -- all points `a i`, `i ∈ S`, lie within `R` of `z`
    have hRi : ∀ i ∈ S, dist (a i) z ≤ R := by
      intro i hi
      rw [hS, Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hi
      rcases hi with hi | hi
      · obtain ⟨h1, h2⟩ := key i z hz hi
        have h3 : M * r i ≤ M * (γ * r j + d) / (1 - δ) := by
          rw [le_div_iff₀ h1δ]
          nlinarith [mul_le_mul_of_nonneg_left (h2.trans hzA) hM0.le]
        linarith
      · obtain ⟨h1, h2⟩ := key i z' hz' hi
        have hzz : infDist z' A ≤ infDist z A + d := by
          have := infDist_le_infDist_add_dist (x := z') (y := z) (s := A)
          rwa [dist_comm, ← hd] at this
        have h3 : M * r i ≤ M * (γ * r j + d) / (1 - δ) := by
          rw [le_div_iff₀ h1δ]
          have h5 : infDist z A + d ≤ γ * r j + d := by linarith
          nlinarith [mul_le_mul_of_nonneg_left (h2.trans (hzz.trans h5)) hM0.le]
        have h4 : dist (a i) z ≤ dist (a i) z' + d := by
          have := dist_triangle (a i) z' z
          rwa [dist_comm z' z, ← hd] at this
        linarith
    have hD : ∀ i ∈ S, ∀ k ∈ S, dist (f (a i)) (f (a k)) ≤ 2 * R := by
      intro i hi k hk
      have h1 := hfa i (a k) (haA k)
      have h2 := dist_triangle (a i) z (a k)
      rw [dist_comm z (a k)] at h2
      linarith [hRi i hi, hRi k hk]
    calc dist (baryExt β A f (fun i ↦ f (a i)) φ hφ0 hφfin hφsum z)
          (baryExt β A f (fun i ↦ f (a i)) φ hφ0 hφfin hφsum z')
        ≤ 2 * R / 2 * ∑ i ∈ S, |φ i z - φ i z'| := dist_baryExt_le hz hz' S hSz hSz' hD
      _ ≤ R * (K * d) := by
          rw [mul_div_cancel_left₀ _ two_ne_zero]
          exact mul_le_mul_of_nonneg_left (hsumz' S) hR0
      _ = R * K * d := by ring
      _ ≤ L' * d := mul_le_mul_of_nonneg_right hRK.le hd0
  · -- continuity at `A`
    refine ⟨M / (1 - δ) + 1, fun a' ha' z hz ↦ ?_⟩
    have hza : infDist z A ≤ dist z a' := infDist_le_dist_of_mem ha'
    have hS : {i | φ i z ≠ 0} ⊆ ↑(hφfin z hz).toFinset := (hφfin z hz).coe_toFinset.symm.subset
    refine (dist_baryExt_le_sum hz _ hS (f a')).trans ?_
    calc ∑ i ∈ (hφfin z hz).toFinset, φ i z * dist (f (a i)) (f a')
        ≤ ∑ i ∈ (hφfin z hz).toFinset, φ i z * ((M / (1 - δ) + 1) * dist z a') := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Set.Finite.mem_toFinset] at hi
          obtain ⟨h1, h2⟩ := key i z hz hi
          apply mul_le_mul_of_nonneg_left _ (hφ0 i z)
          have h3 : dist (a i) a' ≤ dist (a i) z + dist z a' := dist_triangle _ _ _
          have h4 : M * r i ≤ M / (1 - δ) * dist z a' := by
            rw [div_mul_eq_mul_div, le_div_iff₀ h1δ]
            nlinarith [mul_le_mul_of_nonneg_left (h2.trans hza) hM0.le]
          nlinarith [hfa i a' ha']
      _ = (M / (1 - δ) + 1) * dist z a' := by
          rw [← Finset.sum_mul, hφsum z hz _ hS, one_mul]

/-- The local construction behind **Theorem 1.2**: an extension `F` which is pointwise
`1000 (c+1) log₂(n+2)`-Lipschitz off the closure of `A` and continuous at `A` in a
quantitative way. -/
theorem exists_lipAt_extension_of_nagata {Z : Type u} [MetricSpace Z] {Y : Type*}
    [MetricSpace Y] (β : BarycenterMap Y) {A : Set Z} (hA : A.Nonempty) {n : ℕ} {c : ℝ}
    (hN : Nagata n c A) {f : Z → Y} (hf : LipschitzOnWith 1 f A) :
    ∃ F : Z → Y, (∀ a ∈ A, F a = f a) ∧
      (∀ z, 0 < infDist z A → LipAt F z (1000 * (c + 1) * Real.logb 2 (n + 2))) ∧
      ∃ C : ℝ, ∀ a ∈ A, ∀ z, 0 < infDist z A → dist (F z) (f a) ≤ C * dist z a := by
  have hc : 0 ≤ c := hN.nonneg hA
  -- Proposition 3.1 with `ρ = 5/4`
  obtain ⟨ι, B, r, hW⟩ := Nagata.exists_isWhitneyFamily' hA hN
  -- Lemma 3.2 with `p = log(3(n+1)) > 1`
  have h3 : (0 : ℝ) < 3 * ((n : ℝ) + 1) := by positivity
  have hp : 1 < Real.log (3 * ((n : ℝ) + 1)) := by
    rw [Real.lt_log_iff_exp_lt h3]
    have := Real.exp_one_lt_d9
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨F, hF1, hF2, hF3⟩ := barycentric_extension_of_whitney β hA hf hW
    (by linarith) (by norm_num) (by norm_num) (by norm_num) (ε₀ := 1 / 100) (by norm_num) hp
  refine ⟨F, hF1, fun z hz ↦ (hF2 z hz).mono ?_, hF3⟩
  -- `(3(n+1))^(1/p) = e`
  have hme : ((3 * (n + 1) : ℕ) : ℝ) ^ (1 / Real.log (3 * ((n : ℝ) + 1))) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos (by push_cast; exact h3)]
    push_cast
    rw [mul_one_div_cancel (by linarith)]
  rw [hme]
  calc _ = 2 * Real.exp 1 * Real.log (3 * ((n : ℝ) + 1)) *
        ((1 + 1 / 100 + (3 + 29 / 9 * c) + 1 / 25) * (3 / 2) / (1 / 25 * (1 - 1 / 25))) := by
        ring
    _ ≤ _ := langSchlichenmaier_numeric n hc

variable {X : Type u} [MetricSpace X] {Y : Type v} [MetricSpace Y]

/-- The local extension property for targets with a barycenter map. -/
theorem localExtensionProperty_of_nagata (β : BarycenterMap Y) {n : ℕ} {c : ℝ} {A : Set X}
    (hA : A.Nonempty) (hN : Nagata n c A) {f : X → Y} (hf : LipschitzOnWith 1 f A) :
    LocalExtensionProperty A f (1000 * (c + 1) * Real.logb 2 (n + 2)) := by
  intro V _ _ _ ι hι
  have : Nonempty X := ⟨hA.some⟩
  obtain ⟨F, hF1, hF2, C, hC⟩ := exists_lipAt_extension_of_nagata β (hA.image ι)
    (hN.image_isometry hι) (lipschitzOnWith_comp_invFun hι hf)
  refine ⟨F, fun a ha ↦ ?_, hF2, C, fun a ha z hz ↦ ?_⟩
  · rw [hF1 _ (mem_image_of_mem ι ha), comp_invFun_apply hι]
  · have := hC _ (mem_image_of_mem ι ha) z hz
    rwa [comp_invFun_apply hι] at this

/-- The constant `1000 (c + 1) log₂(n + 2)` of Theorem 1.2 is nonnegative. -/
private theorem langSchlichenmaier_constant_nonneg (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ 1000 * (c + 1) * Real.logb 2 (n + 2) := by
  have : 0 ≤ Real.logb 2 ((n : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
  positivity

end LipschitzExtension

open LipschitzExtension

namespace LipschitzOnWith

universe u v

variable {X : Type u} [MetricSpace X] {Y : Type v} [MetricSpace Y] {n : ℕ} {c : ℝ} {A : Set X}
  {f : X → Y}

/-- **Theorem 1.2** for targets with a barycenter map: if `A ⊆ X` satisfies `Nagata(n, c)` and
the complete metric space `Y` admits a barycenter map, then every `1`-Lipschitz map on `A` extends
to a `1000 (c + 1) log₂(n + 2)`-Lipschitz map on `X`. -/
theorem extend_nagata_barycenterMap [CompleteSpace Y] (hf : LipschitzOnWith 1 f A)
    (hN : Nagata n c A) (β : BarycenterMap Y) :
    ∃ F : X → Y, LipschitzWith (1000 * (c + 1) * Real.logb 2 (n + 2)).toNNReal F ∧ EqOn f F A := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact exists_lipschitzWith_eqOn_empty f _
  obtain ⟨F, hFA, hF⟩ := exists_lipschitz_extension_of_local_of_completeSpace hA
    (langSchlichenmaier_constant_nonneg n (hN.nonneg hA))
    (localExtensionProperty_of_nagata β hA hN hf)
  exact ⟨F, LipschitzWith.of_dist_le' hF, hFA.symm⟩

/-- **Theorem 1.2** for closed subsets `A` and targets with a barycenter map; here `Y` need not be
complete. -/
theorem extend_nagata_barycenterMap_of_isClosed (hf : LipschitzOnWith 1 f A) (hA : IsClosed A)
    (hN : Nagata n c A) (β : BarycenterMap Y) :
    ∃ F : X → Y, LipschitzWith (1000 * (c + 1) * Real.logb 2 (n + 2)).toNNReal F ∧ EqOn f F A := by
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · exact exists_lipschitzWith_eqOn_empty f _
  obtain ⟨F, hFA, hF⟩ := exists_lipschitz_extension_of_local hA hAne
    (langSchlichenmaier_constant_nonneg n (hN.nonneg hAne))
    (localExtensionProperty_of_nagata β hAne hN hf)
  exact ⟨F, LipschitzWith.of_dist_le' hF, hFA.symm⟩

/-- **Theorem 1.2** (Lang–Schlichenmaier with explicit constants for gNPC targets): let `X` be a
metric space and `A ⊆ X` a subset satisfying `Nagata(n, c)`, and let `Y` be a complete metric space
of generalized non-positive curvature. Then every `1`-Lipschitz map `f : A → Y` admits a
`1000 (c + 1) log₂(n + 2)`-Lipschitz extension `F : X → Y`. -/
theorem extend_nagata_isGNPC [CompleteSpace Y] (hf : LipschitzOnWith 1 f A) (hN : Nagata n c A)
    (hY : IsGNPC Y) :
    ∃ F : X → Y, LipschitzWith (1000 * (c + 1) * Real.logb 2 (n + 2)).toNNReal F ∧ EqOn f F A :=
  exists_lipschitzWith_eqOn_of_nonempty fun _ ↦
    hf.extend_nagata_barycenterMap hN hY.nonempty_barycenterMap.some

/-- **Theorem 1.2** for Banach space targets: if `A ⊆ X` satisfies `Nagata(n, c)` and `E` is a real
Banach space, every `1`-Lipschitz map `A → E` extends to a `1000 (c+1) log₂(n+2)`-Lipschitz map
`X → E`. -/
theorem extend_nagata_normedSpace {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : X → E} (hf : LipschitzOnWith 1 f A) (hN : Nagata n c A) :
    ∃ F : X → E, LipschitzWith (1000 * (c + 1) * Real.logb 2 (n + 2)).toNNReal F ∧ EqOn f F A :=
  hf.extend_nagata_barycenterMap hN (BarycenterMap.ofNormedSpace E)

/-- **Theorem 1.2** for complete CAT(0) targets. -/
theorem extend_nagata_isCAT0 [CompleteSpace Y] (hf : LipschitzOnWith 1 f A) (hN : Nagata n c A)
    (hY : IsCAT0 Y) :
    ∃ F : X → Y, LipschitzWith (1000 * (c + 1) * Real.logb 2 (n + 2)).toNNReal F ∧ EqOn f F A :=
  hf.extend_nagata_isGNPC hN hY.isGNPC

end LipschitzOnWith
