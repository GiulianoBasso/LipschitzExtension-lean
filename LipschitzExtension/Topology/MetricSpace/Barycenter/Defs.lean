/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Data.Finsupp.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Barycenter maps on finitely supported probability measures

This file sets up the barycenter maps of Section 2.4 of [Basso2024] on finitely supported
probability measures. We work with finitely supported probability measures `μ = ∑ α_i δ_{y_i}` on
a metric space `Y` (`FinProb Y`), and with the `1`-Wasserstein distance in its
Kantorovich–Rubinstein dual form `W₁(μ, ν) = sup { ∫ g d(μ - ν) : g 1-Lipschitz }` (the paper
defines `W₁(μ, ν)` as the Kantorovich–Rubinstein norm `‖μ - ν‖_KR`, which is this expression).

A *barycenter map* (Definition 2.1 of [Basso2024], after Sturm) is a map `β` with `β δ_y = y`
which is `1`-Lipschitz with respect to `W₁`. We prove that real normed spaces admit barycenter
maps and that a space with a barycenter map is of generalized non-positive curvature
(Definition 1.3 of [Basso2024]). We also prove Lemma 2.5 of [Basso2024].

## Main definitions

* `FinProb Y`: finitely supported probability measures on `Y`.
* `FinProb.dirac`: the Dirac measure `δ_y`.
* `FinProb.ofWeights`: the measure `∑_{i ∈ s} α_i δ_{y_i}`.
* `FinProb.W1`: the `1`-Wasserstein distance, in Kantorovich–Rubinstein dual form.
* `BarycenterMap Y`: barycenter maps on finitely supported probability measures on `Y`
  (Definition 2.1 of [Basso2024], restricted to finitely supported measures).
* `BarycenterMap.ofNormedSpace`: the barycenter map `∑ α_i δ_{y_i} ↦ ∑ α_i y_i` of a real normed
  space.
* `IsGNPC Y`: `Y` is a space of generalized non-positive curvature (Definition 1.3 of
  [Basso2024]).

## Main statements

* `FinProb.W1_nonneg`, `FinProb.W1_self`, `FinProb.W1_comm`, `FinProb.W1_triangle`: `W₁` is a
  pseudometric (that it is a metric is never used).
* `FinProb.W1_dirac_dirac`: `y ↦ δ_y` is an isometric embedding.
* `FinProb.W1_ofWeights_le`: Lemma 2.5 of [Basso2024],
  `W₁(∑ α_i δ_{y_i}, ∑ β_i δ_{y_i}) ≤ (D/2) ∑ |α_i - β_i|`.
* `BarycenterMap.isGNPC`: a space with a barycenter map is of generalized non-positive curvature
  (the easy direction of Theorem 2.4 of [Basso2024]).

## Implementation notes

The paper uses barycenter maps on all of `P₁(Y)`; for the proofs it suffices to have them on
finitely supported measures (remark after Theorem 2.4 of [Basso2024]), which is what
`BarycenterMap` is. Theorem 2.4 of [Basso2024] (Es-Sahib–Heinich, Navas, Descombes: a complete
metric space admits a barycenter map if and only if it is of generalized non-positive curvature)
is formalized in two versions:

* `IsGNPC.nonempty_barycenterMap`: every complete gNPC space admits a barycenter map on finitely
  supported measures (the version used in the paper's proofs);
* `isGNPC_iff_nonempty_contractingBarycenterMap`: Theorem 2.4 itself, i.e. the equivalence for
  barycenter maps on `P₁(Y)` (`ContractingBarycenterMap`), where `W₁` is defined by the
  Kantorovich–Rubinstein norm exactly as in the paper (`P1.W1`).

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open Set

namespace LipschitzExtension

/-- A finitely supported probability measure `μ = ∑_y w(y) δ_y` on `Y`. -/
structure FinProb (Y : Type*) where
  /-- The weights: `w y` is the mass of the point `y`. -/
  w : Y →₀ ℝ
  /-- The weights are nonnegative. -/
  nonneg : ∀ y, 0 ≤ w y
  /-- The weights sum to `1`. -/
  sum_eq_one : w.sum (fun _ a ↦ a) = 1

namespace FinProb

variable {Y : Type*}

/-- Two finitely supported probability measures with the same weights are equal. -/
theorem ext_w {μ ν : FinProb Y} (h : μ.w = ν.w) : μ = ν := by
  cases μ; cases ν; cases h; rfl

/-- The integral `∫ g dμ = ∑_y g(y) μ(y)`. -/
noncomputable def integ (g : Y → ℝ) (μ : FinProb Y) : ℝ :=
  μ.w.sum (fun y a ↦ g y * a)

/-- The weights of a Dirac mass are nonnegative. -/
theorem single_one_nonneg (y z : Y) : 0 ≤ Finsupp.single y (1 : ℝ) z := by
  classical
  rw [Finsupp.single_apply]
  split_ifs <;> norm_num

/-- The Dirac measure `δ_y`. -/
noncomputable def dirac (y : Y) : FinProb Y where
  w := Finsupp.single y 1
  nonneg := by exact single_one_nonneg y
  sum_eq_one := by exact Finsupp.sum_single_index rfl

/-- `pairing g μ ν = ∫ g d(μ - ν) = ∑_y g(y) (μ(y) - ν(y))`. -/
noncomputable def pairing (g : Y → ℝ) (μ ν : FinProb Y) : ℝ :=
  (μ.w - ν.w).sum (fun y a ↦ g y * a)

/-- `∫ g d(μ - ν) = ∫ g dμ - ∫ g dν`. -/
theorem pairing_eq_integ_sub (g : Y → ℝ) (μ ν : FinProb Y) :
    pairing g μ ν = integ g μ - integ g ν :=
  Finsupp.sum_sub_index fun _ _ _ ↦ mul_sub _ _ _

/-- The integral of a constant function against a probability measure. -/
theorem integ_const (c : ℝ) (μ : FinProb Y) : integ (fun _ ↦ c) μ = c := by
  rw [integ, ← Finsupp.mul_sum, μ.sum_eq_one, mul_one]

/-- The integral is additive: `∫ (f - g) dμ = ∫ f dμ - ∫ g dμ`. -/
theorem integ_sub (f g : Y → ℝ) (μ : FinProb Y) :
    integ (fun y ↦ f y - g y) μ = integ f μ - integ g μ := by
  simp only [integ, sub_mul, Finsupp.sum_sub]

/-- `∫ (-g) dμ = -∫ g dμ`. -/
theorem integ_neg (g : Y → ℝ) (μ : FinProb Y) : integ (-g) μ = -integ g μ := by
  simp only [integ, Finsupp.sum, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- The integral is monotone. -/
theorem integ_mono {f g : Y → ℝ} (h : ∀ y, f y ≤ g y) (μ : FinProb Y) :
    integ f μ ≤ integ g μ :=
  Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_right (h y) (μ.nonneg y)

/-- `∫ g dδ_y = g y`. -/
theorem integ_dirac (g : Y → ℝ) (y : Y) : integ g (dirac y) = g y := by
  change (Finsupp.single y (1 : ℝ)).sum (fun y a ↦ g y * a) = g y
  rw [Finsupp.sum_single_index (mul_zero _), mul_one]

/-- Auxiliary computation for weighted sums of Dirac masses. -/
theorem sum_weights {ι : Type*} (s : Finset ι) (y : ι → Y) (α : ι → ℝ) (g : Y → ℝ) :
    (∑ i ∈ s, α i • Finsupp.single (y i) (1 : ℝ)).sum (fun z a ↦ g z * a) =
      ∑ i ∈ s, g (y i) * α i := by
  rw [← Finsupp.sum_finsetSum_index (fun _ ↦ mul_zero _) (fun _ _ _ ↦ mul_add _ _ _)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finsupp.smul_single_one, Finsupp.sum_single_index (mul_zero _)]

variable [PseudoMetricSpace Y]

/-- The `1`-Wasserstein distance between finitely supported probability measures, in
Kantorovich–Rubinstein dual form: `W₁(μ, ν) = sup { ∫ g d(μ - ν) : g 1-Lipschitz }`. -/
noncomputable def W1 (μ ν : FinProb Y) : ℝ :=
  sSup {x | ∃ g : Y → ℝ, LipschitzWith 1 g ∧ x = pairing g μ ν}

/-- `g x - g z ≤ d(x, z)` for a `1`-Lipschitz function `g`. -/
theorem sub_le_dist_of_lipschitz {g : Y → ℝ} (hg : LipschitzWith 1 g) (x z : Y) :
    g x - g z ≤ dist x z := by
  have h := hg.dist_le_mul x z
  rw [NNReal.coe_one, one_mul, Real.dist_eq] at h
  exact (le_abs_self _).trans h

/-- The pairing with a `1`-Lipschitz function is bounded by the cost of the product coupling. -/
theorem pairing_le_integ_dist (μ ν : FinProb Y) {g : Y → ℝ} (hg : LipschitzWith 1 g) :
    pairing g μ ν ≤ integ (fun y ↦ integ (fun z ↦ dist y z) ν) μ := by
  have h1 : ∀ y, integ (fun z ↦ g y - g z) ν = g y - integ g ν := fun y ↦ by
    rw [integ_sub (fun _ ↦ g y) g, integ_const]
  have key : integ (fun y ↦ integ (fun z ↦ g y - g z) ν) μ = pairing g μ ν := by
    simp only [h1]
    rw [integ_sub g (fun _ ↦ integ g ν), integ_const, pairing_eq_integ_sub]
  rw [← key]
  exact integ_mono (fun y ↦ integ_mono (fun z ↦ sub_le_dist_of_lipschitz hg y z) ν) μ

private theorem bddAbove_W1 (μ ν : FinProb Y) :
    BddAbove {x | ∃ g : Y → ℝ, LipschitzWith 1 g ∧ x = pairing g μ ν} := by
  refine ⟨integ (fun y ↦ integ (fun z ↦ dist y z) ν) μ, ?_⟩
  rintro x ⟨g, hg, rfl⟩
  exact pairing_le_integ_dist μ ν hg

/-- `∫ g d(μ - ν) ≤ W₁(μ, ν)` for every `1`-Lipschitz function `g`. -/
theorem pairing_le_W1 (μ ν : FinProb Y) {g : Y → ℝ} (hg : LipschitzWith 1 g) :
    pairing g μ ν ≤ W1 μ ν := by
  exact le_csSup (bddAbove_W1 μ ν) ⟨g, hg, rfl⟩

/-- To bound `W₁(μ, ν)` from above it suffices to bound `∫ g d(μ - ν)` for all `1`-Lipschitz
functions `g`. -/
theorem W1_le {μ ν : FinProb Y} {C : ℝ} (h : ∀ g : Y → ℝ, LipschitzWith 1 g → pairing g μ ν ≤ C) :
    W1 μ ν ≤ C := by
  refine csSup_le ⟨_, fun _ ↦ 0, LipschitzWith.const' 0, rfl⟩ ?_
  rintro x ⟨g, hg, rfl⟩
  exact h g hg

/-- `W₁(μ, ν) ≥ 0`. -/
theorem W1_nonneg (μ ν : FinProb Y) : 0 ≤ W1 μ ν := by
  have h := pairing_le_W1 μ ν (LipschitzWith.const' (0 : ℝ))
  rwa [pairing_eq_integ_sub, integ_const, integ_const, sub_self] at h

/-- `W₁(μ, μ) = 0`. -/
theorem W1_self (μ : FinProb Y) : W1 μ μ = 0 :=
  le_antisymm (W1_le fun g _ ↦ by rw [pairing_eq_integ_sub, sub_self]) (W1_nonneg μ μ)

private theorem W1_le_W1_swap (μ ν : FinProb Y) : W1 μ ν ≤ W1 ν μ :=
  W1_le fun g hg ↦ by
    have h := pairing_le_W1 ν μ hg.neg
    rw [pairing_eq_integ_sub, integ_neg, integ_neg] at h
    rw [pairing_eq_integ_sub]
    linarith

/-- `W₁` is symmetric. -/
theorem W1_comm (μ ν : FinProb Y) : W1 μ ν = W1 ν μ :=
  le_antisymm (W1_le_W1_swap μ ν) (W1_le_W1_swap ν μ)

/-- The triangle inequality for `W₁`. -/
theorem W1_triangle (μ ν ρ : FinProb Y) : W1 μ ρ ≤ W1 μ ν + W1 ν ρ :=
  W1_le fun g hg ↦ by
    have h1 := pairing_le_W1 μ ν hg
    have h2 := pairing_le_W1 ν ρ hg
    rw [pairing_eq_integ_sub] at h1 h2 ⊢
    linarith

/-- The measure `∑_{i ∈ s} α i δ_{y i}`. -/
noncomputable def ofWeights {ι : Type*} (s : Finset ι) (y : ι → Y) (α : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ α i) (h1 : ∑ i ∈ s, α i = 1) : FinProb Y where
  w := ∑ i ∈ s, α i • Finsupp.single (y i) 1
  nonneg := by
    intro z
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_nonneg fun i hi ↦ ?_
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact mul_nonneg (h0 i hi) (single_one_nonneg _ _)
  sum_eq_one := by
    have h := sum_weights s y α (fun _ ↦ 1)
    simp only [one_mul] at h
    rw [h, h1]

omit [PseudoMetricSpace Y] in
/-- `∫ g d(∑ α_i δ_{y_i}) = ∑ α_i g(y_i)`. -/
theorem integ_ofWeights {ι : Type*} (s : Finset ι) (y : ι → Y) {α : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ α i) (h1 : ∑ i ∈ s, α i = 1) (g : Y → ℝ) :
    integ g (ofWeights s y α h0 h1) = ∑ i ∈ s, g (y i) * α i :=
  sum_weights s y α g

omit [PseudoMetricSpace Y] in
/-- `∫ g d(∑ α_i δ_{y_i} - ∑ β_i δ_{y_i}) = ∑ (α_i - β_i) g(y_i)`. -/
theorem pairing_ofWeights {ι : Type*} (s : Finset ι) (y : ι → Y) {α β : ι → ℝ}
    (hα0 : ∀ i ∈ s, 0 ≤ α i) (hα1 : ∑ i ∈ s, α i = 1) (hβ0 : ∀ i ∈ s, 0 ≤ β i)
    (hβ1 : ∑ i ∈ s, β i = 1) (g : Y → ℝ) :
    pairing g (ofWeights s y α hα0 hα1) (ofWeights s y β hβ0 hβ1) =
      ∑ i ∈ s, g (y i) * (α i - β i) := by
  rw [pairing_eq_integ_sub, integ_ofWeights, integ_ofWeights, ← Finset.sum_sub_distrib]
  simp only [mul_sub]

/-- **Lemma 2.5** of [Basso2024]: `W₁(∑ α_i δ_{y_i}, ∑ β_i δ_{y_i}) ≤ (D/2) ∑ |α_i - β_i|`, where
`D` bounds the distances `d(y_i, y_j)`. -/
theorem W1_ofWeights_le {ι : Type*} (s : Finset ι) (y : ι → Y) {α β : ι → ℝ}
    (hα0 : ∀ i ∈ s, 0 ≤ α i) (hα1 : ∑ i ∈ s, α i = 1) (hβ0 : ∀ i ∈ s, 0 ≤ β i)
    (hβ1 : ∑ i ∈ s, β i = 1) {D : ℝ} (hD : ∀ i ∈ s, ∀ j ∈ s, dist (y i) (y j) ≤ D) :
    W1 (ofWeights s y α hα0 hα1) (ofWeights s y β hβ0 hβ1) ≤ D / 2 * ∑ i ∈ s, |α i - β i| := by
  refine W1_le fun g hg ↦ ?_
  rw [pairing_ofWeights]
  have hs : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty] at hα1
      exact absurd hα1 zero_ne_one
    · exact h
  obtain ⟨i₁, hi₁, hmax⟩ := Finset.exists_max_image s (fun i ↦ g (y i)) hs
  obtain ⟨i₂, hi₂, hmin⟩ := Finset.exists_min_image s (fun i ↦ g (y i)) hs
  have hdiff : g (y i₁) - g (y i₂) ≤ D :=
    (sub_le_dist_of_lipschitz hg _ _).trans (hD i₁ hi₁ i₂ hi₂)
  set c := (g (y i₁) + g (y i₂)) / 2 with hc_def
  have hc : ∀ i ∈ s, |g (y i) - c| ≤ D / 2 := by
    intro i hi
    have h1 := hmax i hi
    have h2 := hmin i hi
    rw [abs_le]
    constructor <;> linarith
  have hsum0 : ∑ i ∈ s, (α i - β i) = 0 := by
    rw [Finset.sum_sub_distrib, hα1, hβ1, sub_self]
  have hshift : ∑ i ∈ s, (g (y i) - c) * (α i - β i) =
      ∑ i ∈ s, g (y i) * (α i - β i) - c * ∑ i ∈ s, (α i - β i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hsum0, mul_zero, sub_zero] at hshift
  rw [← hshift, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  calc (g (y i) - c) * (α i - β i) ≤ |(g (y i) - c) * (α i - β i)| := le_abs_self _
    _ = |g (y i) - c| * |α i - β i| := abs_mul _ _
    _ ≤ D / 2 * |α i - β i| := mul_le_mul_of_nonneg_right (hc i hi) (abs_nonneg _)

/-- `W₁(∑ α_i δ_{y_i}, δ_z) ≤ ∑ α_i d(y_i, z)`. -/
theorem W1_ofWeights_dirac_le {ι : Type*} (s : Finset ι) (y : ι → Y) {α : ι → ℝ}
    (hα0 : ∀ i ∈ s, 0 ≤ α i) (hα1 : ∑ i ∈ s, α i = 1) (z : Y) :
    W1 (ofWeights s y α hα0 hα1) (dirac z) ≤ ∑ i ∈ s, α i * dist (y i) z := by
  refine W1_le fun g hg ↦ (pairing_le_integ_dist _ _ hg).trans_eq ?_
  simp only [integ_dirac, integ_ofWeights]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- `y ↦ δ_y` is an isometric embedding: `W₁(δ_y, δ_z) = d(y, z)`. -/
theorem W1_dirac_dirac (y z : Y) : W1 (dirac y) (dirac z) = dist y z := by
  apply le_antisymm
  · refine W1_le fun g hg ↦ ?_
    rw [pairing_eq_integ_sub, integ_dirac, integ_dirac]
    exact sub_le_dist_of_lipschitz hg y z
  · have h := pairing_le_W1 (dirac y) (dirac z) (LipschitzWith.dist_left z)
    rwa [pairing_eq_integ_sub, integ_dirac, integ_dirac, dist_self, sub_zero] at h

/-- Auxiliary: the measure `½ δ_x + ½ δ_y`. -/
private noncomputable def mid (x y : Y) : FinProb Y :=
  ofWeights Finset.univ ![x, y] (fun _ ↦ 1 / 2) (fun _ _ ↦ by norm_num)
    (by rw [Fin.sum_univ_two]; norm_num)

omit [PseudoMetricSpace Y] in
private theorem mid_w (x y : Y) :
    (mid x y).w = (1 / 2 : ℝ) • Finsupp.single x 1 + (1 / 2 : ℝ) • Finsupp.single y 1 := by
  change ∑ i : Fin 2, (1 / 2 : ℝ) • Finsupp.single (![x, y] i) 1 = _
  rw [Fin.sum_univ_two]
  rfl

omit [PseudoMetricSpace Y] in
private theorem mid_comm (x y : Y) : mid x y = mid y x :=
  ext_w (by rw [mid_w, mid_w, add_comm])

omit [PseudoMetricSpace Y] in
private theorem mid_self (y : Y) : mid y y = dirac y :=
  ext_w (by
    rw [mid_w, ← add_smul]
    norm_num
    rfl)

omit [PseudoMetricSpace Y] in
private theorem integ_mid (g : Y → ℝ) (x y : Y) : integ g (mid x y) = (g x + g y) / 2 := by
  rw [mid, integ_ofWeights, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end FinProb

/-- A *barycenter map* on `Y` (Definition 2.1 of [Basso2024], restricted to finitely supported
measures): `β δ_y = y` and `d(β μ, β ν) ≤ W₁(μ, ν)`. -/
structure BarycenterMap (Y : Type*) [PseudoMetricSpace Y] where
  /-- The barycenter `β μ` of a finitely supported probability measure `μ`. -/
  bary : FinProb Y → Y
  /-- `β δ_y = y`. -/
  bary_dirac : ∀ y, bary (FinProb.dirac y) = y
  /-- `β` is `1`-Lipschitz with respect to `W₁`. -/
  dist_le_W1 : ∀ μ ν, dist (bary μ) (bary ν) ≤ FinProb.W1 μ ν

/-- Real normed spaces admit barycenter maps: `β (∑ α_i δ_{y_i}) = ∑ α_i y_i`
(the proof uses the Hahn–Banach theorem). -/
noncomputable def BarycenterMap.ofNormedSpace (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : BarycenterMap E where
  bary μ := μ.w.sum (fun y a ↦ a • y)
  bary_dirac := by
    intro y
    exact (Finsupp.sum_single_index (zero_smul ℝ y)).trans (one_smul ℝ y)
  dist_le_W1 := by
    intro μ ν
    obtain ⟨g, hg1, hgv⟩ :=
      exists_dual_vector'' ℝ (μ.w.sum (fun y a ↦ a • y) - ν.w.sum (fun y a ↦ a • y))
    have hlip : LipschitzWith 1 g :=
      ContinuousLinearMap.lipschitzWith_of_opNorm_le (by simpa using hg1)
    have hg : ∀ ρ : FinProb E, g (ρ.w.sum (fun y a ↦ a • y)) = FinProb.integ g ρ := by
      intro ρ
      rw [map_finsuppSum]
      refine Finsupp.sum_congr fun y _ ↦ ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    calc dist (μ.w.sum (fun y a ↦ a • y)) (ν.w.sum (fun y a ↦ a • y))
        = ‖μ.w.sum (fun y a ↦ a • y) - ν.w.sum (fun y a ↦ a • y)‖ := dist_eq_norm _ _
      _ = g (μ.w.sum (fun y a ↦ a • y) - ν.w.sum (fun y a ↦ a • y)) := by
          rw [hgv]; rfl
      _ = FinProb.pairing g μ ν := by
          rw [map_sub, hg, hg, FinProb.pairing_eq_integ_sub]
      _ ≤ FinProb.W1 μ ν := FinProb.pairing_le_W1 μ ν hlip

/-- A metric space of *generalized non-positive curvature* (a gNPC space, Definition 1.3 of
[Basso2024]): there is a symmetric map `m : Y → Y → Y` with `m y y = y` and
`d(m x y, m x z) ≤ d(y, z) / 2`. -/
def IsGNPC (Y : Type*) [PseudoMetricSpace Y] : Prop :=
  ∃ m : Y → Y → Y, (∀ x y, m x y = m y x) ∧ (∀ y, m y y = y) ∧
    ∀ x y z, dist (m x y) (m x z) ≤ dist y z / 2

/-- A space with a barycenter map is of generalized non-positive curvature
(use `m x y = β(½ δ_x + ½ δ_y)`). This is the easy direction of Theorem 2.4 of [Basso2024]. -/
theorem BarycenterMap.isGNPC {Y : Type*} [PseudoMetricSpace Y] (β : BarycenterMap Y) :
    IsGNPC Y := by
  refine ⟨fun x y ↦ β.bary (FinProb.mid x y),
    fun x y ↦ congrArg β.bary (FinProb.mid_comm x y),
    fun y ↦ (congrArg β.bary (FinProb.mid_self y)).trans (β.bary_dirac y),
    fun x y z ↦ (β.dist_le_W1 _ _).trans (FinProb.W1_le fun g hg ↦ ?_)⟩
  rw [FinProb.pairing_eq_integ_sub, FinProb.integ_mid, FinProb.integ_mid]
  have h := FinProb.sub_le_dist_of_lipschitz hg y z
  linarith

end LipschitzExtension
