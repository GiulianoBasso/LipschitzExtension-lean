/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Barycenter.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# The space `P₁(X)` and the `1`-Wasserstein distance

This file defines the space `P₁(X)` of Section 2.1 of [Basso2024bicombings] (and of Section 2.4
of [Basso2024]) and the `1`-Wasserstein distance `W₁` on it. For a metric space `X` (with its Borel
σ-algebra), `P₁(X)` is the set of Radon probability measures `μ` on `X` with finite first moment,
i.e. `∫ d(x, x₀) dμ(x) < ∞` for some (equivalently, every) `x₀ ∈ X` (in [Basso2024bicombings]:
`W₁(μ, δ_{x₀}) < ∞`). "Radon" means inner regular with respect to compact sets
(`Measure.InnerRegular`). The support `spt μ` of [Basso2024bicombings], the set of all `x` such
that every open set containing `x` has positive measure, is Mathlib's `Measure.support`
(`Measure.mem_support_iff_forall`: every neighbourhood of `x` has positive measure).

We also show that finitely supported probability measures embed isometrically into `P₁(X)`
(`FinProb.toP1`, `FinProb.W1_toP1`) and that the support of `μ ∈ P₁(X)` is nonempty and has full
measure.

## Main definitions

* `P1 X`: the Radon probability measures on `X` with finite first moment.
* `P1.W1`: the `1`-Wasserstein distance, in Kantorovich–Rubinstein form.
* `P1.dirac`: the Dirac measure `δ_x` as an element of `P₁(X)`.
* `FinProb.toMeasure`, `FinProb.toP1`: a finitely supported probability measure as a measure and
  as an element of `P₁(X)`.

## Main statements

* `P1.W1_nonneg`, `P1.W1_self`, `P1.W1_comm`, `P1.W1_triangle`: `W₁` is a pseudometric on
  `P₁(X)`.
* `P1.W1_dirac_dirac`: `x ↦ δ_x` is an isometric embedding `X → P₁(X)`.
* `FinProb.W1_toP1`: finitely supported probability measures embed isometrically into `P₁(X)`.
* `FinProb.support_toP1`: the support of a finitely supported probability measure is the set of
  its atoms.
* `P1.measure_compl_support`, `P1.support_nonempty`: the support of `μ ∈ P₁(X)` has full measure
  and is nonempty.

## Implementation notes

We define the `1`-Wasserstein distance in Kantorovich–Rubinstein form (`P1.W1`),
`W₁(μ, ν) = sup { ∫ f dμ - ∫ f dν : f : X → ℝ 1-Lipschitz }`, as for finitely supported measures
(`FinProb.W1`).

* This is exactly the definition of [Basso2024] (Section 2.4, equation (2.7):
  `W₁(μ, ν) = ‖μ - ν‖_KR`).
* [Basso2024bicombings] defines `W₁(μ, ν)` as the infimum of `∫ d(x, y) dπ(x, y)` over all
  couplings `π` of `(μ, ν)`, and then uses the Kantorovich–Rubinstein duality theorem (its
  equation (2.1)), which says that the two definitions agree. One inequality is elementary and
  always holds: the Kantorovich–Rubinstein `W₁` is at most the coupling `W₁`, since
  `∫ f dμ - ∫ f dν = ∫ (f(x) - f(y)) dπ(x, y) ≤ ∫ d(x, y) dπ(x, y)` for every coupling `π` and
  every `1`-Lipschitz `f`. Hence a barycenter map that is contracting in our sense is also
  contracting for the coupling `W₁`, and our Theorem 2.7
  (`ConicalBicombing.exists_contractingBarycenterMap`) is at least as strong as the paper's.
  (Lemma 2.5, and with it the implication "barycentric ⇒ conical bicombing" of Theorem 2.6, is
  stated for maps that are contracting in our sense; by the duality theorem this is the same.)
* The barycenter theorems only use that `W₁` is a pseudometric on `P₁(X)`. That `W₁(μ, ν) = 0`
  implies `μ = ν`, so that `(P₁(X), W₁)` is a metric space, is `P1.eq_of_W1_eq_zero`.

## References

* [G. Basso, *Extending and improving conical bicombings*][Basso2024bicombings]
* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open MeasureTheory Set Metric

namespace LipschitzExtension

/-- The space `P₁(X)` of Radon probability measures on `X` with finite first moment (Section 2.1
of [Basso2024bicombings]). -/
structure P1 (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] where
  /-- The underlying measure. -/
  toMeasure : Measure X
  /-- The measure is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure toMeasure
  /-- The measure is inner regular with respect to compact sets (a Radon measure). -/
  innerRegular : toMeasure.InnerRegular
  /-- The measure has finite first moment: `x ↦ d(x, x₀)` is integrable for some `x₀`. -/
  exists_integrable_dist : ∃ x₀ : X, Integrable (fun x ↦ dist x x₀) toMeasure

attribute [instance] P1.isProbabilityMeasure P1.innerRegular

namespace P1

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Two elements of `P₁(X)` with the same underlying measure are equal. -/
theorem ext {μ ν : P1 X} (h : μ.toMeasure = ν.toMeasure) : μ = ν := by
  cases μ; cases ν; cases h; rfl

/-- `x ↦ d(x, x₀)` is integrable for every `x₀` (finite first moment). -/
theorem integrable_dist (μ : P1 X) (x₀ : X) : Integrable (fun x ↦ dist x x₀) μ.toMeasure := by
  obtain ⟨x₁, hx₁⟩ := μ.exists_integrable_dist
  refine Integrable.mono' (hx₁.add (integrable_const (dist x₁ x₀)))
    (continuous_id.dist continuous_const).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg dist_nonneg]
  exact dist_triangle x x₁ x₀

/-- Lipschitz functions are integrable with respect to every `μ ∈ P₁(X)`. -/
theorem integrable_of_lipschitzWith (μ : P1 X) {K : NNReal} {g : X → ℝ}
    (hg : LipschitzWith K g) : Integrable g μ.toMeasure := by
  obtain ⟨x₀, hx₀⟩ := μ.exists_integrable_dist
  refine Integrable.mono' ((integrable_const |g x₀|).add (hx₀.const_mul K))
    hg.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ ?_)
  have h := hg.dist_le_mul x x₀
  rw [Real.dist_eq] at h
  change |g x| ≤ |g x₀| + K * dist x x₀
  have h' := abs_sub_abs_le_abs_sub (g x) (g x₀)
  linarith

/-- The `1`-Wasserstein distance, in Kantorovich–Rubinstein form:
`W₁(μ, ν) = sup { ∫ g dμ - ∫ g dν : g 1-Lipschitz }`. -/
noncomputable def W1 (μ ν : P1 X) : ℝ :=
  sSup {r | ∃ g : X → ℝ, LipschitzWith 1 g ∧
    r = ∫ x, g x ∂μ.toMeasure - ∫ x, g x ∂ν.toMeasure}

/-- The pairing with a `1`-Lipschitz function is bounded by the first moments. -/
private theorem integral_sub_integral_le (μ ν : P1 X) (x₀ : X) {g : X → ℝ}
    (hg : LipschitzWith 1 g) :
    ∫ x, g x ∂μ.toMeasure - ∫ x, g x ∂ν.toMeasure ≤
      ∫ x, dist x x₀ ∂μ.toMeasure + ∫ x, dist x x₀ ∂ν.toMeasure := by
  have hμ : ∫ x, g x ∂μ.toMeasure ≤ ∫ x, (g x₀ + dist x x₀) ∂μ.toMeasure :=
    integral_mono (μ.integrable_of_lipschitzWith hg)
      ((integrable_const _).add (μ.integrable_dist x₀)) fun x ↦ by
        have := FinProb.sub_le_dist_of_lipschitz hg x x₀
        linarith
  have hν : ∫ x, (g x₀ - dist x x₀) ∂ν.toMeasure ≤ ∫ x, g x ∂ν.toMeasure :=
    integral_mono ((integrable_const _).sub (ν.integrable_dist x₀))
      (ν.integrable_of_lipschitzWith hg) fun x ↦ by
        have := FinProb.sub_le_dist_of_lipschitz hg x₀ x
        rw [dist_comm] at this
        linarith
  rw [integral_add (integrable_const _) (μ.integrable_dist x₀), integral_const,
    probReal_univ, one_smul] at hμ
  rw [integral_sub (integrable_const _) (ν.integrable_dist x₀), integral_const,
    probReal_univ, one_smul] at hν
  linarith

private theorem bddAbove_W1 (μ ν : P1 X) :
    BddAbove {r | ∃ g : X → ℝ, LipschitzWith 1 g ∧
      r = ∫ x, g x ∂μ.toMeasure - ∫ x, g x ∂ν.toMeasure} := by
  obtain ⟨x₀, -⟩ := μ.exists_integrable_dist
  refine ⟨∫ x, dist x x₀ ∂μ.toMeasure + ∫ x, dist x x₀ ∂ν.toMeasure, ?_⟩
  rintro r ⟨g, hg, rfl⟩
  exact integral_sub_integral_le μ ν x₀ hg

/-- `∫ g dμ - ∫ g dν ≤ W₁(μ, ν)` for every `1`-Lipschitz function `g`. -/
theorem integral_sub_integral_le_W1 (μ ν : P1 X) {g : X → ℝ} (hg : LipschitzWith 1 g) :
    ∫ x, g x ∂μ.toMeasure - ∫ x, g x ∂ν.toMeasure ≤ W1 μ ν := by
  exact le_csSup (bddAbove_W1 μ ν) ⟨g, hg, rfl⟩

/-- To bound `W₁(μ, ν)` from above it suffices to bound `∫ g dμ - ∫ g dν` for all
`1`-Lipschitz functions `g`. -/
theorem W1_le {μ ν : P1 X} {C : ℝ}
    (h : ∀ g : X → ℝ, LipschitzWith 1 g → ∫ x, g x ∂μ.toMeasure - ∫ x, g x ∂ν.toMeasure ≤ C) :
    W1 μ ν ≤ C := by
  refine csSup_le ⟨_, fun _ ↦ 0, LipschitzWith.const' 0, rfl⟩ ?_
  rintro r ⟨g, hg, rfl⟩
  exact h g hg

/-- `W₁(μ, ν) ≥ 0` (test against the constant function `0`). -/
theorem W1_nonneg (μ ν : P1 X) : 0 ≤ W1 μ ν := by
  have h := integral_sub_integral_le_W1 μ ν (LipschitzWith.const' (0 : ℝ))
  rwa [integral_zero, integral_zero, sub_self] at h

/-- `W₁(μ, μ) = 0`. -/
theorem W1_self (μ : P1 X) : W1 μ μ = 0 := by
  exact le_antisymm (W1_le fun _ _ ↦ (sub_self _).le) (W1_nonneg μ μ)

/-- `W₁` is symmetric. -/
theorem W1_comm (μ ν : P1 X) : W1 μ ν = W1 ν μ := by
  have key : ∀ μ ν : P1 X, W1 μ ν ≤ W1 ν μ := fun μ ν ↦ W1_le fun g hg ↦ by
    have h := integral_sub_integral_le_W1 ν μ hg.neg
    simp only [Pi.neg_apply, integral_neg] at h
    linarith
  exact le_antisymm (key μ ν) (key ν μ)

/-- The triangle inequality for `W₁`. -/
theorem W1_triangle (μ ν ρ : P1 X) : W1 μ ρ ≤ W1 μ ν + W1 ν ρ := by
  refine W1_le fun g hg ↦ ?_
  have h1 := integral_sub_integral_le_W1 μ ν hg
  have h2 := integral_sub_integral_le_W1 ν ρ hg
  linarith

omit [BorelSpace X] in
/-- Dirac measures are inner regular (use the compact set `{x}`). -/
private theorem innerRegular_dirac (x : X) : (Measure.dirac x).InnerRegular := by
  refine ⟨fun s hs r hr ↦ ?_⟩
  by_cases hx : x ∈ s
  · refine ⟨{x}, singleton_subset_iff.2 hx, isCompact_singleton, ?_⟩
    rwa [Measure.dirac_apply_of_mem (mem_singleton x), ← Measure.dirac_apply_of_mem hx]
  · rw [Measure.dirac_apply' x hs, indicator_of_notMem hx] at hr
    exact absurd hr ENNReal.not_lt_zero

/-- The Dirac measure `δ_x` as an element of `P₁(X)`. -/
noncomputable def dirac (x : X) : P1 X where
  toMeasure := Measure.dirac x
  isProbabilityMeasure := by
    infer_instance
  innerRegular := by
    exact innerRegular_dirac x
  exists_integrable_dist := by
    exact ⟨x, integrable_dirac enorm_lt_top⟩

private theorem toMeasure_dirac (x : X) : (dirac x).toMeasure = Measure.dirac x := rfl

/-- `x ↦ δ_x` is an isometric embedding `X → P₁(X)`. -/
theorem W1_dirac_dirac (x y : X) : W1 (dirac x) (dirac y) = dist x y := by
  apply le_antisymm
  · refine W1_le fun g hg ↦ ?_
    rw [toMeasure_dirac, toMeasure_dirac, integral_dirac, integral_dirac]
    exact FinProb.sub_le_dist_of_lipschitz hg x y
  · have h := integral_sub_integral_le_W1 (dirac x) (dirac y) (LipschitzWith.dist_left y)
    rwa [toMeasure_dirac, toMeasure_dirac, integral_dirac, integral_dirac, dist_self,
      sub_zero] at h

/-- The support of `μ ∈ P₁(X)` has full measure (`μ` is inner regular). -/
theorem measure_compl_support (μ : P1 X) : μ.toMeasure (μ.toMeasure.support)ᶜ = 0 := by
  exact Measure.measure_compl_support_of_innerRegular

/-- The support of `μ ∈ P₁(X)` is nonempty. -/
theorem support_nonempty (μ : P1 X) : μ.toMeasure.support.Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro h
  have h' := μ.measure_compl_support
  rw [h, compl_empty, measure_univ] at h'
  exact one_ne_zero h'

end P1

namespace FinProb

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A finitely supported probability measure `∑_y w(y) δ_y` as a measure. -/
noncomputable def toMeasure (μ : FinProb X) : Measure X :=
  μ.w.sum fun y a ↦ ENNReal.ofReal a • Measure.dirac y

omit [MetricSpace X] [BorelSpace X] in
private theorem toMeasure_eq (μ : FinProb X) :
    μ.toMeasure = ∑ y ∈ μ.w.support, ENNReal.ofReal (μ.w y) • Measure.dirac y := rfl

omit [MetricSpace X] [BorelSpace X] in
private theorem toMeasure_apply (μ : FinProb X) (s : Set X) :
    μ.toMeasure s = ∑ y ∈ μ.w.support, ENNReal.ofReal (μ.w y) * Measure.dirac y s := by
  rw [toMeasure_eq, Measure.finsetSum_apply]
  rfl

/-- Every function is integrable with respect to `ofReal a • δ_y`. -/
private theorem integrable_smul_dirac (g : X → ℝ) (a : ℝ) (y : X) :
    Integrable g (ENNReal.ofReal a • Measure.dirac y) :=
  (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
private theorem exists_mem_support (μ : FinProb X) : ∃ y, y ∈ μ.w.support := by
  refine Finsupp.support_nonempty_iff.2 fun h ↦ ?_
  have h1 := μ.sum_eq_one
  rw [h, Finsupp.sum_zero_index] at h1
  exact zero_ne_one h1

/-- A finitely supported probability measure as an element of `P₁(X)`. -/
noncomputable def toP1 (μ : FinProb X) : P1 X where
  toMeasure := μ.toMeasure
  isProbabilityMeasure := by
    constructor
    rw [toMeasure_apply]
    simp only [measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun y _ ↦ μ.nonneg y]
    have h1 : ∑ y ∈ μ.w.support, μ.w y = 1 := μ.sum_eq_one
    rw [h1, ENNReal.ofReal_one]
  innerRegular := by
    have : ∀ y : X, (Measure.dirac y).InnerRegular := P1.innerRegular_dirac
    rw [toMeasure_eq]
    infer_instance
  exists_integrable_dist := by
    obtain ⟨y, -⟩ := μ.exists_mem_support
    refine ⟨y, ?_⟩
    rw [toMeasure_eq, integrable_finsetSum_measure]
    exact fun z _ ↦ integrable_smul_dirac _ _ z

private theorem toP1_toMeasure (μ : FinProb X) : μ.toP1.toMeasure = μ.toMeasure := rfl

/-- `∫ g d(∑_y μ(y) δ_y) = ∑_y g(y) μ(y)`. -/
theorem integral_toP1 (μ : FinProb X) (g : X → ℝ) :
    ∫ x, g x ∂μ.toP1.toMeasure = μ.w.sum fun y a ↦ g y * a := by
  rw [toP1_toMeasure, toMeasure_eq,
    integral_finsetSum_measure fun y _ ↦ integrable_smul_dirac g _ y, Finsupp.sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (μ.nonneg y), smul_eq_mul,
    mul_comm]

/-- Finitely supported measures embed isometrically into `P₁(X)`. -/
theorem W1_toP1 (μ ν : FinProb X) : P1.W1 μ.toP1 ν.toP1 = W1 μ ν := by
  simp only [P1.W1, W1, integral_toP1, pairing_eq_integ_sub, integ]

/-- The Dirac measures of `FinProb` and of `P₁(X)` agree. -/
theorem toP1_dirac (x : X) : (dirac x).toP1 = P1.dirac x := by
  refine P1.ext ?_
  change (Finsupp.single x (1 : ℝ)).sum (fun y a ↦ ENNReal.ofReal a • Measure.dirac y) =
    Measure.dirac x
  rw [Finsupp.sum_single_index (by rw [ENNReal.ofReal_zero, zero_smul]), ENNReal.ofReal_one,
    one_smul]

/-- The support (in the sense of `Measure.support`) of a finitely supported probability measure
is the set of its atoms. -/
theorem support_toP1 (μ : FinProb X) : μ.toP1.toMeasure.support = μ.w.support := by
  ext x
  rw [Measure.mem_support_iff_forall, Finset.mem_coe, Finsupp.mem_support_iff]
  constructor
  · intro h hx
    have hU : (↑μ.w.support : Set X)ᶜ ∈ nhds x :=
      μ.w.support.finite_toSet.isClosed.isOpen_compl.mem_nhds
        (by rwa [mem_compl_iff, Finset.mem_coe, Finsupp.mem_support_iff, not_not])
    have h0 := h _ hU
    rw [toP1_toMeasure, toMeasure_apply, Finset.sum_eq_zero] at h0
    · exact lt_irrefl 0 h0
    · intro y hy
      rw [Measure.dirac_apply, indicator_of_notMem (not_not.2 (Finset.mem_coe.2 hy)), mul_zero]
  · intro hx U hU
    rw [toP1_toMeasure, toMeasure_apply]
    refine lt_of_lt_of_le ?_
      (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finsupp.mem_support_iff.2 hx))
    rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU), mul_one]
    exact ENNReal.ofReal_pos.2 (lt_of_le_of_ne (μ.nonneg x) (Ne.symm hx))

end FinProb

end LipschitzExtension
