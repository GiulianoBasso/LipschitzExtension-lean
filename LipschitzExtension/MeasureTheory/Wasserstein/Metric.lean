/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.MeasureTheory.Wasserstein.Defs
import LipschitzExtension.Topology.MetricSpace.Bicombing.Defs
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Order.Interval.Set.ProjIcc

/-!
# The metric space `(P₁(X), W₁)` and its linear bicombing

For a metric space `X`, this file shows that the `1`-Wasserstein distance `W₁` (in
Kantorovich–Rubinstein form, `P1.W1`) is a metric on `P₁(X)`: if `W₁(μ, ν) = 0`, then
`∫ g dμ = ∫ g dν` for all bounded Lipschitz functions `g`, and such functions determine finite
Borel measures on metric spaces. This is the metric space `(P₁(X), W₁)` of Section 2.4 of
[Basso2024], where it is asserted without proof ("defines a metric on `P₁(X)`").

The convex combinations `(1 - t) μ + t ν` define a conical bicombing on `P₁(X)`
(`P1.linearBicombing`): for every `1`-Lipschitz `g`, the pairing `ν ↦ ∫ g dν` is affine along
these segments. The paper's proof of the equality case of Lemma 7.4 of [Basso2024], on which its
proof of Lemma 7.5 relies, computes with this bicombing (both results are proved, for `n ≥ 1` and
arbitrary conical bicombings, in `isLeast_lipschitz_conicalExtension_dirac` and
`sqrt_one_add_sphereAvgDist_sq_le`).

We also record `W₁(μ, δ_z) = ∫ d(w, z) dμ(w)` (`P1.W1_dirac_right`).

## Main definitions

* The instance `MetricSpace (P1 X)`: `P₁(X)` with the distance `W₁`.
* `P1.convexComb`: the convex combination `(1 - t) μ + t ν`, for `t ∈ [0, 1]`.
* `P1.linearBicombing`: the linear conical bicombing `(μ, ν, t) ↦ (1 - t) μ + t ν` of
  `(P₁(X), W₁)`.

## Main statements

* `P1.eq_of_W1_eq_zero`: `W₁(μ, ν) = 0` implies `μ = ν`.
* `P1.isometry_dirac`: `x ↦ δ_x` is an isometric embedding `X → P₁(X)`.
* `P1.W1_dirac_right`: `W₁(μ, δ_z) = ∫ d(w, z) dμ(w)`.
* `P1.linearBicombing_apply`: the linear bicombing at `t ∈ [0, 1]` is `(1 - t) μ + t ν`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open MeasureTheory Set Metric

namespace LipschitzExtension

namespace P1

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- If `W₁(μ, ν) = 0`, then `μ` and `ν` give the same integral to every Lipschitz function
(rescale it to a `1`-Lipschitz function). -/
private theorem integral_eq_of_W1_eq_zero {μ ν : P1 X} (h : W1 μ ν = 0) {K : NNReal}
    {g : X → ℝ} (hg : LipschitzWith K g) :
    ∫ x, g x ∂μ.toMeasure = ∫ x, g x ∂ν.toMeasure := by
  set c : ℝ := ((K : ℝ) + 1)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  have hcg : LipschitzWith 1 (fun x ↦ c * g x) := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc0, ← Real.dist_eq, NNReal.coe_one,
      one_mul]
    calc c * dist (g x) (g y) ≤ c * (K * dist x y) := by
          gcongr
          exact hg.dist_le_mul x y
      _ ≤ dist x y := by
          rw [← mul_assoc]
          refine mul_le_of_le_one_left dist_nonneg ?_
          rw [hc, inv_mul_le_iff₀ (by positivity)]
          linarith
  have h1 := integral_sub_integral_le_W1 μ ν hcg
  have h2 := integral_sub_integral_le_W1 ν μ hcg
  rw [W1_comm, h] at h2
  rw [h] at h1
  rw [integral_const_mul, integral_const_mul] at h1 h2
  have h3 : c * (∫ x, g x ∂μ.toMeasure - ∫ x, g x ∂ν.toMeasure) = 0 := by linarith
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd h4 hc0.ne'
  · linarith

/-- `W₁(μ, ν) = 0` implies `μ = ν`: bounded Lipschitz functions determine finite Borel measures
on metric spaces. -/
theorem eq_of_W1_eq_zero {μ ν : P1 X} (h : W1 μ ν = 0) : μ = ν := by
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun _ ↦ Nat.one_div_pos_of_nat
  have hF : ∀ F : Set X, IsClosed F → μ.toMeasure F = ν.toMeasure F := by
    intro F hF
    have h1 := tendsto_integral_thickenedIndicator_of_isClosed μ.toMeasure hF hδ
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := tendsto_integral_thickenedIndicator_of_isClosed ν.toMeasure hF hδ
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h3 : (fun n : ℕ ↦ ∫ x, (thickenedIndicator (hδ n) F x : ℝ) ∂μ.toMeasure) =
        fun n : ℕ ↦ ∫ x, (thickenedIndicator (hδ n) F x : ℝ) ∂ν.toMeasure :=
      funext fun n ↦ integral_eq_of_W1_eq_zero h (lipschitzWith_thickenedIndicator (hδ n) F)
    rw [h3] at h1
    exact (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).1
      (tendsto_nhds_unique h1 h2)
  refine ext (ext_of_generate_finite _ ?_ isPiSystem_isClosed (fun F hF' ↦ hF F hF')
    (hF univ isClosed_univ))
  rw [BorelSpace.measurable_eq (α := X), borel_eq_generateFrom_isClosed]

/-- `P₁(X)` with the `1`-Wasserstein distance is a metric space. -/
noncomputable instance : MetricSpace (P1 X) where
  dist := W1
  dist_self := W1_self
  dist_comm := W1_comm
  dist_triangle := W1_triangle
  eq_of_dist_eq_zero := eq_of_W1_eq_zero

/-- The distance on `P₁(X)` is the `1`-Wasserstein distance `W₁`. -/
theorem dist_eq_W1 (μ ν : P1 X) : dist μ ν = W1 μ ν := rfl

/-- `x ↦ δ_x` is an isometric embedding of `X` into `P₁(X)`. -/
theorem isometry_dirac : Isometry (dirac : X → P1 X) := by
  exact Isometry.of_dist_eq fun x y ↦ W1_dirac_dirac x y

private theorem toMeasure_dirac' (x : X) : (dirac x).toMeasure = Measure.dirac x := rfl

/-- `W₁(μ, δ_z) = ∫ d(w, z) dμ(w)`. -/
theorem W1_dirac_right (μ : P1 X) (z : X) : W1 μ (dirac z) = ∫ w, dist w z ∂μ.toMeasure := by
  apply le_antisymm
  · refine W1_le fun g hg ↦ ?_
    have hint : ∫ x, g x ∂μ.toMeasure - g z = ∫ x, (g x - g z) ∂μ.toMeasure := by
      rw [integral_sub (μ.integrable_of_lipschitzWith hg) (integrable_const _), integral_const,
        probReal_univ, one_smul]
    rw [toMeasure_dirac', integral_dirac, hint]
    exact integral_mono ((μ.integrable_of_lipschitzWith hg).sub (integrable_const _))
      (μ.integrable_dist z) fun x ↦ FinProb.sub_le_dist_of_lipschitz hg x z
  · have h := integral_sub_integral_le_W1 μ (dirac z) (LipschitzWith.dist_left z)
    rwa [toMeasure_dirac', integral_dirac, dist_self, sub_zero] at h

/-- The convex combination `(1 - t) μ + t ν` of `μ, ν ∈ P₁(X)`, for `t ∈ [0, 1]`. -/
noncomputable def convexComb (μ ν : P1 X) (t : Icc (0 : ℝ) 1) : P1 X where
  toMeasure := ENNReal.ofReal (1 - (t : ℝ)) • μ.toMeasure + ENNReal.ofReal (t : ℝ) • ν.toMeasure
  isProbabilityMeasure := by
    constructor
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add (sub_nonneg.2 t.2.2) t.2.1,
      sub_add_cancel, ENNReal.ofReal_one]
  innerRegular := by
    infer_instance
  exists_integrable_dist := by
    obtain ⟨x₀, -⟩ := μ.exists_integrable_dist
    exact ⟨x₀, ((μ.integrable_dist x₀).smul_measure ENNReal.ofReal_ne_top).add_measure
      ((ν.integrable_dist x₀).smul_measure ENNReal.ofReal_ne_top)⟩

/-- The underlying measure of `convexComb μ ν t` is `(1 - t) μ + t ν`. -/
theorem toMeasure_convexComb (μ ν : P1 X) (t : Icc (0 : ℝ) 1) :
    (convexComb μ ν t).toMeasure =
      ENNReal.ofReal (1 - (t : ℝ)) • μ.toMeasure + ENNReal.ofReal (t : ℝ) • ν.toMeasure :=
  rfl

/-- `∫ g d((1 - t) μ + t ν) = (1 - t) ∫ g dμ + t ∫ g dν`. -/
theorem integral_convexComb (μ ν : P1 X) (t : Icc (0 : ℝ) 1) {g : X → ℝ}
    (hμ : Integrable g μ.toMeasure) (hν : Integrable g ν.toMeasure) :
    ∫ x, g x ∂(convexComb μ ν t).toMeasure =
      (1 - (t : ℝ)) * ∫ x, g x ∂μ.toMeasure + (t : ℝ) * ∫ x, g x ∂ν.toMeasure := by
  rw [toMeasure_convexComb, integral_add_measure (hμ.smul_measure ENNReal.ofReal_ne_top)
    (hν.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (sub_nonneg.2 t.2.2), ENNReal.toReal_ofReal t.2.1, smul_eq_mul,
    smul_eq_mul]

/-- The pairing with a `1`-Lipschitz function along a segment `σ_t = (1 - t) μ + t ν`:
`∫ g dσ_s - ∫ g dσ_t = (t - s) (∫ g dμ - ∫ g dν)`. -/
private theorem integral_convexComb_sub (μ ν : P1 X) (s t : Icc (0 : ℝ) 1) {g : X → ℝ}
    (hg : LipschitzWith 1 g) :
    ∫ x, g x ∂(convexComb μ ν s).toMeasure - ∫ x, g x ∂(convexComb μ ν t).toMeasure =
      ((t : ℝ) - s) * (∫ x, g x ∂μ.toMeasure - ∫ x, g x ∂ν.toMeasure) := by
  rw [integral_convexComb μ ν s (μ.integrable_of_lipschitzWith hg)
      (ν.integrable_of_lipschitzWith hg),
    integral_convexComb μ ν t (μ.integrable_of_lipschitzWith hg)
      (ν.integrable_of_lipschitzWith hg)]
  ring

/-- The linear conical bicombing `(μ, ν, t) ↦ (1 - t) μ + t ν` of `(P₁(X), W₁)` (parameters
outside `[0, 1]` are projected to `[0, 1]`). -/
noncomputable def linearBicombing : ConicalBicombing (P1 X) where
  toFun μ ν t := convexComb μ ν (projIcc 0 1 zero_le_one t)
  toFun_zero := by
    intro μ ν
    refine ext ?_
    rw [projIcc_left, toMeasure_convexComb]
    simp
  toFun_one := by
    intro μ ν
    refine ext ?_
    rw [projIcc_right, toMeasure_convexComb]
    simp
  dist_toFun_toFun := by
    intro μ ν s t hs ht
    simp only [dist_eq_W1, projIcc_of_mem _ hs, projIcc_of_mem _ ht]
    apply le_antisymm
    · refine W1_le fun g hg ↦ ?_
      rw [integral_convexComb_sub μ ν _ _ hg]
      have h1 := integral_sub_integral_le_W1 μ ν hg
      have h2 := integral_sub_integral_le_W1 ν μ hg
      rw [W1_comm] at h2
      calc (t - s) * (∫ x, g x ∂μ.toMeasure - ∫ x, g x ∂ν.toMeasure)
          ≤ |t - s| * |∫ x, g x ∂μ.toMeasure - ∫ x, g x ∂ν.toMeasure| := by
            rw [← abs_mul]
            exact le_abs_self _
        _ ≤ |s - t| * W1 μ ν := by
            rw [abs_sub_comm t s]
            gcongr
            exact abs_sub_le_iff.2 ⟨h1, by linarith⟩
    · rcases eq_or_lt_of_le (abs_nonneg (s - t)) with hst | hst
      · rw [← hst, zero_mul]
        exact W1_nonneg _ _
      · refine (le_div_iff₀' hst).1 (W1_le fun g hg ↦ (le_div_iff₀' hst).2 ?_)
        rcases le_total s t with h | h
        · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
          rw [← integral_convexComb_sub μ ν ⟨s, hs⟩ ⟨t, ht⟩ hg]
          exact integral_sub_integral_le_W1 _ _ hg
        · rw [abs_of_nonneg (sub_nonneg.2 h), W1_comm]
          rw [← integral_convexComb_sub μ ν ⟨t, ht⟩ ⟨s, hs⟩ hg]
          exact integral_sub_integral_le_W1 _ _ hg
  conical := by
    intro μ ν μ' ν' t ht
    simp only [dist_eq_W1, projIcc_of_mem _ ht]
    refine W1_le fun g hg ↦ ?_
    rw [integral_convexComb μ ν _ (μ.integrable_of_lipschitzWith hg)
        (ν.integrable_of_lipschitzWith hg),
      integral_convexComb μ' ν' _ (μ'.integrable_of_lipschitzWith hg)
        (ν'.integrable_of_lipschitzWith hg)]
    have h1 := integral_sub_integral_le_W1 μ μ' hg
    have h2 := integral_sub_integral_le_W1 ν ν' hg
    have h3 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 ht.2)
    have h4 := mul_le_mul_of_nonneg_left h2 ht.1
    simp only at h3 h4 ⊢
    linarith

/-- For `t ∈ [0, 1]`, the linear bicombing is the convex combination `(1 - t) μ + t ν`. -/
theorem linearBicombing_apply (μ ν : P1 X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    linearBicombing μ ν t = convexComb μ ν ⟨t, ht⟩ := by
  change convexComb μ ν (projIcc 0 1 zero_le_one t) = _
  rw [projIcc_of_mem _ ht]

end P1

end LipschitzExtension
