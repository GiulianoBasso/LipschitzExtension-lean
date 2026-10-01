/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.MeasureTheory.Sphere.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The constants `c₁ = 4/π` and `c₂ = 4/3`

This file computes the first two of the constants `c_n = ∫_{S^n} |x - q| dρ_n(x)`
(`sphereAvgDist`) of Section 7.1 of [Basso2024], where it is stated that "`c_1 = 4/π` and
`c_2 = 4/3`". By Proposition 7.3 of [Basso2024], they give the constants `λ₁ = √(1 + 16/π²)` and
`λ₂ = 5/3` for complete gNPC spaces (`IsGNPC.lcBall_one`, `IsGNPC.lcBall_two`).

## Main statements

* `integral_sphereMeasure_eq`: the cone formula
  `∫_{S^n} h dρ_n = (1/vol(B^(n+1))) ∫_{B^(n+1)} h(x/|x|) dx`.
* `sphereAvgDist_one`: `c₁ = 4/π`.
* `sphereAvgDist_two`: `c₂ = 4/3`.

## Proof outline

*Cone formula* (`integral_sphereMeasure_eq`, for every `h : ℝ^(n+1) → ℝ`). This follows from the
polar decomposition `Measure.measurePreserving_homeomorphUnitSphereProd` of Lebesgue measure on
`ℝ^(n+1) \ {0}` into `toSphere × Measure.volumeIoiPow n` and `∫_0^1 r^n dr = 1/(n+1)`, together
with `toSphere (S^n) = (n+1) vol(B^(n+1))` (`Measure.toSphere_real_apply_univ`).

*Base point.* We use the base point `q = -e₀` (`integral_dist_eq_sphereAvgDist`): for `|u| = 1`,
`|u + e₀| = √(2 + 2u₀)`, and `√(2 + 2 cos θ) = 2 cos(θ/2)` for `θ ∈ [-π, π]`.

*`c₁`.* In polar coordinates `x = s (cos θ, sin θ)` (`integral_comp_polarCoord_symm`),
`|x/|x| + e₀| = 2 cos(θ/2)`, so
`∫_{B²} |x/|x| + e₀| dx = ∫_0^1 s ds · ∫_{-π}^{π} 2cos(θ/2) dθ = ½ · 8 = 4`, and `vol(B²) = π`.

*`c₂`.* Write `x = (x₀, x')`, put `x' ∈ ℝ²` in polar coordinates `(ρ, φ)` and then `(x₀, ρ)` in
polar coordinates `(s cos θ, s sin θ)`, `θ ∈ (0, π)` (Fubini twice). This gives
`∫_{B³} √(2 + 2x₀/|x|) dx = 2π ∫_0^1 s² ds ∫_0^π √(2 + 2cos θ) sin θ dθ = 2π · (1/3) · (8/3)`,
that is `16π/9`, since `√(2 + 2cos θ) sin θ = 4 cos²(θ/2) sin(θ/2)` has the primitive
`-(8/3) cos³(θ/2)`. Finally `vol(B³) = 4π/3`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open MeasureTheory Metric Set Real

namespace LipschitzExtension

/-! ### The cone formula -/

/-- The radial part of the polar decomposition: the integral of `h (x / ‖x‖)` over the unit ball
is `(∫ h d(toSphere)) / dim`. -/
private theorem setIntegral_ball_eq_integral_toSphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (h : E → ℝ) :
    ∫ x in ball (0 : E) 1, h (‖x‖⁻¹ • x) ∂μ =
      (∫ u, h (u : E) ∂μ.toSphere) / Module.finrank ℝ E := by
  set f : E → ℝ := (ball (0 : E) 1).indicator fun x ↦ h (‖x‖⁻¹ • x) with hf
  set g : Ioi (0 : ℝ) → ℝ := fun r ↦ (Iio (⟨1, mem_Ioi.2 one_pos⟩ : Ioi (0 : ℝ))).indicator 1 r
  have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos
  have h1 : ∫ x in ball (0 : E) 1, h (‖x‖⁻¹ • x) ∂μ =
      ∫ x : ({(0 : E)}ᶜ : Set E), f x.1 ∂(μ.comap (↑)) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl f, restrict_compl_singleton,
      hf, integral_indicator measurableSet_ball]
  -- polar decomposition `x ↦ (x / ‖x‖, ‖x‖)`
  have h2 : ∫ x : ({(0 : E)}ᶜ : Set E), f x.1 ∂(μ.comap (↑)) =
      ∫ p, h (p.1 : E) * g p.2
        ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    rw [← μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
      (Homeomorph.measurableEmbedding _)]
    congr 1 with x
    simp only [hf, g, indicator, mem_ball_zero_iff, mem_Iio, Pi.one_apply, mul_ite, mul_one,
      mul_zero, ← Subtype.coe_lt_coe, homeomorphUnitSphereProd_apply_snd_coe,
      homeomorphUnitSphereProd_apply_fst_coe]
  -- `∫_0^1 r^(dim - 1) dr = 1 / dim`
  have h3 : ∫ r, g r ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) =
      1 / Module.finrank ℝ E := by
    rw [integral_indicator_one measurableSet_Iio, measureReal_def, Measure.volumeIoiPow_apply_Iio,
      Nat.sub_add_cancel hpos, ENNReal.toReal_ofReal (by positivity), Nat.cast_pred hpos]
    simp
  rw [h1, h2, integral_prod_mul (fun u : sphere (0 : E) 1 ↦ h u) g, h3]
  ring

/-- The cone formula: `∫_{S^n} h dρ_n = (1/vol(B^(n+1))) ∫_{B^(n+1)} h(x/|x|) dx` for every `h`
(both sides vanish if `h` is not integrable). -/
theorem integral_sphereMeasure_eq (n : ℕ) (h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :
    ∫ u, h (u : EuclideanSpace ℝ (Fin (n + 1))) ∂(sphereMeasure n) =
      (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))⁻¹ *
        ∫ x in ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, h (‖x‖⁻¹ • x) := by
  rw [setIntegral_ball_eq_integral_toSphere, sphereMeasure, integral_smul_measure,
    ENNReal.toReal_inv, ← measureReal_def, Measure.toSphere_real_apply_univ,
    finrank_euclideanSpace_fin, smul_eq_mul]
  ring

/-! ### Reduction to integrals of functions of the first coordinate -/

/-- For `u` on the unit sphere, `‖u + e₀‖ = √(2 + 2 u₀)`. -/
private theorem dist_neg_single_eq_sqrt (n : ℕ) {u : EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ‖u‖ = 1) : dist u (-EuclideanSpace.single 0 1) = √(2 + 2 * u 0) := by
  have h2 : ‖u + EuclideanSpace.single 0 1‖ ^ 2 = 2 + 2 * u 0 := by
    rw [norm_add_sq_real, hu, PiLp.norm_single, EuclideanSpace.inner_single_right]
    simp only [norm_one, one_pow, conj_trivial, one_mul]
    ring
  rw [dist_eq_norm, sub_neg_eq_add, ← h2, Real.sqrt_sq (norm_nonneg _)]

/-- `c_n = ∫ √(2 + 2 u₀) dρ_n(u)`, using the base point `-e₀`. -/
private theorem sphereAvgDist_eq_integral_sqrt (n : ℕ) :
    sphereAvgDist n =
      ∫ u, √(2 + 2 * (u : EuclideanSpace ℝ (Fin (n + 1))) 0) ∂(sphereMeasure n) := by
  have hq : -EuclideanSpace.single 0 1 ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_neg, PiLp.norm_single, norm_one]
  rw [← integral_dist_eq_sphereAvgDist n hq]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u ↦
    dist_neg_single_eq_sqrt n (mem_sphere_zero_iff_norm.1 u.2))

/-- `√(2 + 2 cos θ) = 2 cos (θ / 2)` for `θ ∈ [-π, π]`. -/
private theorem sqrt_two_add_two_cos {θ : ℝ} (h1 : -π ≤ θ) (h2 : θ ≤ π) :
    √(2 + 2 * cos θ) = 2 * cos (θ / 2) := by
  have hc := Real.cos_sq (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hc
  have hnn : 0 ≤ cos (θ / 2) := cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  rw [show 2 + 2 * cos θ = (2 * cos (θ / 2)) ^ 2 by linear_combination (-4) * hc,
    Real.sqrt_sq (by positivity)]

/-! ### Polar coordinates in the plane -/

/-- `x² + y² = r²` for `(x, y) = (r cos θ, r sin θ)`. -/
private theorem sq_add_sq_polarCoord_symm (p : ℝ × ℝ) :
    (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
  simp only [polarCoord_symm_apply]
  linear_combination p.1 ^ 2 * sin_sq_add_cos_sq p.2

/-- Integrals of radial functions on `ℝ × ℝ` in polar coordinates. -/
private theorem integral_radial_prod (F : ℝ → ℝ) :
    ∫ q : ℝ × ℝ, F √(q.1 ^ 2 + q.2 ^ 2) = 2 * π * ∫ r in Ioi 0, r * F r := by
  have hpol : ∀ p ∈ polarCoord.target, p.1 • F √((polarCoord.symm p).1 ^ 2 +
      (polarCoord.symm p).2 ^ 2) = (p.1 * F p.1) * (fun _ ↦ (1 : ℝ)) p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only [mem_Ioi] at hr
    rw [sq_add_sq_polarCoord_symm, Real.sqrt_sq hr.le, smul_eq_mul, mul_one]
  rw [← integral_comp_polarCoord_symm,
    setIntegral_congr_fun polarCoord.open_target.measurableSet hpol, polarCoord_target,
    Measure.volume_eq_prod, setIntegral_prod_mul (fun r ↦ r * F r) (fun _ ↦ (1 : ℝ)),
    setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [pi_pos]), smul_eq_mul]
  ring

/-! ### `c₁ = 4/π` -/

/-- `‖x‖ = √(x₀² + x₁²)` in `ℝ²`. -/
private theorem norm_fin_two (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ = √(x 0 ^ 2 + x 1 ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg x), EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- `∫_0^1 r dr = 1/2`, as an integral over `(0, ∞)`. -/
private theorem setIntegral_Ioi_indicator_Iio_id :
    ∫ r in Ioi (0 : ℝ), (Iio 1).indicator (fun r ↦ r) r = 1 / 2 := by
  rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, integral_id]
  norm_num

/-- The integral over the unit disc of a function of `x₀ / ‖x‖`, in polar coordinates. -/
private theorem setIntegral_ball_two (φ : ℝ → ℝ) :
    ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, φ ((‖x‖⁻¹ • x) 0) =
      (∫ θ in Ioo (-π) π, φ (cos θ)) / 2 := by
  let T : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
  have hT : MeasurePreserving T volume volume :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
      (volume_preserving_finTwoArrow ℝ)
  let G : ℝ × ℝ → ℝ := fun p ↦
    if p.1 ^ 2 + p.2 ^ 2 < 1 then φ ((√(p.1 ^ 2 + p.2 ^ 2))⁻¹ * p.1) else 0
  have hGT : ∀ x, (ball (0 : EuclideanSpace ℝ (Fin 2)) 1).indicator
      (fun x ↦ φ ((‖x‖⁻¹ • x) 0)) x = G (T x) := by
    intro x
    have hTx : T x = (x 0, x 1) := rfl
    rw [hTx]
    simp only [indicator, mem_ball_zero_iff, G, PiLp.smul_apply, smul_eq_mul, norm_fin_two,
      Real.sqrt_lt' one_pos, one_pow]
  have hpol : ∀ p ∈ polarCoord.target, p.1 • G (polarCoord.symm p) =
      (Iio 1).indicator (fun r ↦ r) p.1 * φ (cos p.2) := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only [mem_Ioi] at hr
    simp only [G, sq_add_sq_polarCoord_symm]
    simp only [Real.sqrt_sq hr.le, sq_lt_one_iff₀ hr.le, polarCoord_symm_apply,
      inv_mul_cancel_left₀ hr.ne', indicator, mem_Iio, smul_eq_mul]
    split_ifs <;> ring
  rw [← integral_indicator measurableSet_ball]
  simp_rw [hGT]
  rw [hT.integral_comp' G, ← integral_comp_polarCoord_symm,
    setIntegral_congr_fun polarCoord.open_target.measurableSet hpol, polarCoord_target,
    Measure.volume_eq_prod,
    setIntegral_prod_mul ((Iio 1).indicator (fun r ↦ r)) (fun θ ↦ φ (cos θ)),
    setIntegral_Ioi_indicator_Iio_id]
  ring

/-- `∫_{-π}^{π} √(2 + 2 cos θ) dθ = 8`. -/
private theorem integral_sqrt_two_add_two_cos :
    ∫ θ in Ioo (-π) π, √(2 + 2 * cos θ) = 8 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
    intervalIntegral.integral_congr (g := fun θ ↦ 2 * cos (θ / 2)) fun θ hθ ↦ by
      rw [uIcc_of_le (by linarith [pi_pos])] at hθ
      exact sqrt_two_add_two_cos hθ.1 hθ.2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div _ two_ne_zero,
    integral_cos]
  simp only [neg_div, sin_neg, sin_pi_div_two, smul_eq_mul]
  norm_num

/-- `c₁ = 4/π` (Section 7.1 of [Basso2024]). -/
theorem sphereAvgDist_one : sphereAvgDist 1 = 4 / π := by
  rw [sphereAvgDist_eq_integral_sqrt,
    integral_sphereMeasure_eq 1 (fun y : EuclideanSpace ℝ (Fin (1 + 1)) ↦ √(2 + 2 * y 0))]
  have hB : (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (ball 0 1) = π := by
    simp [measureReal_def, pi_pos.le]
  rw [setIntegral_ball_two (fun t ↦ √(2 + 2 * t)), hB, integral_sqrt_two_add_two_cos]
  ring

/-! ### `c₂ = 4/3` -/

/-- `‖x‖ = √(x₀² + x₁² + x₂²)` in `ℝ³`. -/
private theorem norm_fin_three (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ = √(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg x), EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- `|a / √(a² + b)| ≤ 1` for `b ≥ 0`. -/
private theorem abs_inv_sqrt_mul_le_one (a : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    |(√(a ^ 2 + b))⁻¹ * a| ≤ 1 := by
  rw [abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_mul_le_one_of_le₀ (Real.abs_le_sqrt (by linarith)) (Real.sqrt_nonneg _)

/-- A bounded measurable function vanishing outside the closed unit ball of a proper space is
integrable. -/
private theorem integrable_of_bound_of_closedBall {X : Type*} [NormedAddCommGroup X]
    [ProperSpace X] [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] {f : X → ℝ} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (hs : ∀ x, f x ≠ 0 → ‖x‖ ≤ 1) : Integrable f μ := by
  refine (integrableOn_iff_integrable_of_support_subset (s := closedBall 0 1) fun x hx ↦
    mem_closedBall_zero_iff.2 (hs x hx)).1 ?_
  exact Measure.integrableOn_of_bounded measure_closedBall_lt_top.ne hf
    (Filter.Eventually.of_forall hC)

/-- The coordinates `x ↦ (x₀, (x₁, x₂))` of `ℝ³`, as a measurable equivalence. -/
private def euclideanThreeEquiv : EuclideanSpace ℝ (Fin 3) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow))

private theorem euclideanThreeEquiv_apply (x : EuclideanSpace ℝ (Fin 3)) :
    euclideanThreeEquiv x = (x 0, (x 1, x 2)) := rfl

private theorem measurePreserving_euclideanThreeEquiv :
    MeasurePreserving euclideanThreeEquiv volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).trans
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).trans
      ((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)))

/-- The integral over the unit ball of `ℝ³` of a function of `x₀ / ‖x‖`, in spherical
coordinates. -/
private theorem setIntegral_ball_three {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∫ x in ball (0 : EuclideanSpace ℝ (Fin 3)) 1, φ ((‖x‖⁻¹ • x) 0) =
      2 * π / 3 * ∫ θ in Ioo 0 π, sin θ * φ (cos θ) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hφ.continuousOn (s := Icc (-1 : ℝ) 1))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by norm_num, by norm_num⟩)
  -- the integrand in the half plane `(x₀, √(x₁² + x₂²))`
  set P : ℝ → ℝ → ℝ := fun a r ↦
    if a ^ 2 + r ^ 2 < 1 then φ ((√(a ^ 2 + r ^ 2))⁻¹ * a) else 0 with hP
  have hPC : ∀ a r, ‖P a r‖ ≤ C := by
    intro a r
    simp only [hP]
    split_ifs
    · have h := abs_le.1 (abs_inv_sqrt_mul_le_one a (sq_nonneg r))
      exact hC _ ⟨h.1, h.2⟩
    · simpa using hC0
  have hPmeas : Measurable fun p : ℝ × ℝ ↦ P p.1 p.2 := by
    refine Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      (hφ.measurable.comp (by fun_prop)) measurable_const
  have hPsupp : ∀ a r, P a r ≠ 0 → a ^ 2 + r ^ 2 < 1 := by
    intro a r h
    by_contra h'
    exact h (by simp only [hP, h', ite_false])
  -- the integrand in the coordinates `(x₀, (x₁, x₂))`
  set G : ℝ × (ℝ × ℝ) → ℝ := fun p ↦ P p.1 √(p.2.1 ^ 2 + p.2.2 ^ 2) with hG
  have hfG : ∀ x, (ball (0 : EuclideanSpace ℝ (Fin 3)) 1).indicator
      (fun x ↦ φ ((‖x‖⁻¹ • x) 0)) x = G (euclideanThreeEquiv x) := by
    intro x
    rw [euclideanThreeEquiv_apply]
    simp only [indicator, mem_ball_zero_iff, hG, hP, PiLp.smul_apply, smul_eq_mul,
      norm_fin_three, Real.sq_sqrt (add_nonneg (sq_nonneg (x 1)) (sq_nonneg (x 2))), ← add_assoc,
      Real.sqrt_lt' one_pos, one_pow]
  have hGmeas : Measurable G :=
    hPmeas.comp (f := fun p : ℝ × (ℝ × ℝ) ↦ (p.1, √(p.2.1 ^ 2 + p.2.2 ^ 2))) (by fun_prop)
  have hGint : Integrable G volume := by
    refine integrable_of_bound_of_closedBall _ hGmeas.aestronglyMeasurable C
      (fun p ↦ hPC _ _) fun p hp ↦ ?_
    have h := hPsupp _ _ hp
    rw [Real.sq_sqrt (by positivity)] at h
    simp only [Prod.norm_def, Real.norm_eq_abs]
    refine max_le (abs_le.2 ⟨by nlinarith, by nlinarith⟩)
      (max_le (abs_le.2 ⟨by nlinarith, by nlinarith⟩) (abs_le.2 ⟨by nlinarith, by nlinarith⟩))
  -- the integrand in the half plane, weighted by the radius `r` of `(x₁, x₂)`
  set Q : ℝ × ℝ → ℝ := fun p ↦ (Ioi 0).indicator (fun r ↦ r * P p.1 r) p.2 with hQ
  have hQmeas : Measurable Q := by
    simp only [hQ, indicator_apply, mem_Ioi]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_snd)
      (measurable_snd.mul hPmeas) measurable_const
  have hQint : Integrable Q volume := by
    refine integrable_of_bound_of_closedBall _ hQmeas.aestronglyMeasurable C
      (fun p ↦ ?_) fun p hp ↦ ?_
    · simp only [hQ, indicator_apply, mem_Ioi]
      split_ifs with hr
      · by_cases h : P p.1 p.2 = 0
        · simpa [h] using hC0
        · have h1 := hPsupp _ _ h
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos hr]
          calc p.2 * ‖P p.1 p.2‖ ≤ 1 * C := by
                gcongr
                · nlinarith
                · exact hPC _ _
            _ = C := one_mul C
      · simpa using hC0
    · simp only [hQ, indicator_apply, mem_Ioi] at hp
      split_ifs at hp with hr
      · have h := hPsupp _ _ (right_ne_zero_of_mul hp)
        simp only [Prod.norm_def, Real.norm_eq_abs]
        exact max_le (abs_le.2 ⟨by nlinarith, by nlinarith⟩)
          (abs_le.2 ⟨by nlinarith, by nlinarith⟩)
      · exact absurd rfl hp
  -- the integrand in polar coordinates `(s, θ)` of the half plane
  have hpol : ∀ p ∈ polarCoord.target, p.1 • Q (polarCoord.symm p) =
      (Iio 1).indicator (fun s ↦ s ^ 2) p.1 *
        (Ioi 0).indicator (fun θ ↦ sin θ * φ (cos θ)) p.2 := by
    rintro ⟨s, θ⟩ ⟨hs, hθ⟩
    simp only [mem_Ioi, mem_Ioo] at hs hθ
    have hsin : 0 < s * sin θ ↔ 0 < θ := by
      constructor
      · intro h
        by_contra hθ'
        have := sin_nonpos_of_nonpos_of_neg_pi_le (not_lt.1 hθ') hθ.1.le
        nlinarith
      · exact fun h ↦ mul_pos hs (sin_pos_of_pos_of_lt_pi h hθ.2)
    simp only [hQ, hP, indicator_apply, mem_Ioi, mem_Iio, sq_add_sq_polarCoord_symm]
    simp only [polarCoord_symm_apply, hsin, Real.sqrt_sq hs.le, sq_lt_one_iff₀ hs.le,
      inv_mul_cancel_left₀ hs.ne', smul_eq_mul]
    split_ifs <;> ring
  calc ∫ x in ball (0 : EuclideanSpace ℝ (Fin 3)) 1, φ ((‖x‖⁻¹ • x) 0)
      = ∫ x, G (euclideanThreeEquiv x) := by
        rw [← integral_indicator measurableSet_ball]
        exact integral_congr_ae (Filter.Eventually.of_forall hfG)
    _ = ∫ p, G p := measurePreserving_euclideanThreeEquiv.integral_comp' G
    _ = ∫ a, ∫ q, G (a, q) := integral_prod G hGint
    _ = ∫ a, 2 * π * ∫ r in Ioi 0, r * P a r := by
        congr 1 with a
        exact integral_radial_prod (P a)
    _ = 2 * π * ∫ a, ∫ r, Q (a, r) := by
        rw [integral_const_mul]
        congr 2 with a
        exact (integral_indicator measurableSet_Ioi).symm
    _ = 2 * π * ∫ p, Q p := congrArg (2 * π * ·) (integral_prod Q hQint).symm
    _ = 2 * π * ((∫ s in Ioi 0, (Iio 1).indicator (fun s ↦ s ^ 2) s) *
          ∫ θ in Ioo (-π) π, (Ioi 0).indicator (fun θ ↦ sin θ * φ (cos θ)) θ) := by
        rw [← integral_comp_polarCoord_symm,
          setIntegral_congr_fun polarCoord.open_target.measurableSet hpol, polarCoord_target,
          Measure.volume_eq_prod,
          setIntegral_prod_mul ((Iio 1).indicator (fun s ↦ s ^ 2))
            ((Ioi 0).indicator (fun θ ↦ sin θ * φ (cos θ)))]
    _ = 2 * π / 3 * ∫ θ in Ioo 0 π, sin θ * φ (cos θ) := by
        rw [setIntegral_indicator measurableSet_Iio, setIntegral_indicator measurableSet_Ioi,
          Ioi_inter_Iio, Ioo_inter_Ioi, max_eq_right (by linarith [pi_pos]),
          ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
          integral_pow]
        ring

/-- `∫_0^π sin θ √(2 + 2 cos θ) dθ = 8/3`. -/
private theorem integral_sin_mul_sqrt_two_add_two_cos :
    ∫ θ in Ioo 0 π, sin θ * √(2 + 2 * cos θ) = 8 / 3 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le,
    intervalIntegral.integral_congr (g := fun θ ↦ 4 * cos (θ / 2) ^ 2 * sin (θ / 2))
      fun θ hθ ↦ by
        rw [uIcc_of_le pi_pos.le] at hθ
        have h := Real.sin_two_mul (θ / 2)
        rw [show 2 * (θ / 2) = θ by ring] at h
        dsimp only
        rw [sqrt_two_add_two_cos (by linarith [hθ.1, pi_pos]) hθ.2, h]
        ring]
  -- the primitive `-(8/3) cos³(θ/2)`
  have hderiv : ∀ x ∈ uIcc 0 π, HasDerivAt (fun θ ↦ -(8 / 3) * cos (θ / 2) ^ 3)
      (4 * cos (x / 2) ^ 2 * sin (x / 2)) x := by
    intro x _
    have h := (((hasDerivAt_id' x).div_const 2).cos.pow 3).const_mul (-(8 / 3 : ℝ))
    convert h using 1
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun x ↦ 4 * cos (x / 2) ^ 2 * sin (x / 2)).intervalIntegrable _ _)]
  simp only [cos_pi_div_two, zero_div, cos_zero]
  norm_num

/-- `c₂ = 4/3` (Section 7.1 of [Basso2024]). -/
theorem sphereAvgDist_two : sphereAvgDist 2 = 4 / 3 := by
  rw [sphereAvgDist_eq_integral_sqrt,
    integral_sphereMeasure_eq 2 (fun y : EuclideanSpace ℝ (Fin (2 + 1)) ↦ √(2 + 2 * y 0))]
  have hB : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (ball 0 1) = π * 4 / 3 := by
    rw [measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow,
      one_mul, ENNReal.toReal_ofReal (by positivity)]
  rw [setIntegral_ball_three (φ := fun t ↦ √(2 + 2 * t)) (by fun_prop), hB,
    integral_sin_mul_sqrt_two_add_two_cos]
  field_simp
  ring

end LipschitzExtension
