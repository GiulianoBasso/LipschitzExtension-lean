/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The normalized surface measure on the unit sphere and the constants `c_n`

This file defines the normalized Riemannian volume measure `ρ_n` on the unit sphere
`S^n ⊆ ℝ^(n+1)` and the constants `c_n` of Section 7.1 of [Basso2024],
`c_n = (1/Vol(S^n)) ∫_{S^n} |x - q| dx = ∫_{S^n} |x - q| dρ_n(x)`,
the average distance to a point `q ∈ S^n`, which does not depend on `q`. For example, `c₁ = 4/π`
and `c₂ = 4/3` (see `LipschitzExtension.MeasureTheory.Sphere.AvgDist`). The constants `c_n` enter
Proposition 7.3 and Lemma 7.5 of [Basso2024].

## Main definitions

* `sphereMeasure n`: the normalized surface measure `ρ_n` on `S^n`, a probability measure with
  full support.
* `sphereAvgDist n`: the constant `c_n`.

## Main statements

* `integral_comp_linearIsometryEquiv`: `ρ_n` is invariant under linear isometries of `ℝ^(n+1)`.
* `integral_dist_eq_sphereAvgDist`: `∫ |x - q| dρ_n(x) = c_n` for every `q ∈ S^n`.
* `sphereAvgDist_le_sqrt_two`: `c_n ≤ √2`, the end of the proof of Proposition 7.3 of
  [Basso2024].

## Implementation notes

`ρ_n = sphereMeasure n` is Mathlib's surface measure `volume.toSphere` on
`sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1`, normalized to a probability measure. By the cone
formula `Measure.toSphere_apply'`, `toSphere s = (n + 1) · Vol((0, 1) · s)`, so `toSphere` is the
Riemannian volume of the sphere. The constant `c_n = sphereAvgDist n` is defined with the base
point `q = e₀`.

## Proof outline

* The invariance of `ρ_n` under a linear isometry `A`: by the cone formula, since the cone over
  `A⁻¹(s)` is the preimage under `A` of the cone over `s`, and `A` preserves the volume
  (`LinearIsometryEquiv.measurePreserving`).
* The independence of `c_n` of the base point `q ∈ S^n`: the reflection
  `Submodule.reflection (ℝ ∙ (q - e₀))ᗮ` maps `q` to `e₀` (`Submodule.reflection_sub`).
* `c_n ≤ √2`, as in the paper: by symmetry,
  `c_n = ½ ∫ (|x - q| + |x + q|) dρ_n ≤ (√2/2) ∫ √(|x - q|² + |x + q|²) dρ_n = √2`, by the
  parallelogram law `|x - q|² + |x + q|² = 4`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open MeasureTheory Metric Set

namespace LipschitzExtension

/-- The normalized Riemannian volume measure on the unit sphere `S^n ⊆ ℝ^(n+1)`: Mathlib's surface
measure `volume.toSphere` divided by its total mass. -/
noncomputable def sphereMeasure (n : ℕ) : Measure (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere

/-- The normalized surface measure is a probability measure. -/
instance isProbabilityMeasure_sphereMeasure (n : ℕ) : IsProbabilityMeasure (sphereMeasure n) := by
  constructor
  rw [sphereMeasure, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.2 (Measure.toSphere_ne_zero _))
    (measure_ne_top _ _)

/-- The normalized surface measure has full support: nonempty open subsets of `S^n` have positive
measure. -/
instance isOpenPosMeasure_sphereMeasure (n : ℕ) : (sphereMeasure n).IsOpenPosMeasure :=
  Measure.isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))

/-- The constant `c_n = ∫_{S^n} |x - q| dρ_n(x)` of Section 7.1 of [Basso2024], for the base point
`q = e₀` (by `integral_dist_eq_sphereAvgDist` every `q ∈ S^n` gives the same value). -/
noncomputable def sphereAvgDist (n : ℕ) : ℝ :=
  ∫ x, dist (x : EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace.single 0 1) ∂(sphereMeasure n)

section SphereEquiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-- A linear isometry equivalence of `E` restricts to a measurable equivalence of the unit
sphere. -/
private noncomputable def sphereEquiv (A : E ≃ₗᵢ[ℝ] E) : sphere (0 : E) 1 ≃ᵐ sphere (0 : E) 1 :=
  (A.toHomeomorph.subtype fun x ↦ by simp).toMeasurableEquiv

private theorem coe_sphereEquiv (A : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    (sphereEquiv A x : E) = A x :=
  rfl

open scoped Pointwise in
/-- Linear isometries preserve the surface measure `volume.toSphere`: by the cone formula
`Measure.toSphere_apply'`, the cone over `A⁻¹(s)` is the preimage under `A` of the cone over `s`,
and `A` preserves the volume. -/
private theorem measurePreserving_sphereEquiv [FiniteDimensional ℝ E] (A : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereEquiv A) (volume : Measure E).toSphere
      (volume : Measure E).toSphere := by
  refine ⟨(sphereEquiv A).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereEquiv A).measurable hs, Measure.toSphere_apply' _ hs,
    Measure.toSphere_apply' _ ((sphereEquiv A).measurable hs)]
  congr 1
  have key : Ioo (0 : ℝ) 1 • ((↑) '' (sphereEquiv A ⁻¹' s) : Set E) =
      A ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext y
    simp only [Set.mem_smul, mem_image, mem_preimage]
    constructor
    · rintro ⟨t, ht, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨t, ht, _, ⟨_, hx, rfl⟩, by rw [coe_sphereEquiv, map_smul]⟩
    · rintro ⟨t, ht, _, ⟨x, hx, rfl⟩, hy⟩
      refine ⟨t, ht, A.symm (x : E), ⟨(sphereEquiv A).symm x, by simpa using hx, rfl⟩, ?_⟩
      rw [← map_smul, hy, A.symm_apply_apply]
  rw [key]
  exact A.measurePreserving.measure_preimage_emb A.toHomeomorph.measurableEmbedding _

end SphereEquiv

/-- The normalized surface measure is invariant under linear isometries of `ℝ^(n+1)`. -/
theorem integral_comp_linearIsometryEquiv (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :
    ∫ x, h (A (x : EuclideanSpace ℝ (Fin (n + 1)))) ∂(sphereMeasure n) =
      ∫ x, h (x : EuclideanSpace ℝ (Fin (n + 1))) ∂(sphereMeasure n) := by
  have hA : MeasurePreserving (sphereEquiv A) (sphereMeasure n) (sphereMeasure n) := by
    refine ⟨(sphereEquiv A).measurable, ?_⟩
    rw [sphereMeasure, Measure.map_smul _ (sphereEquiv A).measurable.aemeasurable,
      (measurePreserving_sphereEquiv A).map_eq]
  exact hA.integral_comp' fun x ↦ h x

/-- The average distance to a point of the sphere does not depend on the point:
`∫ |x - q| dρ_n(x) = c_n` for every `q ∈ S^n`. -/
theorem integral_dist_eq_sphereAvgDist (n : ℕ) {q : EuclideanSpace ℝ (Fin (n + 1))}
    (hq : q ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ∫ x, dist (x : EuclideanSpace ℝ (Fin (n + 1))) q ∂(sphereMeasure n) = sphereAvgDist n := by
  set e₀ : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1 with he₀
  have hnorm : ‖q‖ = ‖e₀‖ := by
    rw [mem_sphere_zero_iff_norm.1 hq, he₀, PiLp.norm_single, norm_one]
  -- the reflection in the hyperplane orthogonal to `q - e₀` maps `q` to `e₀`
  set A := Submodule.reflection (ℝ ∙ (q - e₀))ᗮ
  have hAq : A q = e₀ := Submodule.reflection_sub hnorm
  have hd : ∀ x : EuclideanSpace ℝ (Fin (n + 1)), dist x q = dist (A x) e₀ := fun x ↦ by
    rw [← hAq, A.dist_map]
  simp_rw [hd]
  exact integral_comp_linearIsometryEquiv n A fun y ↦ dist y e₀

/-- `0 ≤ c_n`. -/
theorem sphereAvgDist_nonneg (n : ℕ) : 0 ≤ sphereAvgDist n := by
  exact integral_nonneg fun _ ↦ dist_nonneg

/-- The distance to a fixed point is integrable on the sphere (it is bounded by `1 + ‖q‖`). -/
private theorem integrable_dist (n : ℕ) (q : EuclideanSpace ℝ (Fin (n + 1))) :
    Integrable (fun x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦ dist x.1 q)
      (sphereMeasure n) := by
  refine Integrable.of_bound (by fun_prop) (1 + ‖q‖) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, dist_eq_norm]
  calc ‖x.1 - q‖ ≤ ‖x.1‖ + ‖q‖ := norm_sub_le _ _
    _ = 1 + ‖q‖ := by rw [mem_sphere_zero_iff_norm.1 x.2]

/-- For unit vectors `x` and `e`, `‖x - e‖ + ‖x + e‖ ≤ 2√2`, since
`‖x - e‖² + ‖x + e‖² = 4` by the parallelogram law. -/
private theorem norm_sub_add_norm_add_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {x e : F} (hx : ‖x‖ = 1) (he : ‖e‖ = 1) :
    ‖x - e‖ + ‖x + e‖ ≤ 2 * √2 := by
  have hpar := parallelogram_law_with_norm ℝ x e
  rw [hx, he] at hpar
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2,
    norm_nonneg (x - e), norm_nonneg (x + e), sq_nonneg (‖x - e‖ - ‖x + e‖)]

/-- `c_n ≤ √2` (the end of the proof of Proposition 7.3 of [Basso2024]). -/
theorem sphereAvgDist_le_sqrt_two (n : ℕ) : sphereAvgDist n ≤ √2 := by
  set e₀ : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1 with he₀
  have hn : ‖e₀‖ = 1 := by rw [he₀, PiLp.norm_single, norm_one]
  have hme : e₀ ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := mem_sphere_zero_iff_norm.2 hn
  have hme' : -e₀ ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_neg, hn]
  -- by symmetry, `c_n = ½ ∫ (‖x - e₀‖ + ‖x + e₀‖) dρ_n(x)`
  have h2 : 2 * sphereAvgDist n = ∫ x, (dist x.1 e₀ + dist x.1 (-e₀)) ∂(sphereMeasure n) := by
    rw [integral_add (integrable_dist n _) (integrable_dist n _),
      integral_dist_eq_sphereAvgDist n hme, integral_dist_eq_sphereAvgDist n hme', two_mul]
  have h3 : ∫ x, (dist x.1 e₀ + dist x.1 (-e₀)) ∂(sphereMeasure n) ≤ 2 * √2 := by
    calc _ ≤ ∫ _, 2 * √2 ∂(sphereMeasure n) :=
          integral_mono ((integrable_dist n _).add (integrable_dist n _)) (integrable_const _)
            fun x ↦ by
              simpa only [Pi.add_apply, dist_eq_norm, sub_neg_eq_add] using
                norm_sub_add_norm_add_le (mem_sphere_zero_iff_norm.1 x.2) hn
      _ = 2 * √2 := by simp
  linarith

end LipschitzExtension
