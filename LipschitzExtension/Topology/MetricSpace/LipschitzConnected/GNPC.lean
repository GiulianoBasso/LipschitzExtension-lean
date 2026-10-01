/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.Defs
import LipschitzExtension.Topology.MetricSpace.LipschitzConnected.ConicalExtension
import LipschitzExtension.MeasureTheory.Sphere.Basic
import LipschitzExtension.Topology.MetricSpace.Barycenter.Contracting
import LipschitzExtension.MeasureTheory.Sphere.AvgDist

/-!
# Complete gNPC spaces are Lipschitz `n`-connected

This file proves Proposition 7.3 of [Basso2024]: every complete metric space `Y` of generalized
non-positive curvature (gNPC, Definition 1.3 of [Basso2024]) satisfies `LC(B^(n+1), λ_n)` with
`λ_n = √(1 + c_n²)`, where `c_n = sphereAvgDist n` is the average distance to a point of the unit
sphere `S^n ⊆ ℝ^(n+1)`. In particular, such spaces are Lipschitz `n`-connected with constant `√3`
for every `n`, since `c_n ≤ √2`.

## Main statements

* `IsGNPC.lcBall`: Proposition 7.3 of [Basso2024], `LC(B^(n+1), √(1 + c_n²))`.
* `IsGNPC.lipschitzConnected`: the second part of Proposition 7.3, `LC(n, √3)` for every `n`.
* `IsGNPC.lcBall_one`, `IsGNPC.lcBall_two`: the constants `λ₁ = √(1 + 16/π²)` and `λ₂ = 5/3`,
  which follow from the values `c₁ = 4/π` and `c₂ = 4/3` of Section 7.1 of [Basso2024].

## Implementation notes

The paper normalizes the Lipschitz constant `L` of `f : S^n → Y` to `1` by rescaling `Y`; we
keep `L` instead. In the proof, `Y` is given its Borel σ-algebra (`borelize`), `f` is the
restriction of the given map `ℝ^(n+1) → Y` to the subtype `S^n`, and the push-forward `f_* ρ` of
the normalized volume measure `ρ` of `S^n` is an element of `P₁(Y)`: it is inner regular, as the
image of a finite measure on the compact space `S^n` under a continuous map.

## Proof outline

We follow the paper; the idea to take the tip `p = β(μ)` is due to U. Lang. Let `f : S^n → Y` be
`L`-Lipschitz, let `ρ` be the normalized volume measure of `S^n`, let `β : P₁(Y) → Y` be a
contracting barycenter map (Theorem 2.4 of [Basso2024],
`isGNPC_iff_nonempty_contractingBarycenterMap`), and let `μ = f_* ρ` and `p = β(μ)`. For every
`q ∈ S^n`,
`d(p, f(q)) ≤ W₁(μ, δ_{f(q)}) ≤ ∫ d(f(x), f(q)) dρ(x) ≤ L ∫ |x - q| dρ(x) = L c_n`.
By Lemma 7.4 (`dist_conicalExtension_le`), the conical extension of `f` with tip `p` for the
conical bicombing `σ_β(x, y, t) = β((1 - t) δ_x + t δ_y)` of `β` (Lemma 2.5 of
[Basso2024bicombings], `ContractingBarycenterMap.toConicalBicombing`) is then
`√(L² + L² c_n²) = λ_n L`-Lipschitz. Finally `c_n ≤ √2` (`sphereAvgDist_le_sqrt_two`), so
`λ_n ≤ √3`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso, *Extending and improving conical bicombings*][Basso2024bicombings]
-/

open MeasureTheory Metric Set

namespace LipschitzExtension

/-- Continuous real functions on the unit sphere are integrable for the normalized surface
measure (the sphere is compact). -/
private theorem integrable_sphereMeasure {n : ℕ}
    {φ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → ℝ} (hφ : Continuous φ) :
    Integrable φ (sphereMeasure n) :=
  hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace φ)

section PushForward

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The push-forward `f_* ρ_n ∈ P₁(Y)` of the normalized surface measure `ρ_n` under a continuous
map `f : S^n → Y`. -/
private noncomputable def pushSphere (n : ℕ)
    (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → Y) (hf : Continuous f) : P1 Y where
  toMeasure := (sphereMeasure n).map f
  isProbabilityMeasure := inferInstance
  innerRegular := by
    have := Measure.InnerRegularCompactLTTop.map_of_continuous (μ := sphereMeasure n) hf
    infer_instance
  exists_integrable_dist := by
    obtain ⟨q₀, hq₀⟩ :=
      (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin (n + 1)))) (r := 1)).2
        zero_le_one
    refine ⟨f ⟨q₀, hq₀⟩, ?_⟩
    exact (integrable_map_measure (continuous_id.dist continuous_const).aestronglyMeasurable
      hf.aemeasurable).2 (integrable_sphereMeasure (hf.dist continuous_const))

/-- The main estimate: `W₁(f_* ρ_n, δ_{f(q)}) ≤ L c_n` if `f : S^n → Y` is `L`-Lipschitz and
`q ∈ S^n`. -/
private theorem W1_pushSphere_dirac_le (n : ℕ)
    {f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → Y} (hf : Continuous f) {L : ℝ}
    (hfL : ∀ x y, dist (f x) (f y) ≤ L * dist x y)
    (q : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    P1.W1 (pushSphere n f hf) (P1.dirac (f q)) ≤ L * sphereAvgDist n := by
  refine P1.W1_le fun h hh ↦ ?_
  change ∫ y, h y ∂((sphereMeasure n).map f) - ∫ y, h y ∂(Measure.dirac (f q)) ≤ _
  rw [integral_map hf.aemeasurable hh.continuous.aestronglyMeasurable, integral_dirac]
  have hint : Integrable (fun x ↦ h (f x)) (sphereMeasure n) :=
    integrable_sphereMeasure (hh.continuous.comp hf)
  have hint' : Integrable (fun x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      L * dist (x : EuclideanSpace ℝ (Fin (n + 1))) q) (sphereMeasure n) :=
    integrable_sphereMeasure (continuous_const.mul (continuous_subtype_val.dist continuous_const))
  calc ∫ x, h (f x) ∂(sphereMeasure n) - h (f q)
      = ∫ x, (h (f x) - h (f q)) ∂(sphereMeasure n) := by
        rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
    _ ≤ ∫ x, L * dist (x : EuclideanSpace ℝ (Fin (n + 1))) q ∂(sphereMeasure n) :=
        integral_mono (hint.sub (integrable_const _)) hint' fun x ↦
          (FinProb.sub_le_dist_of_lipschitz hh _ _).trans (hfL x q)
    _ = L * sphereAvgDist n := by
        rw [integral_const_mul, integral_dist_eq_sphereAvgDist n q.2]

end PushForward

/-- **Proposition 7.3** of [Basso2024]: a complete metric space of generalized non-positive
curvature satisfies `LC(B^(n+1), λ_n)` with `λ_n = √(1 + c_n²)`. -/
theorem IsGNPC.lcBall {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (hY : IsGNPC Y) (n : ℕ) :
    LCBall n (√(1 + sphereAvgDist n ^ 2)) Y := by
  borelize Y
  obtain ⟨β⟩ := isGNPC_iff_nonempty_contractingBarycenterMap.1 hY
  intro L hL g hg
  -- the restriction `f` of `g` to the sphere
  let f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → Y := fun x ↦ g x
  have hfL : ∀ x y, dist (f x) (f y) ≤ L * dist x y := fun x y ↦ hg x x.2 y y.2
  have hf : Continuous f := (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩) hfL).continuous
  -- the tip `p = β(f_* ρ_n)` is within `L c_n` of every point of `f(S^n)`
  obtain ⟨p, hp⟩ : ∃ p : Y, ∀ q ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      dist p (g q) ≤ L * sphereAvgDist n := by
    refine ⟨β.toFun (pushSphere n f hf), fun q hq ↦ ?_⟩
    calc dist (β.toFun (pushSphere n f hf)) (g q)
        = dist (β.toFun (pushSphere n f hf)) (β.toFun (P1.dirac (f ⟨q, hq⟩))) := by
          rw [β.toFun_dirac]
      _ ≤ P1.W1 (pushSphere n f hf) (P1.dirac (f ⟨q, hq⟩)) := β.dist_le_W1 _ _
      _ ≤ L * sphereAvgDist n := W1_pushSphere_dirac_le n hf hfL ⟨q, hq⟩
  -- the conical extension with tip `p` (Lemma 7.4)
  refine ⟨conicalExtension β.toConicalBicombing p g,
    fun x hx ↦ conicalExtension_eq_of_mem_sphere _ _ _ hx, fun x hx y hy ↦ ?_⟩
  have key := dist_conicalExtension_le β.toConicalBicombing p hg hp hx hy
  have hsq : √(L ^ 2 + (L * sphereAvgDist n) ^ 2) = √(1 + sphereAvgDist n ^ 2) * L := by
    rw [show L ^ 2 + (L * sphereAvgDist n) ^ 2 = (1 + sphereAvgDist n ^ 2) * L ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hL]
  rwa [hsq] at key

/-- **Proposition 7.3** of [Basso2024] (second part): complete gNPC spaces are Lipschitz
`n`-connected with constant `√3` for every `n`. -/
theorem IsGNPC.lipschitzConnected {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (hY : IsGNPC Y)
    (n : ℕ) : LipschitzConnected n (√3) Y := by
  refine lipschitzConnected_iff_forall_lcBall.2 fun m _ ↦ (hY.lcBall m).mono ?_
  refine Real.sqrt_le_sqrt ?_
  have h2 : sphereAvgDist m ^ 2 ≤ 2 := by
    calc sphereAvgDist m ^ 2 ≤ √2 ^ 2 :=
          pow_le_pow_left₀ (sphereAvgDist_nonneg m) (sphereAvgDist_le_sqrt_two m) 2
      _ = 2 := Real.sq_sqrt (by norm_num)
  linarith

/-- `λ₁ = √(1 + 16/π²)`: complete gNPC spaces satisfy `LC(B², √(1 + 16/π²))`, since
`c₁ = 4/π`. -/
theorem IsGNPC.lcBall_one {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (hY : IsGNPC Y) :
    LCBall 1 (√(1 + 16 / Real.pi ^ 2)) Y := by
  have h := hY.lcBall 1
  rwa [sphereAvgDist_one, div_pow, show (4 : ℝ) ^ 2 = 16 by norm_num] at h

/-- `λ₂ = 5/3`: complete gNPC spaces satisfy `LC(B³, 5/3)`, since `c₂ = 4/3`. -/
theorem IsGNPC.lcBall_two {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (hY : IsGNPC Y) :
    LCBall 2 (5 / 3) Y := by
  have h := hY.lcBall 2
  rw [sphereAvgDist_two] at h
  have e : √(1 + (4 / 3 : ℝ) ^ 2) = 5 / 3 := by
    rw [show (1 : ℝ) + (4 / 3) ^ 2 = (5 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rwa [e] at h

end LipschitzExtension
