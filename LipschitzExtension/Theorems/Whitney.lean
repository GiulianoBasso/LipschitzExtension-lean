/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Geometry.SimplicialComplex.Basic
import LipschitzExtension.Topology.MetricSpace.WhitneyCovering.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import LipschitzExtension.Topology.MetricSpace.LengthSpace
import LipschitzExtension.Topology.EMetricSpace.Lipschitz

/-!
# A general Whitney-type extension theorem

This file proves Theorem 6.1 of [Basso2024], in the form required by item 5 of the errata
[BassoClaude2026]: let `X` be a length space, `A ⊆ X` closed and `f : A → Y` `1`-Lipschitz. If
`X \ A` admits a covering satisfying `Whitney(n, α, δ, γ)` (multiplicity `n + 1`, `α, γ ≥ 1`,
`0 < δ ≤ 1/2`) and `Y` is an `(n, C)`-simplicial extensor with `C ≥ 1`, then `f` admits a
`100 C α δ⁻¹ γ log₂(n + 2)`-Lipschitz extension `F : X → Y`.

## Main statements

* `exists_lipAt_extension_of_isWhitneyFamily`: the construction, in any metric space `Z` and for
  any nonempty `A ⊆ Z`: the extension is pointwise `100 C α δ⁻¹ γ log₂(n + 2)`-Lipschitz off `A`
  and continuous at `A` in a quantitative way. This is the form used for Theorem 1.1 (via the
  reduction of errata item 5, `exists_lipschitz_extension_of_local`).
* `LipschitzOnWith.extend_isWhitneyFamily_simplicialExtensor`: Theorem 6.1 for length spaces.

## Implementation notes

* As explained in item 5 of the errata, the proof of Theorem 6.1 uses Lemma 2.2 and hence needs
  that points of `X` are joined by curves of length close to their distance. We prove the theorem
  for length spaces (`IsLengthSpace`), with Lemma 2.2 for length spaces
  (`IsLengthSpace.dist_le_of_lipAt_of_continuousAt`); real normed spaces are length spaces
  (`isLengthSpace_normedSpace`).
* We assume `C ≥ 1`. This holds automatically if `n ≥ 1` and `Y` has two points, and some such
  assumption is necessary: for `n = 0`, `A = X = ℝ`, the empty Whitney family and `Y = ℝ` (a
  `(0, 0)`-simplicial extensor), the literal statement would give a `0`-Lipschitz extension of
  `f = id`.
* In the paper's notation the Whitney family has multiplicity `n + 1` (`Whitney(n, α, δ, γ)`); in
  `IsWhitneyFamily` the multiplicity is an explicit argument, here `n + 1`.

## Proof outline

Take the partition of unity of Lemma 3.2 for the Whitney family with multiplicity `m = n + 1` and
`p = 2 log₂(n+2) ≥ 2` (then `2 p m^(1/p) ≤ 4√2 log₂(n+2)`), points `a_i ∈ A` with
`d(a_i, B_i) ≤ (1 + ε₀) r_i`, the nerve `K = {σ | σ ⊆ supp Φ(z) for some z}` (dimension `≤ n`),
the map `Φ(z) = ∑ φ_i(z) e_i ∈ simplex (supp Φ(z))`, and the extension `Ψ` of `e_i ↦ f(a_i)` given
by the simplicial extensor property. Put `F = Ψ ∘ Φ` off `A` and `F = f` on `A`.

* For `z'` near `z`, `supp Φ(z) ⊆ supp Φ(z')` (continuity of the `φ_i`), so `Φ(z), Φ(z')` lie in
  the simplex `σ = supp Φ(z')` of `K`, and
  `d(F z, F z') ≤ C · (max_{i,j∈σ} d(a_i, a_j)/√2) · ‖Φ z - Φ z'‖₂`
  with `‖·‖₂ ≤ ‖·‖₁` (`l2dist_le_sum_abs`) and
  `max d(a_i, a_j) ≤ 2(1+ε₀+α+δ)(γ r_j + d(z,z'))/(1-δ)`.
* Continuity at `A`: with `z ∈ B_j` (so `φ_j(z) > 0`),
  `d(F z, f(a_j)) = d(Ψ Φ z, Ψ e_j) ≤ C max d(a_i,a_j)` (`l2dist ≤ √2` on a simplex,
  `l2dist_le_sqrt_two`), and `d(a_j, a) ≤ (1+ε₀+α) r_j + d(z, a)`, `r_j ≤ d(z, A) ≤ d(z, a)`.

We take `ε₀ = 1`; the resulting constant `8 C (2 + α + δ) γ log₂(n+2) / (δ (1 - δ))` is at most
`56 C α δ⁻¹ γ log₂(n+2)`. Finally Lemma 2.2 for length spaces turns the pointwise bound off `A`
and the continuity at `A` into a global Lipschitz bound.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
-/

open Set Metric Filter Topology

namespace LipschitzExtension

universe u v

/-! ### Auxiliary lemmas -/

/-- `ε`-management for pointwise Lipschitz bounds: if for every `K > T` and all `z'` near `z`
we have `d(F z, F z') ≤ (a + b d(z, z')) K d(z, z')`, then `Lip F(z) ≤ a T`. -/
private theorem lipAt_of_forall_gt {Z Y : Type*} [PseudoMetricSpace Z] [PseudoMetricSpace Y]
    {F : Z → Y} {z : Z} {a b T : ℝ} (ha : 0 ≤ a)
    (h : ∀ K > T, ∀ᶠ z' in 𝓝 z, dist (F z) (F z') ≤ (a + b * dist z z') * K * dist z z') :
    LipAt F z (a * T) := by
  intro L' hL'
  have ha1 : 0 < a + 1 := by linarith
  obtain ⟨η, hη⟩ : ∃ η, η = (L' - a * T) / (a + 1) := ⟨_, rfl⟩
  have hη0 : 0 < η := hη ▸ div_pos (by linarith) ha1
  have haη : a * η < L' - a * T := by
    have e : η * (a + 1) = L' - a * T := by rw [hη]; field_simp
    nlinarith
  have hev : ∀ᶠ z' in 𝓝 z, (a + b * dist z z') * (T + η) < L' := by
    have hc : Continuous fun z' ↦ (a + b * dist z z') * (T + η) := by fun_prop
    have h0 : (a + b * dist z z) * (T + η) < L' := by
      rw [dist_self, mul_zero, add_zero]
      linarith
    exact (hc.tendsto z).eventually_lt_const h0
  filter_upwards [h (T + η) (by linarith), hev] with z' h1 h2
  exact h1.trans (mul_le_mul_of_nonneg_right h2.le dist_nonneg)

/-- `log₂(n + 2) ≥ 1`. -/
private theorem one_le_logb_two_add_two (n : ℕ) : 1 ≤ Real.logb 2 ((n : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity), Real.rpow_one]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- `(n + 2)^(1/p) = √2` for `p = 2 log₂(n+2)`. -/
private theorem rpow_one_div_two_logb (n : ℕ) :
    ((n : ℝ) + 2) ^ (1 / (2 * Real.logb 2 ((n : ℝ) + 2))) = Real.sqrt 2 := by
  have hn2 : (1 : ℝ) < (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hlog : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos hn2
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [Real.rpow_def_of_pos (by linarith), Real.sqrt_eq_rpow, Real.rpow_def_of_pos two_pos,
    Real.logb]
  congr 1
  field_simp

/-- `2 p (n+1)^(1/p) ≤ 4 √2 log₂(n+2)` for `p = 2 log₂(n+2)`. -/
private theorem two_mul_rpow_le (n : ℕ) :
    2 * (2 * Real.logb 2 ((n : ℝ) + 2)) *
        ((n + 1 : ℕ) : ℝ) ^ (1 / (2 * Real.logb 2 ((n : ℝ) + 2))) ≤
      4 * Real.sqrt 2 * Real.logb 2 ((n : ℝ) + 2) := by
  have hℓ := one_le_logb_two_add_two n
  have h1 : ((n + 1 : ℕ) : ℝ) ^ (1 / (2 * Real.logb 2 ((n : ℝ) + 2))) ≤
      ((n : ℝ) + 2) ^ (1 / (2 * Real.logb 2 ((n : ℝ) + 2))) := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) (by push_cast; linarith)
    exact div_nonneg zero_le_one (by linarith)
  rw [rpow_one_div_two_logb] at h1
  calc _ ≤ 2 * (2 * Real.logb 2 ((n : ℝ) + 2)) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = _ := by ring

/-- The final numerical estimate: `C √2 (2 + α + δ) γ X / ((1 - δ) δ) ≤ 100 C α δ⁻¹ γ ℓ`
whenever `X ≤ 4 √2 ℓ`. -/
private theorem final_bound {C α δ γ ℓ X : ℝ} (hC : 0 ≤ C) (hα : 1 ≤ α) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hγ : 1 ≤ γ) (hℓ : 0 ≤ ℓ) (hX : X ≤ 4 * Real.sqrt 2 * ℓ) :
    C * Real.sqrt 2 * (1 + 1 + α + δ) * γ / (1 - δ) * X / δ ≤
      100 * C * α * δ⁻¹ * γ * ℓ := by
  have h1δ : 0 < 1 - δ := by linarith
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hM : (1 + 1 + α + δ) / (1 - δ) ≤ 7 * α := by
    rw [div_le_iff₀ h1δ]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ α) (by linarith : (0 : ℝ) ≤ 1 / 2 - δ)]
  have hM0 : 0 ≤ (1 + 1 + α + δ) / (1 - δ) := div_nonneg (by linarith) h1δ.le
  have hCγ : 0 ≤ C * γ := mul_nonneg hC (by linarith)
  have h1 : Real.sqrt 2 * X ≤ 8 * ℓ := by
    calc Real.sqrt 2 * X ≤ Real.sqrt 2 * (4 * Real.sqrt 2 * ℓ) :=
          mul_le_mul_of_nonneg_left hX hs0
      _ = 4 * (Real.sqrt 2 * Real.sqrt 2) * ℓ := by ring
      _ = 8 * ℓ := by rw [hs]; ring
  have h2 : Real.sqrt 2 * X * ((1 + 1 + α + δ) / (1 - δ)) ≤ 8 * ℓ * (7 * α) :=
    mul_le_mul h1 hM hM0 (by linarith)
  calc C * Real.sqrt 2 * (1 + 1 + α + δ) * γ / (1 - δ) * X / δ
      = C * γ * (Real.sqrt 2 * X * ((1 + 1 + α + δ) / (1 - δ))) / δ := by ring
    _ ≤ C * γ * (8 * ℓ * (7 * α)) / δ := by
        apply div_le_div_of_nonneg_right _ hδ.le
        exact mul_le_mul_of_nonneg_left h2 hCγ
    _ = 56 * C * α * δ⁻¹ * γ * ℓ := by
        field_simp
        ring
    _ ≤ 100 * C * α * δ⁻¹ * γ * ℓ := by
        have : 0 ≤ C * α * δ⁻¹ * γ * ℓ :=
          mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (by linarith))
            (inv_nonneg.mpr hδ.le)) (by linarith)) hℓ
        nlinarith

/-! ### Theorem 6.1 -/

/-- The construction behind **Theorem 6.1**, in an arbitrary metric space `Z`: if `Z \ A` has a
Whitney family of multiplicity `n + 1` and `Y` is an `(n, C)`-simplicial extensor, then a
`1`-Lipschitz map on `A` extends to a map `F` which is pointwise
`100 C α δ⁻¹ γ log₂(n + 2)`-Lipschitz off `A` and satisfies `d(F z, f a) ≤ C' d(z, a)` for all
`a ∈ A` and `z ∉ A`. -/
theorem exists_lipAt_extension_of_isWhitneyFamily {Z : Type u} [MetricSpace Z] {Y : Type v}
    [MetricSpace Y] {A : Set Z} (hA : A.Nonempty) {f : Z → Y} (hf : LipschitzOnWith 1 f A)
    {ι : Type u} {B : ι → Set Z} {r : ι → ℝ} {n : ℕ} {α δ γ : ℝ}
    (hW : IsWhitneyFamily A B r (n + 1) α δ γ)
    (hα : 1 ≤ α) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hγ : 1 ≤ γ) {C : ℝ} (hC : 0 ≤ C)
    (hY : SimplicialExtensor.{u} n C Y) :
    ∃ F : Z → Y, (∀ a ∈ A, F a = f a) ∧
      (∀ z, 0 < infDist z A → LipAt F z (100 * C * α * δ⁻¹ * γ * Real.logb 2 (n + 2))) ∧
      ∃ C' : ℝ, ∀ a ∈ A, ∀ z, 0 < infDist z A → dist (F z) (f a) ≤ C' * dist z a := by
  classical
  have hδ1 : δ < 1 := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  -- Lemma 3.2 with `p = 2 log₂(n + 2)`
  have hℓ := one_le_logb_two_add_two n
  have hp : 1 < 2 * Real.logb 2 ((n : ℝ) + 2) := by linarith
  obtain ⟨φ, hφ0, hφU, hφpos, hφfin, hφsum, hφLip⟩ := hW.exists_partitionOfUnity hA hδ hδ1 hp
  -- the points `a i ∈ A` with `d(x i, a i) < (1 + ε₀) r i` for some `x i ∈ B i` (`ε₀ = 1`)
  have hex : ∀ i, ∃ a ∈ A, ∃ x ∈ B i, dist x a < (1 + 1) * r i := by
    intro i
    obtain ⟨x, hx, hxA⟩ := hW.exists_infDist_lt i (mul_pos one_pos (hW.r_pos i))
    obtain ⟨a, haA, hxa⟩ := (infDist_lt_iff hA).1 hxA
    exact ⟨a, haA, x, hx, by linarith⟩
  choose a haA x hxB hxa using hex
  obtain ⟨M, hM⟩ : ∃ M, M = 1 + 1 + α + δ := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; linarith
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
    have h3 : dist (a i) w ≤ dist (a i) (x i) + dist (x i) b + dist b w :=
      dist_triangle4 _ _ _ _
    rw [dist_comm (a i) (x i), dist_comm b w] at h3
    have e : M * r i = (1 + 1) * r i + α * r i + δ * r i := by rw [hM]; ring
    linarith
  -- hence `d(a i, w) ≤ M d(w, A) / (1 - δ)`
  have key' : ∀ i w, 0 < infDist w A → φ i w ≠ 0 →
      dist (a i) w ≤ M * infDist w A / (1 - δ) := by
    intro i w hw hφ
    obtain ⟨h1, h2⟩ := key i w hw hφ
    rw [le_div_iff₀ h1δ]
    nlinarith [mul_le_mul_of_nonneg_left h2 hM0.le, mul_le_mul_of_nonneg_right h1 h1δ.le]
  -- the nerve of the covering
  obtain ⟨Kn, hKn⟩ : ∃ Kn : Set (Finset ι),
      Kn = {σ : Finset ι | σ.Nonempty ∧ ∃ z, 0 < infDist z A ∧ (↑σ : Set ι) ⊆ {i | φ i z ≠ 0}} :=
    ⟨_, rfl⟩
  have hmemK : ∀ σ : Finset ι, σ.Nonempty → ∀ z, 0 < infDist z A →
      (↑σ : Set ι) ⊆ {i | φ i z ≠ 0} → σ ∈ Kn := by
    intro σ hσ z hz hσz
    rw [hKn]
    exact ⟨hσ, z, hz, hσz⟩
  have hK : IsSComplex n Kn := by
    refine ⟨fun σ hσ ↦ ?_, fun σ hσ ↦ ?_, fun σ hσ τ hτσ hτ ↦ ?_⟩
    · rw [hKn] at hσ
      exact hσ.1
    · rw [hKn] at hσ
      obtain ⟨-, z, hz, hσz⟩ := hσ
      have h1 : (↑σ : Set ι) ⊆ {i | infDist z (B i) < δ * r i} :=
        fun i hi ↦ hφU i z hz (hσz hi)
      have h2 := (Set.encard_le_encard h1).trans (hW.mult_le z hz)
      rw [Set.encard_coe_eq_coe_finsetCard] at h2
      exact_mod_cast h2
    · rw [hKn] at hσ
      obtain ⟨-, z, hz, hσz⟩ := hσ
      exact hmemK τ hτ z hz ((Finset.coe_subset.mpr hτσ).trans hσz)
  -- the simplicial extension `G` of `e i ↦ f (a i)`
  obtain ⟨G, hG1, hG2⟩ := hY ι Kn hK (fun i ↦ f (a i))
  -- the map `Φ z = ∑ φ i z e i`
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Z → (ι →₀ ℝ), Φ = fun z ↦
      if h : 0 < infDist z A then Finsupp.ofSupportFinite (fun i ↦ φ i z) (hφfin z h) else 0 :=
    ⟨_, rfl⟩
  have hΦ : ∀ z, 0 < infDist z A → ∀ i, Φ z i = φ i z := by
    intro z hz i
    rw [hΦdef]
    simp only [hz, ↓reduceDIte]
    rfl
  have hΦsupp : ∀ z, 0 < infDist z A → ∀ σ : Finset ι, {i | φ i z ≠ 0} ⊆ ↑σ →
      (↑(Φ z).support : Set ι) ⊆ ↑σ := by
    intro z hz σ hσ i hi
    apply hσ
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hΦ z hz] at hi
    exact hi
  have hΦmem : ∀ z, 0 < infDist z A → ∀ σ : Finset ι, {i | φ i z ≠ 0} ⊆ ↑σ →
      Φ z ∈ simplex σ := by
    intro z hz σ hσ
    refine ⟨fun i ↦ ?_, hΦsupp z hz σ hσ, ?_⟩
    · rw [hΦ z hz]
      exact hφ0 i z
    · rw [Finset.sum_congr rfl (fun i _ ↦ hΦ z hz i)]
      exact hφsum z hz σ hσ
  -- the extension
  obtain ⟨F, hFdef⟩ : ∃ F : Z → Y, F = fun z ↦ if 0 < infDist z A then G (Φ z) else f z :=
    ⟨_, rfl⟩
  have hFz : ∀ z, 0 < infDist z A → F z = G (Φ z) := fun z hz ↦ by
    rw [hFdef]
    exact ite_eq_left hz
  -- vertex bounds: if `d(a i, w) ≤ R` for all `i ∈ σ`, then `d(f(a i), f(a k)) ≤ (√2 R) √2`
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hvert : ∀ (σ : Finset ι) (w : Z) (R : ℝ), (∀ i ∈ σ, dist (a i) w ≤ R) →
      ∀ i ∈ σ, ∀ k ∈ σ, dist (f (a i)) (f (a k)) ≤ Real.sqrt 2 * R * Real.sqrt 2 := by
    intro σ w R hR i hi k hk
    have h1 := hfa i (a k) (haA k)
    have h2 := dist_triangle (a i) w (a k)
    rw [dist_comm w (a k)] at h2
    have e : Real.sqrt 2 * R * Real.sqrt 2 = 2 * R := by
      rw [mul_comm (Real.sqrt 2) R, mul_assoc, hs, mul_comm]
    rw [e]
    linarith [hR i hi, hR k hk]
  refine ⟨F, fun a' ha' ↦ ?_, fun z hz ↦ ?_, ?_⟩
  · -- `F = f` on `A`
    rw [hFdef]
    have : ¬ 0 < infDist a' A := by
      rw [infDist_zero_of_mem ha']
      exact lt_irrefl 0
    exact ite_eq_right this
  · -- the pointwise Lipschitz bound
    obtain ⟨j, hj⟩ := hW.cover z hz
    have hrj := hW.r_pos j
    have hzA : infDist z A ≤ γ * r j := hW.hd_le j z hj
    have hjz : φ j z ≠ 0 := (hφpos j z hj).ne'
    obtain ⟨X, hX⟩ : ∃ X, X = 2 * (2 * Real.logb 2 ((n : ℝ) + 2)) *
        ((n + 1 : ℕ) : ℝ) ^ (1 / (2 * Real.logb 2 ((n : ℝ) + 2))) := ⟨_, rfl⟩
    have hX0 : 0 ≤ X := by
      rw [hX]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hXle : X ≤ 4 * Real.sqrt 2 * Real.logb 2 ((n : ℝ) + 2) := hX ▸ two_mul_rpow_le n
    have ha0 : 0 ≤ C * Real.sqrt 2 * M * γ * r j / (1 - δ) :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hs0) hM0.le)
        (by linarith)) hrj.le) h1δ.le
    have hmain : LipAt F z (C * Real.sqrt 2 * M * γ * r j / (1 - δ) * (X / (δ * r j))) := by
      apply lipAt_of_forall_gt (b := C * Real.sqrt 2 * M / (1 - δ)) ha0
      intro K hK
      have ev1 := hφLip z j hj K (hX ▸ hK)
      have ev2 : ∀ᶠ z' in 𝓝 z, 0 < infDist z' A :=
        ((continuous_infDist_pt A).tendsto z).eventually_const_lt hz
      -- each `φ i` with `φ i z ≠ 0` is continuous at `z`, hence nonzero near `z`
      have ev3 : ∀ᶠ z' in 𝓝 z, ∀ i ∈ (hφfin z hz).toFinset, φ i z' ≠ 0 := by
        refine (Filter.eventually_all_finset _).2 fun i hi ↦ ?_
        rw [Set.Finite.mem_toFinset] at hi
        have hcont : ContinuousAt (φ i) z := by
          refine LipAt.continuousAt (L := K) (lipAt_of_eventually_le ?_)
          filter_upwards [ev1] with z' hz'
          have := hz' {i}
          rw [Finset.sum_singleton] at this
          rw [Real.dist_eq]
          exact this
        exact hcont.eventually_ne hi
      filter_upwards [ev1, ev2, ev3] with z' hsum hz' hsub
      -- the simplex `σ = supp Φ(z')` contains `Φ z` and `Φ z'`
      have hσz' : {i | φ i z' ≠ 0} ⊆ ↑(hφfin z' hz').toFinset :=
        (hφfin z' hz').coe_toFinset.symm.subset
      have hσz : {i | φ i z ≠ 0} ⊆ ↑(hφfin z' hz').toFinset := by
        intro i hi
        rw [Set.Finite.coe_toFinset]
        exact hsub i ((hφfin z hz).mem_toFinset.mpr hi)
      have hσK : (hφfin z' hz').toFinset ∈ Kn :=
        hmemK _ ⟨j, hσz hjz⟩ z' hz' (hφfin z' hz').coe_toFinset.subset
      -- all points `a i`, `i ∈ σ`, are close to `z'`
      have hzz' : infDist z' A ≤ γ * r j + dist z z' := by
        have := infDist_le_infDist_add_dist (x := z') (y := z) (s := A)
        rw [dist_comm z' z] at this
        linarith
      have hRi : ∀ i ∈ (hφfin z' hz').toFinset,
          dist (a i) z' ≤ M * (γ * r j + dist z z') / (1 - δ) := by
        intro i hi
        refine (key' i z' hz' ((hφfin z' hz').mem_toFinset.mp hi)).trans ?_
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzz' hM0.le) h1δ.le
      have hR0 : 0 ≤ Real.sqrt 2 * (M * (γ * r j + dist z z') / (1 - δ)) :=
        mul_nonneg hs0 (div_nonneg (mul_nonneg hM0.le
          (add_nonneg (mul_nonneg (by linarith) hrj.le) dist_nonneg)) h1δ.le)
      have hG := hG2 _ hσK _ hR0 (hvert _ z' _ hRi) (Φ z) (hΦmem z hz _ hσz) (Φ z')
        (hΦmem z' hz' _ hσz')
      have hl2 : l2dist (Φ z) (Φ z') ≤ ∑ i ∈ (hφfin z' hz').toFinset, |φ i z - φ i z'| := by
        have := l2dist_le_sum_abs (hΦsupp z hz _ hσz) (hΦsupp z' hz' _ hσz')
        simpa only [hΦ z hz, hΦ z' hz'] using this
      rw [hFz z hz, hFz z' hz']
      calc dist (G (Φ z)) (G (Φ z'))
          ≤ C * (Real.sqrt 2 * (M * (γ * r j + dist z z') / (1 - δ))) * l2dist (Φ z) (Φ z') :=
            hG
        _ ≤ C * (Real.sqrt 2 * (M * (γ * r j + dist z z') / (1 - δ))) * (K * dist z z') :=
            mul_le_mul_of_nonneg_left (hl2.trans (hsum _)) (mul_nonneg hC hR0)
        _ = (C * Real.sqrt 2 * M * γ * r j / (1 - δ) +
              C * Real.sqrt 2 * M / (1 - δ) * dist z z') * K * dist z z' := by ring
    refine hmain.mono ?_
    have hrj0 : r j ≠ 0 := hrj.ne'
    have h1δ0 : 1 - δ ≠ 0 := h1δ.ne'
    have hδ0 : δ ≠ 0 := hδ.ne'
    have e : C * Real.sqrt 2 * M * γ * r j / (1 - δ) * (X / (δ * r j)) =
        C * Real.sqrt 2 * (1 + 1 + α + δ) * γ / (1 - δ) * X / δ := by
      rw [hM]
      field_simp
    rw [e]
    exact final_bound hC hα hδ hδ' hγ (by linarith) hXle
  · -- continuity at `A`
    refine ⟨2 * C * M / (1 - δ) + M / (1 - δ) + 1, fun a' ha' z hz ↦ ?_⟩
    obtain ⟨j, hj⟩ := hW.cover z hz
    have hjz : φ j z ≠ 0 := (hφpos j z hj).ne'
    have hza : infDist z A ≤ dist z a' := infDist_le_dist_of_mem ha'
    have hσz : {i | φ i z ≠ 0} ⊆ ↑(hφfin z hz).toFinset :=
      (hφfin z hz).coe_toFinset.symm.subset
    have hjσ : j ∈ (hφfin z hz).toFinset := hσz hjz
    have hσK : (hφfin z hz).toFinset ∈ Kn :=
      hmemK _ ⟨j, hjσ⟩ z hz (hφfin z hz).coe_toFinset.subset
    obtain ⟨R, hR⟩ : ∃ R, R = M * infDist z A / (1 - δ) := ⟨_, rfl⟩
    have hR0 : 0 ≤ R := by
      rw [hR]
      exact div_nonneg (mul_nonneg hM0.le infDist_nonneg) h1δ.le
    have hRi : ∀ i ∈ (hφfin z hz).toFinset, dist (a i) z ≤ R := fun i hi ↦
      hR ▸ key' i z hz ((hφfin z hz).mem_toFinset.mp hi)
    have hG := hG2 _ hσK _ (mul_nonneg hs0 hR0) (hvert _ z R hRi) (Φ z) (hΦmem z hz _ hσz)
      _ (single_mem_simplex hjσ)
    rw [hG1 j] at hG
    have hl2 := l2dist_le_sqrt_two (hΦmem z hz _ hσz) (single_mem_simplex hjσ)
    have h1 : dist (G (Φ z)) (f (a j)) ≤ 2 * C * R := by
      calc dist (G (Φ z)) (f (a j))
          ≤ C * (Real.sqrt 2 * R) * l2dist (Φ z) (Finsupp.single j 1) := hG
        _ ≤ C * (Real.sqrt 2 * R) * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_left hl2 (mul_nonneg hC (mul_nonneg hs0 hR0))
        _ = 2 * C * R := by
            rw [show C * (Real.sqrt 2 * R) * Real.sqrt 2 =
              C * R * (Real.sqrt 2 * Real.sqrt 2) by ring, hs]
            ring
    have h2 : dist (f (a j)) (f a') ≤ R + dist z a' := by
      refine (hfa j a' ha').trans ((dist_triangle _ z _).trans ?_)
      linarith [hRi j hjσ]
    have hRa : R ≤ M / (1 - δ) * dist z a' := by
      rw [hR, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hza hM0.le) h1δ.le
    rw [hFz z hz]
    calc dist (G (Φ z)) (f a') ≤ dist (G (Φ z)) (f (a j)) + dist (f (a j)) (f a') :=
          dist_triangle _ _ _
      _ ≤ 2 * C * R + (R + dist z a') := add_le_add h1 h2
      _ ≤ 2 * C * (M / (1 - δ) * dist z a') + (M / (1 - δ) * dist z a' + dist z a') := by
          have : 2 * C * R ≤ 2 * C * (M / (1 - δ) * dist z a') :=
            mul_le_mul_of_nonneg_left hRa (by linarith)
          linarith
      _ = (2 * C * M / (1 - δ) + M / (1 - δ) + 1) * dist z a' := by ring

end LipschitzExtension

open LipschitzExtension

/-- **Theorem 6.1** (for length spaces, errata item 5; with `C ≥ 1`): let `X` be a length space,
`A ⊆ X` closed and `f` `1`-Lipschitz on `A`. If `X \ A` admits a Whitney family of multiplicity
`n + 1` (`Whitney(n, α, δ, γ)` in the notation of the paper) and `Y` is an `(n, C)`-simplicial
extensor, then `f` extends to a `100 C α δ⁻¹ γ log₂(n + 2)`-Lipschitz map `F : X → Y`. -/
theorem LipschitzOnWith.extend_isWhitneyFamily_simplicialExtensor.{u, v} {X : Type u}
    [MetricSpace X] {Y : Type v} [MetricSpace Y] {A : Set X} {f : X → Y}
    (hf : LipschitzOnWith 1 f A) (hX : IsLengthSpace X) (hA : IsClosed A) {ι : Type u}
    {B : ι → Set X} {r : ι → ℝ} {n : ℕ} {α δ γ : ℝ} (hW : IsWhitneyFamily A B r (n + 1) α δ γ)
    (hα : 1 ≤ α) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hγ : 1 ≤ γ) {C : ℝ}
    (hY : SimplicialExtensor.{u} n C Y) (hC : 1 ≤ C) :
    ∃ F : X → Y,
      LipschitzWith (100 * C * α * δ⁻¹ * γ * Real.logb 2 (n + 2)).toNNReal F ∧ EqOn f F A := by
  have hℓ := one_le_logb_two_add_two n
  have hδi : 1 ≤ δ⁻¹ := by
    rw [one_le_inv₀ hδ]
    linarith
  -- the Lipschitz constant is `≥ 1`
  have hL1 : 1 ≤ 100 * C * α * δ⁻¹ * γ * Real.logb 2 (n + 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hC) hα) hδi) hγ) hℓ
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · exact exists_lipschitzWith_eqOn_empty f _
  · obtain ⟨F, hF1, hF2, C', hC'⟩ :=
      exists_lipAt_extension_of_isWhitneyFamily hAne hf hW hα hδ hδ' hγ (by linarith) hY
    refine ⟨F, LipschitzWith.of_dist_le' ?_, fun a ha ↦ (hF1 a ha).symm⟩
    have hFA : ∀ a ∈ A, ∀ b ∈ A, dist (F a) (F b) ≤ dist a b := by
      intro a ha b hb
      rw [hF1 a ha, hF1 b hb]
      simpa using hf.dist_le_mul a ha b hb
    -- continuity at the points of `A`
    have hcont : ∀ a ∈ A, ContinuousAt F a := by
      intro a ha
      refine LipAt.continuousAt (L := |C'| + 1)
        (lipAt_of_eventually_le (Filter.Eventually.of_forall fun z ↦ ?_))
      rw [dist_comm (F a), dist_comm a, hF1 a ha]
      by_cases hz : 0 < infDist z A
      · exact (hC' a ha z hz).trans
          (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C']) dist_nonneg)
      · have hzA : z ∈ A := by
          rw [hA.mem_iff_infDist_zero hAne]
          exact le_antisymm (not_lt.mp hz) infDist_nonneg
        have h1 := hFA z hzA a ha
        rw [hF1 z hzA, hF1 a ha] at h1
        rw [hF1 z hzA]
        exact h1.trans (le_mul_of_one_le_left dist_nonneg (by linarith [abs_nonneg C']))
    -- Lemma 2.2 for length spaces
    exact hX.dist_le_of_lipAt_of_continuousAt hA hFA hcont hL1
      (fun x hx ↦ hF2 x ((hA.notMem_iff_infDist_pos hAne).1 hx))
