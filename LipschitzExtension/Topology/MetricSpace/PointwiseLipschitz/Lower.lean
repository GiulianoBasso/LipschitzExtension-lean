/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.PointwiseLipschitz.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# The lower pointwise Lipschitz constant and lengths of curves

This file proves Lemma 2.4 of Basso–Wenger–Young (*Undistorted fillings in subsets of metric
spaces*), which [Basso2024] cites as a proof of its folklore Lemma 2.1 and uses in the proof of its
Lemma 8.2.

The *lower pointwise Lipschitz constant* of `f : X → Y` at `x` is
`lip f(x) = lim_{r → 0+} ℓ_r f(x)`, where
`ℓ_r f(x) = inf_{0 < s < r} sup_{d(x,y) < s} d(f x, f y) / s`. We encode `lip f(x) ≤ C` by the
predicate `LipLowerLE f x C`. Since `lip f ≤ Lip f`, the upper bound `LipAt f x C` implies
`LipLowerLE f x C` for `C ≥ 0` (`LipAt.lipLowerLE`). (For `C < 0` this fails: `LipAt f x C` holds
at every isolated point `x`, while `LipLowerLE f x C` never holds, take `y = x`.)

**Lemma 2.4 of Basso–Wenger–Young.** If `lip f(x) ≤ C` for all `x ∈ X`, then `f` is continuous
and `ℓ(f ∘ γ) ≤ C ℓ(γ)` for every curve `γ` in `X`. In particular, if `X` is `λ`-quasiconvex,
then `f` is `Cλ`-Lipschitz.

We prove the length estimate for continuous curves of finite length; for `C = 0` this assumption
cannot be dropped (see `eVariationOn_comp_le_of_lipLowerLE`).

## Main definitions

* `LipLowerLE f x C`: the lower pointwise Lipschitz constant `lip f(x)` is at most `C`.
* `IsQuasiconvex lam X`: any two points of `X` are joined by a continuous curve of length at most
  `lam` times their distance.

## Main statements

* `LipAt.lipLowerLE`: `lip f ≤ Lip f` (for bounds `C ≥ 0`).
* `LipLowerLE.continuousAt`: a bound on `lip f(x)` implies continuity at `x`.
* `dist_le_of_lipLowerLE_curve`, `eVariationOn_comp_le_of_lipLowerLE`: Lemma 2.4 of
  Basso–Wenger–Young: `d(f(γ a), f(γ b)) ≤ C ℓ(γ)` and `ℓ(f ∘ γ) ≤ C ℓ(γ)` for every continuous
  curve `γ : [a, b] → X` of finite length.
* `dist_le_of_lipLowerLE_of_lipschitzOn`: the same estimate along `K`-Lipschitz curves.
* `dist_le_of_lipLowerLE_of_isQuasiconvex`: Lemma 2.1 of [Basso2024], in the generality of
  Basso–Wenger–Young: on a `λ`-quasiconvex space, `lip f ≤ C` implies that `f` is
  `Cλ`-Lipschitz.
* `isQuasiconvex_normedSpace`: real normed spaces are `1`-quasiconvex.
* `exists_curve_of_polygonal`: a polygonal path yields a continuous curve of at most the same
  length (used to prove quasiconvexity of simplicial complexes and of boundaries of simplices).

## Proof outline

This is the proof of Basso–Wenger–Young. Continuity: for every `r > 0` there is
`s ∈ (0, r)` with `sup_{d(x,y)<s} d(f x, f y) ≤ 2Cs` (any `C' > C` works). For the length
estimate it suffices to show `d(f(γ 0), f(γ l)) ≤ C ℓ(γ)` for rectifiable `γ : [0, l] → X`
parametrized by arc length (then sum over partitions). Let `C' > C` and
`A = {t ∈ [0, l] | d(f(γ 0), f(γ t)) ≤ C' t}`; `A` is closed and nonempty, so `t = sup A ∈ A`.
If `t < l`, choose `s ∈ (0, l - t)` with `sup_{d(γ t, y) < s} d(f(γ t), f y) ≤ C' s`; as
`d(γ t, γ (t + s')) ≤ s'` for `s' < s`, continuity gives `d(f(γ t), f(γ(t+s))) ≤ C' s`, so
`t + s ∈ A`, a contradiction.

## Implementation notes

Curves are maps `γ : ℝ → X` considered on an interval `[a, b]`, and the length of `γ` is its
variation `eVariationOn γ (Icc a b)`. Instead of reparametrizing by arc length, we prove the core
estimate for a continuous curve `γ : [a, b] → X` whose increments are controlled by a real
function `φ`, i.e. `d(γ s, γ t) ≤ φ t - φ s` for `s ≤ t`. This covers both `K`-Lipschitz curves
(`φ t = K t`) and curves of finite length (`φ` = the variation function
`variationOnFromTo γ [a, b] a`, which need not be known to be continuous). With
`A = {t ∈ [a, b] | d(f(γ a), f(γ t)) ≤ C' (φ t - φ a)}` and `T = sup A`, we get `T ∈ A` from the
monotonicity of `φ` and the continuity of `f ∘ γ`. Given `s ∈ (0, φ b - φ T + ε / C')` as in the
definition of `lip f(γ T) ≤ C`, either `d(γ T, γ b) < s`, whence `d(f(γ T), f(γ b)) ≤ C' s`, or
the first time `t' > T` with `d(γ T, γ t') ≥ s` satisfies `t' ∈ A` (by continuity from the left),
which contradicts `t' > T = sup A`.

## References

* G. Basso, S. Wenger and R. Young, *Undistorted fillings in subsets of metric spaces*, Adv. Math.
  423 (2023), Paper No. 109024
* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open Set Metric Filter Topology

namespace LipschitzExtension

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-! ### The lower pointwise Lipschitz constant -/

/-- `LipLowerLE f x C`: the pointwise *lower* Lipschitz constant
`lip f(x) = lim_{r→0+} inf_{0<s<r} sup_{d(x,y)<s} d(f x, f y)/s` is at most `C`, i.e. for every
`C' > C` and `r > 0` there is `s ∈ (0, r)` with `d(f x, f y) ≤ C' s` whenever `d(x, y) < s`. -/
def LipLowerLE (f : X → Y) (x : X) (C : ℝ) : Prop :=
  ∀ C' > C, ∀ r > 0, ∃ s ∈ Ioo 0 r, ∀ y, dist x y < s → dist (f x) (f y) ≤ C' * s

/-- `lip f ≤ Lip f`: an upper pointwise bound implies a lower one (for `C ≥ 0`; the hypothesis
`0 ≤ C` is necessary, since `LipAt f x C` holds for every `C` at an isolated point `x`, whereas
`LipLowerLE f x C` is false for `C < 0`). -/
theorem LipAt.lipLowerLE {f : X → Y} {x : X} {C : ℝ} (h : LipAt f x C) (hC : 0 ≤ C) :
    LipLowerLE f x C := by
  intro C' hC' r hr
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (h C' hC')
  have hm : 0 < min r ε := lt_min hr hε
  refine ⟨min r ε / 2, ⟨by positivity, by linarith [min_le_left r ε]⟩, fun y hy ↦ ?_⟩
  have hyε : dist y x < ε := by rw [dist_comm]; linarith [min_le_right r ε]
  calc dist (f x) (f y) ≤ C' * dist x y := hball hyε
    _ ≤ C' * (min r ε / 2) := by gcongr; linarith

/-- A bound on the lower pointwise Lipschitz constant implies continuity. -/
theorem LipLowerLE.continuousAt {f : X → Y} {x : X} {C : ℝ} (h : LipLowerLE f x C) :
    ContinuousAt f x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hC' : C < |C| + 1 := by linarith [le_abs_self C]
  have hpos : 0 < |C| + 1 := by positivity
  obtain ⟨s, hs, hball⟩ := h (|C| + 1) hC' (ε / (|C| + 1)) (by positivity)
  refine ⟨s, hs.1, fun y hy ↦ ?_⟩
  rw [dist_comm] at hy ⊢
  calc dist (f x) (f y) ≤ (|C| + 1) * s := hball y hy
    _ < (|C| + 1) * (ε / (|C| + 1)) := by gcongr; exact hs.2
    _ = ε := by field_simp

/-! ### Lemma 2.4 of Basso–Wenger–Young -/

/-- Core of Lemma 2.4 of Basso–Wenger–Young, for a fixed constant `C' > C`: along a continuous
curve `γ : [a, b] → X` whose increments are controlled by a real function `φ`
(`d(γ s, γ t) ≤ φ t - φ s` for `s ≤ t`), we have `d(f(γ a), f(γ b)) ≤ C' (φ b - φ a)`. -/
private theorem dist_le_of_lipLowerLE_aux' {f : X → Y} {C C' : ℝ} (hC : 0 ≤ C) (hC' : C < C')
    {γ : ℝ → X} {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hγc : ContinuousOn γ (Icc a b))
    (hγ : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → dist (γ s) (γ t) ≤ φ t - φ s)
    (hf : ∀ t ∈ Icc a b, LipLowerLE f (γ t) C) :
    dist (f (γ a)) (f (γ b)) ≤ C' * (φ b - φ a) := by
  have hC'0 : 0 < C' := hC.trans_lt hC'
  have hφ : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → φ s ≤ φ t := fun s hs t ht hst ↦ by
    have := hγ s hs t ht hst
    linarith [dist_nonneg (x := γ s) (y := γ t)]
  have hfγ : ContinuousOn (fun t ↦ f (γ t)) (Icc a b) := fun t ht ↦
    ((hf t ht).continuousAt).comp_continuousWithinAt (hγc t ht)
  have hdc : ∀ x : Y, ContinuousOn (fun t ↦ dist x (f (γ t))) (Icc a b) := fun x ↦
    (continuous_const.dist continuous_id).comp_continuousOn hfγ
  set A : Set ℝ := {t ∈ Icc a b | dist (f (γ a)) (f (γ t)) ≤ C' * (φ t - φ a)} with hA
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have haA : a ∈ A := ⟨haI, by simp⟩
  have hAbdd : BddAbove A := ⟨b, fun t ht ↦ ht.1.2⟩
  set T := sSup A with hT
  have hTa : a ≤ T := le_csSup hAbdd haA
  have hTb : T ≤ b := csSup_le ⟨a, haA⟩ fun t ht ↦ ht.1.2
  have hTI : T ∈ Icc a b := ⟨hTa, hTb⟩
  -- `T = sup A ∈ A`, by monotonicity of `φ` and continuity of `f ∘ γ`
  have hTA : T ∈ A := by
    have hS : IsClosed {t ∈ Icc a b | dist (f (γ a)) (f (γ t)) ≤ C' * (φ T - φ a)} :=
      (hdc _).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hAS : A ⊆ {t ∈ Icc a b | dist (f (γ a)) (f (γ t)) ≤ C' * (φ T - φ a)} :=
      fun t ht ↦ ⟨ht.1, ht.2.trans (by gcongr; exact hφ t ht.1 T hTI (le_csSup hAbdd ht))⟩
    exact ⟨hTI, (closure_minimal hAS hS (csSup_mem_closure ⟨a, haA⟩ hAbdd)).2⟩
  -- the step from `T` to `b`
  have hstep : ∀ ε > 0, dist (f (γ T)) (f (γ b)) ≤ C' * (φ b - φ T) + ε := by
    intro ε hε
    have hr : 0 < φ b - φ T + ε / C' := by
      have := hφ T hTI b hbI hTb
      have : 0 < ε / C' := by positivity
      linarith
    obtain ⟨s, hs, hball⟩ := hf T hTI C' hC' (φ b - φ T + ε / C') hr
    by_cases hb : dist (γ T) (γ b) < s
    · calc dist (f (γ T)) (f (γ b)) ≤ C' * s := hball _ hb
        _ ≤ C' * (φ b - φ T + ε / C') := by gcongr; exact hs.2.le
        _ = C' * (φ b - φ T) + ε := by field_simp
    · exfalso
      rw [not_lt] at hb
      -- the first time `t' > T` at which `γ` leaves the open ball `B(γ T, s)`
      set U : Set ℝ := {σ ∈ Icc T b | s ≤ dist (γ T) (γ σ)} with hU
      have hTbsub : Icc T b ⊆ Icc a b := Icc_subset_Icc_left hTa
      have hUc : IsClosed U :=
        (((continuous_const.dist continuous_id).comp_continuousOn hγc).mono
          hTbsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have hbU : b ∈ U := ⟨⟨hTb, le_rfl⟩, hb⟩
      have hUbdd : BddBelow U := ⟨T, fun σ hσ ↦ hσ.1.1⟩
      set t' := sInf U with ht'
      have ht'U : t' ∈ U := hUc.csInf_mem ⟨b, hbU⟩ hUbdd
      have hTt' : T < t' := by
        rcases ht'U.1.1.lt_or_eq with h | h
        · exact h
        · exfalso
          have := ht'U.2
          rw [← h, dist_self] at this
          linarith [hs.1]
      have ht'I : t' ∈ Icc a b := hTbsub ht'U.1
      have hlt : ∀ σ ∈ Ico T t', dist (f (γ T)) (f (γ σ)) ≤ C' * s := by
        intro σ hσ
        apply hball
        by_contra hcon
        rw [not_lt] at hcon
        have hσU : σ ∈ U := ⟨⟨hσ.1, hσ.2.le.trans ht'U.1.2⟩, hcon⟩
        have := csInf_le hUbdd hσU
        linarith [hσ.2]
      -- by continuity from the left
      have ht'bound : dist (f (γ T)) (f (γ t')) ≤ C' * s := by
        have hsub : Icc T t' ⊆ Icc a b := Icc_subset_Icc hTa ht'I.2
        have hW : IsClosed {σ ∈ Icc T t' | dist (f (γ T)) (f (γ σ)) ≤ C' * s} :=
          ((hdc _).mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
        have hsubW : Ico T t' ⊆ {σ ∈ Icc T t' | dist (f (γ T)) (f (γ σ)) ≤ C' * s} :=
          fun σ hσ ↦ ⟨⟨hσ.1, hσ.2.le⟩, hlt σ hσ⟩
        have hcl : t' ∈ closure (Ico T t') := by
          rw [closure_Ico hTt'.ne]
          exact ⟨hTt'.le, le_rfl⟩
        exact (closure_minimal hsubW hW hcl).2
      -- hence `t' ∈ A`, contradicting `t' > T = sup A`
      have ht'A : t' ∈ A := by
        refine ⟨ht'I, ?_⟩
        calc dist (f (γ a)) (f (γ t'))
            ≤ dist (f (γ a)) (f (γ T)) + dist (f (γ T)) (f (γ t')) := dist_triangle _ _ _
          _ ≤ C' * (φ T - φ a) + C' * s := add_le_add hTA.2 ht'bound
          _ ≤ C' * (φ T - φ a) + C' * (φ t' - φ T) := by
              gcongr
              exact ht'U.2.trans (hγ T hTI t' ht'I hTt'.le)
          _ = C' * (φ t' - φ a) := by ring
      have := le_csSup hAbdd ht'A
      linarith
  have hTb' : dist (f (γ T)) (f (γ b)) ≤ C' * (φ b - φ T) := le_of_forall_pos_le_add hstep
  calc dist (f (γ a)) (f (γ b)) ≤ dist (f (γ a)) (f (γ T)) + dist (f (γ T)) (f (γ b)) :=
        dist_triangle _ _ _
    _ ≤ C' * (φ T - φ a) + C' * (φ b - φ T) := add_le_add hTA.2 hTb'
    _ = C' * (φ b - φ a) := by ring

/-- Core of Lemma 2.4 of Basso–Wenger–Young: along a continuous curve `γ : [a, b] → X` whose
increments are controlled by a real function `φ` (`d(γ s, γ t) ≤ φ t - φ s` for `s ≤ t`), we have
`d(f(γ a), f(γ b)) ≤ C (φ b - φ a)` provided `lip f ≤ C` at all points of the curve. -/
private theorem dist_le_of_lipLowerLE_aux {f : X → Y} {C : ℝ} (hC : 0 ≤ C)
    {γ : ℝ → X} {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hγc : ContinuousOn γ (Icc a b))
    (hγ : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → dist (γ s) (γ t) ≤ φ t - φ s)
    (hf : ∀ t ∈ Icc a b, LipLowerLE f (γ t) C) :
    dist (f (γ a)) (f (γ b)) ≤ C * (φ b - φ a) := by
  have htend : Tendsto (fun C' ↦ C' * (φ b - φ a)) (𝓝[>] C) (𝓝 (C * (φ b - φ a))) :=
    ((continuous_id.mul continuous_const).tendsto C).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun C' hC' ↦
    dist_le_of_lipLowerLE_aux' hC hC' hab hγc hγ hf)

/-- **Lemma 2.4 of Basso–Wenger–Young** for Lipschitz curves: along a `K`-Lipschitz curve
`γ : [a, b] → X`, `d(f(γ a), f(γ b)) ≤ C K (b - a)` provided `lip f ≤ C` at all points of the
curve. -/
theorem dist_le_of_lipLowerLE_of_lipschitzOn {f : X → Y} {C : ℝ} (hC : 0 ≤ C) {γ : ℝ → X}
    {a b K : ℝ} (hab : a ≤ b) (_hK : 0 ≤ K)
    (hγ : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (γ s) (γ t) ≤ K * dist s t)
    (hf : ∀ t ∈ Icc a b, LipLowerLE f (γ t) C) :
    dist (f (γ a)) (f (γ b)) ≤ C * K * (b - a) := by
  have hγc : ContinuousOn γ (Icc a b) := (LipschitzOnWith.of_dist_le' hγ).continuousOn
  have h := dist_le_of_lipLowerLE_aux hC (φ := fun t ↦ K * t) hab hγc (fun s hs t ht hst ↦ by
    calc dist (γ s) (γ t) ≤ K * dist s t := hγ s hs t ht
      _ = K * t - K * s := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith)]
        ring) hf
  calc dist (f (γ a)) (f (γ b)) ≤ C * (K * b - K * a) := h
    _ = C * K * (b - a) := by ring

/-- **Lemma 2.4 of Basso–Wenger–Young**: if `lip f ≤ C` at all points of a continuous curve
`γ : [a, b] → X` of finite length `ℓ(γ) = eVariationOn γ [a, b]`, then
`d(f(γ a), f(γ b)) ≤ C ℓ(γ)`. -/
theorem dist_le_of_lipLowerLE_curve {f : X → Y} {C : ℝ} (hC : 0 ≤ C) {γ : ℝ → X} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b)) (hlen : eVariationOn γ (Icc a b) ≠ ⊤)
    (hf : ∀ t ∈ Icc a b, LipLowerLE f (γ t) C) :
    dist (f (γ a)) (f (γ b)) ≤ C * (eVariationOn γ (Icc a b)).toReal := by
  have hbv : LocallyBoundedVariationOn γ (Icc a b) :=
    BoundedVariationOn.locallyBoundedVariationOn hlen
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  -- use the variation function `φ t = ℓ(γ|[a, t])` to control the increments of `γ`
  have h := dist_le_of_lipLowerLE_aux hC (φ := variationOnFromTo γ (Icc a b) a) hab hγ
    (fun s hs t ht hst ↦ by
      rw [variationOnFromTo.sub_right hbv haI ht hs, variationOnFromTo.eq_of_le _ _ hst]
      exact (hbv s t hs ht).dist_le ⟨hs, le_rfl, hst⟩ ⟨ht, hst, le_rfl⟩) hf
  rwa [variationOnFromTo.self, sub_zero, variationOnFromTo.eq_of_le _ _ hab, inter_self] at h

/-- **Lemma 2.4 of Basso–Wenger–Young**: if `lip f ≤ C` at all points of a continuous
rectifiable curve `γ`, then `ℓ(f ∘ γ) ≤ C ℓ(γ)`. (Rectifiability is needed when `C = 0`: a map
with `lip f = 0` can be non-constant along a non-rectifiable curve, e.g. the inverse of the
parametrization of a snowflake curve.) -/
theorem eVariationOn_comp_le_of_lipLowerLE {f : X → Y} {C : ℝ} (hC : 0 ≤ C) {γ : ℝ → X}
    {a b : ℝ} (hγ : ContinuousOn γ (Icc a b)) (hlen : eVariationOn γ (Icc a b) ≠ ⊤)
    (hf : ∀ t ∈ Icc a b, LipLowerLE f (γ t) C) :
    eVariationOn (f ∘ γ) (Icc a b) ≤ ENNReal.ofReal C * eVariationOn γ (Icc a b) := by
  apply iSup_le
  rintro ⟨n, u, hu, us⟩
  calc ∑ i ∈ Finset.range n, edist ((f ∘ γ) (u (i + 1))) ((f ∘ γ) (u i))
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal C * eVariationOn γ (Icc (u i) (u (i + 1))) := by
        gcongr with i hi
        have hsub : Icc (u i) (u (i + 1)) ⊆ Icc a b := Icc_subset_Icc (us i).1 (us (i + 1)).2
        have hfin : eVariationOn γ (Icc (u i) (u (i + 1))) ≠ ⊤ :=
          ne_top_of_le_ne_top hlen (eVariationOn.mono γ hsub)
        have h := dist_le_of_lipLowerLE_curve hC (hu (Nat.le_succ i)) (hγ.mono hsub) hfin
          (fun t ht ↦ hf t (hsub ht))
        rw [Function.comp_apply, Function.comp_apply, edist_comm, edist_dist,
          ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal C * ∑ i ∈ Finset.range n, eVariationOn γ (Icc (u i) (u (i + 1))) := by
        rw [Finset.mul_sum]
    _ = ENNReal.ofReal C * eVariationOn γ (Icc (u 0) (u n)) := by rw [eVariationOn.sum' γ hu]
    _ ≤ ENNReal.ofReal C * eVariationOn γ (Icc a b) := by
        gcongr
        exact eVariationOn.mono γ (Icc_subset_Icc (us 0).1 (us n).2)

/-! ### Quasiconvex spaces -/

/-- `IsQuasiconvex lam X`: the pseudometric space `X` is `lam`-quasiconvex, i.e. any two points
`x, y` are joined by a curve `γ : ℝ → X`, continuous on `[0, 1]`, with `γ 0 = x`, `γ 1 = y` and
length `eVariationOn γ [0, 1]` at most `lam * d(x, y)`. -/
def IsQuasiconvex (lam : ℝ) (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ : ℝ → X, ContinuousOn γ (Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧
    eVariationOn γ (Icc 0 1) ≤ ENNReal.ofReal (lam * dist x y)

/-- **Lemma 2.1** of [Basso2024], in the generality of Lemma 2.4 of Basso–Wenger–Young: on a
`lam`-quasiconvex space, a map with `lip f ≤ C` everywhere (`C ≥ 0`) is `C lam`-Lipschitz. -/
theorem dist_le_of_lipLowerLE_of_isQuasiconvex {lam : ℝ} (hX : IsQuasiconvex lam X) {f : X → Y}
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, LipLowerLE f x C) (x y : X) :
    dist (f x) (f y) ≤ C * lam * dist x y := by
  obtain ⟨γ, hγc, h0, h1, hvar⟩ := hX x y
  have hfin : eVariationOn γ (Icc 0 1) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  have h := dist_le_of_lipLowerLE_curve hC zero_le_one hγc hfin (fun t _ ↦ hf (γ t))
  have hd : dist x y ≤ (eVariationOn γ (Icc 0 1)).toReal := by
    have := BoundedVariationOn.dist_le hfin (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩
      ⟨zero_le_one, le_rfl⟩
    rwa [h0, h1] at this
  -- `ℓ(γ) ≤ λ d(x, y)`; note that `λ d(x, y) < 0` is impossible since `d(x, y) ≤ ℓ(γ)`
  have hv : (eVariationOn γ (Icc 0 1)).toReal ≤ lam * dist x y := by
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvar
    rw [ENNReal.toReal_ofReal'] at h2
    rcases le_or_gt 0 (lam * dist x y) with hpos | hneg
    · rwa [max_eq_left hpos] at h2
    · exfalso
      rw [max_eq_right hneg.le] at h2
      have h3 : dist x y = 0 := le_antisymm (hd.trans h2) dist_nonneg
      rw [h3, mul_zero] at hneg
      exact lt_irrefl _ hneg
  rw [h0, h1] at h
  calc dist (f x) (f y) ≤ C * (eVariationOn γ (Icc 0 1)).toReal := h
    _ ≤ C * (lam * dist x y) := by gcongr
    _ = C * lam * dist x y := by ring

/-- Real normed spaces are `1`-quasiconvex (segments). -/
theorem isQuasiconvex_normedSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsQuasiconvex 1 E := by
  intro x y
  refine ⟨fun t ↦ AffineMap.lineMap x y t, AffineMap.lineMap_continuous.continuousOn,
    by simp, by simp, ?_⟩
  have hL : LipschitzWith (nndist x y) (fun t : ℝ ↦ AffineMap.lineMap x y t) :=
    LipschitzWith.of_dist_le_mul fun s t ↦ by
      rw [dist_lineMap_lineMap, coe_nndist, mul_comm]
  have h := (hL.lipschitzOnWith (s := univ)).comp_eVariationOn_le (g := id)
    (s := Icc (0 : ℝ) 1) (mapsTo_univ _ _)
  rw [eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_one, mul_one] at h
  rw [one_mul, ← edist_dist, edist_nndist]
  exact h

/-- The segment from `a` to `b`, parametrized on `[0, 1]`, has length at most `d(a, b)`. -/
theorem eVariationOn_lineMap_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) :
    eVariationOn (fun t : ℝ ↦ AffineMap.lineMap a b t) (Icc 0 1) ≤ ENNReal.ofReal (dist a b) := by
  have hL : LipschitzWith (nndist a b) (fun t : ℝ ↦ AffineMap.lineMap a b t) :=
    LipschitzWith.of_dist_le_mul fun s t ↦ by
      rw [dist_lineMap_lineMap, coe_nndist, mul_comm]
  have h := (hL.lipschitzOnWith (s := univ)).comp_eVariationOn_le (g := id)
    (s := Icc (0 : ℝ) 1) (mapsTo_univ _ _)
  rw [eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_one, mul_one] at h
  rw [← edist_dist, edist_nndist]
  exact h

/-- A polygonal path `p 0, …, p l` whose segments lie in `C` yields a continuous curve
`γ : [0, 1] → C` from `p 0` to `p l` whose length is at most the length of the path. -/
theorem exists_curve_of_polygonal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (l : ℕ) (p : ℕ → E) (hC0 : p 0 ∈ C)
    (hseg : ∀ i < l, ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap (p i) (p (i + 1)) t ∈ C) :
    ∃ γ : ℝ → E, Continuous γ ∧ γ 0 = p 0 ∧ γ 1 = p l ∧ MapsTo γ (Icc 0 1) C ∧
      eVariationOn γ (Icc 0 1) ≤ ENNReal.ofReal (∑ i ∈ Finset.range l, dist (p i) (p (i + 1))) := by
  induction l with
  | zero =>
    refine ⟨fun _ ↦ p 0, continuous_const, rfl, rfl, fun _ _ ↦ hC0, ?_⟩
    rw [eVariationOn.constant_on (by simp)]
    exact zero_le
  | succ l ih =>
    obtain ⟨γ₁, hc₁, h0₁, h1₁, hm₁, hv₁⟩ := ih fun i hi ↦ hseg i (by omega)
    let γ₂ : ℝ → E := fun t ↦ AffineMap.lineMap (p l) (p (l + 1)) t
    have hc₂ : Continuous γ₂ := AffineMap.lineMap_continuous
    have h0₂ : γ₂ 0 = p l := by simp [γ₂]
    have h1₂ : γ₂ 1 = p (l + 1) := by simp [γ₂]
    refine ⟨fun t ↦ if t ≤ 1 / 2 then γ₁ (2 * t) else γ₂ (2 * t - 1), ?_, ?_, ?_, ?_, ?_⟩
    · refine Continuous.if_le (hc₁.comp (continuous_const.mul continuous_id))
        (hc₂.comp ((continuous_const.mul continuous_id).sub continuous_const)) continuous_id
        continuous_const fun t ht ↦ ?_
      simp only [ht]
      norm_num
      rw [h1₁, h0₂]
    · simp [h0₁]
    · norm_num
      exact h1₂
    · intro t ht
      dsimp only
      split_ifs with h
      · exact hm₁ ⟨by linarith [ht.1], by linarith⟩
      · exact hseg l (by omega) _ ⟨by linarith, by linarith [ht.2]⟩
    · set γ := fun t : ℝ ↦ if t ≤ 1 / 2 then γ₁ (2 * t) else γ₂ (2 * t - 1)
      have hsplit := eVariationOn.Icc_add_Icc γ (s := univ) (a := 0) (b := 1 / 2) (c := 1)
        (by norm_num) (by norm_num) (mem_univ _)
      simp only [Set.univ_inter] at hsplit
      have e1 : eVariationOn γ (Icc 0 (1 / 2)) ≤ eVariationOn γ₁ (Icc 0 1) := by
        rw [eVariationOn.eq_of_eqOn (f := γ) (f' := γ₁ ∘ fun t ↦ 2 * t) (s := Icc 0 (1 / 2))
          fun t ht ↦ ite_eq_left ht.2]
        exact eVariationOn.comp_le_of_monotoneOn γ₁ _ (fun s _ t _ hst ↦ by linarith)
          fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have e2 : eVariationOn γ (Icc (1 / 2) 1) ≤ eVariationOn γ₂ (Icc 0 1) := by
        rw [eVariationOn.eq_of_eqOn (f := γ) (f' := γ₂ ∘ fun t ↦ 2 * t - 1)
          (s := Icc (1 / 2) 1) fun t ht ↦ ?_]
        · exact eVariationOn.comp_le_of_monotoneOn γ₂ _ (fun s _ t _ hst ↦ by linarith)
            fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
        · by_cases h : t ≤ 1 / 2
          · obtain rfl : t = 1 / 2 := le_antisymm h ht.1
            refine (ite_eq_left h).trans ?_
            rw [Function.comp_apply, show (2 : ℝ) * (1 / 2) = 1 by norm_num, sub_self, h1₁, h0₂]
          · exact ite_eq_right h
      calc eVariationOn γ (Icc 0 1)
          = eVariationOn γ (Icc 0 (1 / 2)) + eVariationOn γ (Icc (1 / 2) 1) := hsplit.symm
        _ ≤ ENNReal.ofReal (∑ i ∈ Finset.range l, dist (p i) (p (i + 1))) +
            ENNReal.ofReal (dist (p l) (p (l + 1))) :=
          add_le_add (e1.trans hv₁) (e2.trans (eVariationOn_lineMap_le _ _))
        _ = ENNReal.ofReal (∑ i ∈ Finset.range (l + 1), dist (p i) (p (i + 1))) := by
          rw [Finset.sum_range_succ, ENNReal.ofReal_add
            (Finset.sum_nonneg fun _ _ ↦ dist_nonneg) dist_nonneg]

end LipschitzExtension
