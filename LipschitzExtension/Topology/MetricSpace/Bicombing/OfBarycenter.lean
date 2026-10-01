/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Bicombing.Defs
import LipschitzExtension.Topology.MetricSpace.Barycenter.Defs
import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Conical bicombings from barycenter maps

This file proves **Lemma 2.5** of [Basso2024bicombings]: if `β` is a contracting barycenter map on
a metric space `X`, then `σ_β(x, y, t) = β((1 - t) δ_x + t δ_y)` is a reversible conical
bicombing. We prove it for barycenter maps on finitely supported measures (`BarycenterMap`); the
version for barycenter maps on `P₁(X)` follows by restriction
(`ContractingBarycenterMap.toConicalBicombing`).

## Main definitions

* `FinProb.segment`: the measure `(1 - t) δ_x + t δ_y`, for `t ∈ [0, 1]`.
* `BarycenterMap.toConicalBicombing`: the conical bicombing `σ_β` of a barycenter map `β`
  (Lemma 2.5).

## Main statements

* `FinProb.W1_segment_segment`, `FinProb.W1_segment_right`: upper bounds for the `W₁`-distances
  between measures of the form `(1 - t) δ_x + t δ_y`.
* `BarycenterMap.toConicalBicombing_apply`: `σ_β(x, y, t) = β((1 - t) δ_x + t δ_y)` for
  `t ∈ [0, 1]`.
* `BarycenterMap.isReversible_toConicalBicombing`: `σ_β` is reversible (Lemma 2.5).

## Implementation notes

Outside `[0, 1]`, `σ_β(x, y, t)` is evaluated at the projection of `t` onto `[0, 1]`.

## Proof outline

For `s ≤ t`, `d(σ_{xy}(s), σ_{xy}(t)) ≤ W₁((1-s)δ_x + sδ_y, (1-t)δ_x + tδ_y) ≤ (t-s) d(x,y)`
(the paper computes these `W₁`-distances with Lemma 2.3; we only need the upper bounds, which
follow by testing against `1`-Lipschitz functions). Together with `d(x, σ_{xy}(s)) ≤ s d(x, y)` and
`d(σ_{xy}(t), y) ≤ (1 - t) d(x, y)` the triangle inequality forces equality, so `σ_{xy}` is a
constant speed geodesic. Moreover `d(σ_{xy}(t), σ_{xz}(t)) ≤ W₁ ≤ t d(y, z)`, and reversibility
(`(1-t)δ_x + tδ_y = tδ_y + (1-t)δ_x`) gives the conical inequality
`d(σ_{xy}(t), σ_{x'y'}(t)) ≤ d(σ_{xy}(t), σ_{xy'}(t)) + d(σ_{y'x}(1-t), σ_{y'x'}(1-t))`.

## References

* [G. Basso, *Extending and improving conical bicombings*][Basso2024bicombings]
-/

open Set

namespace LipschitzExtension

namespace FinProb

variable {X : Type*}

/-- The measure `(1 - t) δ_x + t δ_y` for `t ∈ [0, 1]`. -/
noncomputable def segment (x y : X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : FinProb X :=
  ofWeights Finset.univ ![x, y] ![1 - t, t]
    (by
      intro i _
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, sub_nonneg]; exact ht.2
      · simp only [Fin.mk_one, Matrix.cons_val_one]; exact ht.1)
    (by simp [Fin.sum_univ_two])

/-- The weights of `segment x y t` are those of `(1 - t) δ_x + t δ_y`. -/
theorem segment_w (x y : X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (segment x y t ht).w = (1 - t) • Finsupp.single x (1 : ℝ) + t • Finsupp.single y 1 := by
  change ∑ i : Fin 2, ![1 - t, t] i • Finsupp.single (![x, y] i) (1 : ℝ) = _
  rw [Fin.sum_univ_two]
  rfl

/-- The atoms of `segment x y t` are among `x` and `y`. -/
theorem support_segment_subset (x y : X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ((segment x y t ht).w.support : Set X) ⊆ {x, y} := by
  classical
  intro z hz
  by_contra hz'
  rw [mem_insert_iff, mem_singleton_iff, not_or] at hz'
  apply Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hz)
  rw [segment_w]
  simp [Ne.symm hz'.1, Ne.symm hz'.2]

private theorem dirac_w (x : X) : (dirac x).w = Finsupp.single x 1 := rfl

private theorem integ_segment (g : X → ℝ) (x y : X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    integ g (segment x y t ht) = g x * (1 - t) + g y * t := by
  rw [segment, integ_ofWeights, Fin.sum_univ_two]
  rfl

/-- `segment x y t` only depends on the value of `t`. -/
private theorem segment_congr (x y : X) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (h : s = t) : segment x y s hs = segment x y t ht := by
  subst h
  rfl

/-- `segment x y 0 = δ_x`. -/
theorem segment_zero (x y : X) : segment x y 0 (by simp) = dirac x := by
  refine ext_w ?_
  rw [segment_w, dirac_w, sub_zero, one_smul, zero_smul, add_zero]

/-- `segment x y 1 = δ_y`. -/
theorem segment_one (x y : X) : segment x y 1 (by simp) = dirac y := by
  refine ext_w ?_
  rw [segment_w, dirac_w, sub_self, zero_smul, zero_add, one_smul]

/-- `(1 - t) δ_x + t δ_y = t δ_y + (1 - t) δ_x`. -/
theorem segment_symm (x y : X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht' : 1 - t ∈ Icc (0 : ℝ) 1) :
    segment x y t ht = segment y x (1 - t) ht' := by
  refine ext_w ?_
  rw [segment_w, segment_w, sub_sub_cancel, add_comm]

variable [PseudoMetricSpace X]

/-- `W₁((1 - s) δ_x + s δ_y, (1 - t) δ_x + t δ_y) ≤ |s - t| d(x, y)`. -/
theorem W1_segment_segment (x y : X) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : W1 (segment x y s hs) (segment x y t ht) ≤ |s - t| * dist x y := by
  refine W1_le fun g hg ↦ ?_
  rw [pairing_eq_integ_sub, integ_segment, integ_segment]
  have h1 := sub_le_dist_of_lipschitz hg x y
  have h2 := sub_le_dist_of_lipschitz hg y x
  rw [dist_comm] at h2
  have h3 : |g x - g y| ≤ dist x y := abs_sub_le_iff.2 ⟨h1, h2⟩
  calc g x * (1 - s) + g y * s - (g x * (1 - t) + g y * t) = (t - s) * (g x - g y) := by ring
    _ ≤ |(t - s) * (g x - g y)| := le_abs_self _
    _ = |s - t| * |g x - g y| := by rw [abs_mul, abs_sub_comm t s]
    _ ≤ |s - t| * dist x y := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)

/-- `W₁((1 - t) δ_x + t δ_y, (1 - t) δ_x + t δ_z) ≤ t d(y, z)`. -/
theorem W1_segment_right (x y z : X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    W1 (segment x y t ht) (segment x z t ht) ≤ t * dist y z := by
  refine W1_le fun g hg ↦ ?_
  rw [pairing_eq_integ_sub, integ_segment, integ_segment]
  have h := sub_le_dist_of_lipschitz hg y z
  calc g x * (1 - t) + g y * t - (g x * (1 - t) + g z * t) = t * (g y - g z) := by ring
    _ ≤ t * dist y z := mul_le_mul_of_nonneg_left h ht.1

end FinProb

namespace BarycenterMap

variable {X : Type*} [MetricSpace X]

private theorem one_sub_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 1 - t ∈ Icc (0 : ℝ) 1 :=
  ⟨sub_nonneg.2 ht.2, sub_le_self _ ht.1⟩

private theorem bary_segment_projIcc (β : BarycenterMap X) (x y : X) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    β.bary (FinProb.segment x y (projIcc (0 : ℝ) 1 zero_le_one t)
      (projIcc (0 : ℝ) 1 zero_le_one t).2) = β.bary (FinProb.segment x y t ht) :=
  congrArg β.bary (FinProb.segment_congr x y _ ht (by rw [projIcc_of_mem zero_le_one ht]))

private theorem dist_bary_segment_le (β : BarycenterMap X) (x y : X) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (β.bary (FinProb.segment x y s hs)) (β.bary (FinProb.segment x y t ht)) ≤
      |s - t| * dist x y :=
  (β.dist_le_W1 _ _).trans (FinProb.W1_segment_segment x y hs ht)

private theorem bary_segment_zero (β : BarycenterMap X) (x y : X)
    (h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1) : β.bary (FinProb.segment x y 0 h0) = x := by
  rw [FinProb.segment_zero, β.bary_dirac]

private theorem bary_segment_one (β : BarycenterMap X) (x y : X)
    (h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1) : β.bary (FinProb.segment x y 1 h1) = y := by
  rw [FinProb.segment_one, β.bary_dirac]

/-- For `s ≤ t` the triangle inequality forces `d(σ_{xy}(s), σ_{xy}(t)) = (t - s) d(x, y)`. -/
private theorem dist_bary_segment_of_le (β : BarycenterMap X) (x y : X) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    dist (β.bary (FinProb.segment x y s hs)) (β.bary (FinProb.segment x y t ht)) =
      (t - s) * dist x y := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have e1 := dist_bary_segment_le β x y h0 hs
  have e2 := dist_bary_segment_le β x y hs ht
  have e3 := dist_bary_segment_le β x y ht h1
  rw [bary_segment_zero, zero_sub, abs_neg, abs_of_nonneg hs.1] at e1
  rw [abs_of_nonpos (sub_nonpos.2 hst)] at e2
  rw [bary_segment_one, abs_of_nonpos (sub_nonpos.2 ht.2)] at e3
  have tri := dist_triangle4 x (β.bary (FinProb.segment x y s hs))
    (β.bary (FinProb.segment x y t ht)) y
  apply le_antisymm <;> linarith

private theorem dist_bary_segment (β : BarycenterMap X) (x y : X) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (β.bary (FinProb.segment x y s hs)) (β.bary (FinProb.segment x y t ht)) =
      |s - t| * dist x y := by
  rcases le_total s t with hst | hst
  · rw [dist_bary_segment_of_le β x y hs ht hst, abs_of_nonpos (sub_nonpos.2 hst), neg_sub]
  · rw [dist_comm, dist_bary_segment_of_le β x y ht hs hst, abs_of_nonneg (sub_nonneg.2 hst)]

/-- The conical inequality, via `d(σ_{xy}(t), σ_{xz}(t)) ≤ t d(y, z)` and reversibility. -/
private theorem dist_bary_segment_conical (β : BarycenterMap X) (x y x' y' : X) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (β.bary (FinProb.segment x y t ht)) (β.bary (FinProb.segment x' y' t ht)) ≤
      (1 - t) * dist x x' + t * dist y y' := by
  have ht' := one_sub_mem_Icc ht
  have h1 : dist (β.bary (FinProb.segment x y t ht)) (β.bary (FinProb.segment x y' t ht)) ≤
      t * dist y y' :=
    (β.dist_le_W1 _ _).trans (FinProb.W1_segment_right x y y' ht)
  have h2 : dist (β.bary (FinProb.segment x y' t ht)) (β.bary (FinProb.segment x' y' t ht)) ≤
      (1 - t) * dist x x' := by
    rw [FinProb.segment_symm x y' ht ht', FinProb.segment_symm x' y' ht ht']
    exact (β.dist_le_W1 _ _).trans (FinProb.W1_segment_right y' x x' ht')
  linarith [dist_triangle (β.bary (FinProb.segment x y t ht))
    (β.bary (FinProb.segment x y' t ht)) (β.bary (FinProb.segment x' y' t ht))]

/-- **Lemma 2.5** of [Basso2024bicombings]: the conical bicombing
`σ_β(x, y, t) = β((1 - t) δ_x + t δ_y)` of a barycenter map `β` (evaluated at the projection of
`t` onto `[0, 1]`). -/
noncomputable def toConicalBicombing (β : BarycenterMap X) : ConicalBicombing X where
  toFun x y t := β.bary (FinProb.segment x y (projIcc (0 : ℝ) 1 zero_le_one t)
    (projIcc (0 : ℝ) 1 zero_le_one t).2)
  toFun_zero x y :=
    (bary_segment_projIcc β x y (left_mem_Icc.2 zero_le_one)).trans (bary_segment_zero β x y _)
  toFun_one x y :=
    (bary_segment_projIcc β x y (right_mem_Icc.2 zero_le_one)).trans (bary_segment_one β x y _)
  dist_toFun_toFun x y _ _ hs ht :=
    (congrArg₂ dist (bary_segment_projIcc β x y hs) (bary_segment_projIcc β x y ht)).trans
      (dist_bary_segment β x y hs ht)
  conical x y x' y' _ ht :=
    (congrArg₂ dist (bary_segment_projIcc β x y ht) (bary_segment_projIcc β x' y' ht)).trans_le
      (dist_bary_segment_conical β x y x' y' ht)

/-- `σ_β(x, y, t) = β((1 - t) δ_x + t δ_y)` for `t ∈ [0, 1]`, where
`FinProb.segment x y t ht` is the measure `(1 - t) δ_x + t δ_y` (`FinProb.segment_w`). -/
theorem toConicalBicombing_apply (β : BarycenterMap X) (x y : X) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    β.toConicalBicombing x y t = β.bary (FinProb.segment x y t ht) :=
  bary_segment_projIcc β x y ht

/-- **Lemma 2.5** of [Basso2024bicombings]: the bicombing of a barycenter map is reversible. -/
theorem isReversible_toConicalBicombing (β : BarycenterMap X) :
    β.toConicalBicombing.IsReversible := by
  intro x y t ht
  rw [toConicalBicombing_apply β x y ht, toConicalBicombing_apply β y x (one_sub_mem_Icc ht),
    FinProb.segment_symm x y ht (one_sub_mem_Icc ht)]

end BarycenterMap

end LipschitzExtension
