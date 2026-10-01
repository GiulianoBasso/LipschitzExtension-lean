/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Order.Interval.Set.Basic

/-!
# Conical bicombings

This file defines conical bicombings on metric spaces, reversibility, `σ`-convex sets and
`σ`-convex hulls, as in the introduction and Section 2.2 of [Basso2024bicombings].

A *conical bicombing* on a metric space `X` (following Lang) is a map `σ : X × X × [0, 1] → X`
such that for all `x, y ∈ X` the curve `σ_{xy} = σ(x, y, ·)` is a constant speed geodesic from `x`
to `y`, and the *conical inequality* (1.1) of [Basso2024bicombings]
`d(σ_{xy}(t), σ_{x'y'}(t)) ≤ (1 - t) d(x, x') + t d(y, y')` holds for all `x, y, x', y' ∈ X` and
`t ∈ [0, 1]`. It is *reversible* if `σ_{xy}(t) = σ_{yx}(1 - t)` for all `x, y` and `t ∈ [0, 1]`.

A set `C` is `σ`-convex if `σ_{xy}([0, 1]) ⊆ C` for all `x, y ∈ C`. The *closed `σ`-convex hull*
`\overline{conv}_σ(A)` of `A` is the closure of the smallest `σ`-convex set containing `A`; here it
is `closure (σ.convexHull A)`. We also show that it is the intersection of all closed
`σ`-convex sets containing `A` (the definition used in Descombes' thesis).

## Main definitions

* `ConicalBicombing X`: the conical bicombings on `X`.
* `ConicalBicombing.IsReversible`: `σ` is reversible, i.e. `σ_{xy}(t) = σ_{yx}(1 - t)`.
* `ConicalBicombing.IsConvex`: `σ`-convex sets.
* `ConicalBicombing.convexHull`: the `σ`-convex hull, i.e. the smallest `σ`-convex set containing
  a given set.

## Main statements

* `ConicalBicombing.continuous_toFun`: for fixed `t ∈ [0, 1]`, `(x, y) ↦ σ_{xy}(t)` is continuous.
* `ConicalBicombing.IsConvex.closure`: the closure of a `σ`-convex set is `σ`-convex.
* `ConicalBicombing.closure_convexHull_eq_sInter`: the closed `σ`-convex hull of `A` is the
  intersection of all closed `σ`-convex sets containing `A`.

## Implementation notes

We take `ℝ` as the parameter domain of `σ x y`; only parameters in `[0, 1]` matter (all
conditions are imposed on `[0, 1]` only).

## References

* [G. Basso, *Extending and improving conical bicombings*][Basso2024bicombings]
* D. Descombes, *Spaces with convex geodesic bicombings*, PhD thesis, ETH Zürich, 2015
-/

open Set Metric

namespace LipschitzExtension

/-- A *conical bicombing* on `X`: `σ x y` is a constant speed geodesic from `x` to `y` on
`[0, 1]`, and `d(σ x y t, σ x' y' t) ≤ (1 - t) d(x, x') + t d(y, y')` for `t ∈ [0, 1]`
(inequality (1.1) of [Basso2024bicombings]). -/
structure ConicalBicombing (X : Type*) [PseudoMetricSpace X] where
  /-- The bicombing as a function: `toFun x y t = σ_{xy}(t)`. -/
  toFun : X → X → ℝ → X
  /-- The geodesic `σ_{xy}` starts at `x`. -/
  toFun_zero : ∀ x y, toFun x y 0 = x
  /-- The geodesic `σ_{xy}` ends at `y`. -/
  toFun_one : ∀ x y, toFun x y 1 = y
  /-- `σ_{xy}` is a constant speed geodesic on `[0, 1]`:
  `d(σ_{xy}(s), σ_{xy}(t)) = |s - t| d(x, y)`. -/
  dist_toFun_toFun : ∀ (x y : X) {s t : ℝ}, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
    dist (toFun x y s) (toFun x y t) = |s - t| * dist x y
  /-- The conical inequality `d(σ_{xy}(t), σ_{x'y'}(t)) ≤ (1 - t) d(x, x') + t d(y, y')`. -/
  conical : ∀ (x y x' y' : X) {t : ℝ}, t ∈ Icc (0 : ℝ) 1 →
    dist (toFun x y t) (toFun x' y' t) ≤ (1 - t) * dist x x' + t * dist y y'

namespace ConicalBicombing

/-- A conical bicombing `σ` can be applied as `σ x y t`. -/
instance instCoeFun {X : Type*} [PseudoMetricSpace X] :
    CoeFun (ConicalBicombing X) (fun _ ↦ X → X → ℝ → X) :=
  ⟨ConicalBicombing.toFun⟩

variable {X : Type*} [MetricSpace X] (σ : ConicalBicombing X)

/-- `σ` is *reversible* if `σ_{xy}(t) = σ_{yx}(1 - t)` for all `x, y` and `t ∈ [0, 1]`. -/
def IsReversible : Prop :=
  ∀ (x y : X) {t : ℝ}, t ∈ Icc (0 : ℝ) 1 → σ x y t = σ y x (1 - t)

/-- A set `C` is `σ`-convex if `σ_{xy}([0, 1]) ⊆ C` for all `x, y ∈ C`. -/
def IsConvex (C : Set X) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ t ∈ Icc (0 : ℝ) 1, σ x y t ∈ C

/-- The `σ`-convex hull of `A`: the smallest `σ`-convex set containing `A`. The closed
`σ`-convex hull `\overline{conv}_σ(A)` of the paper is `closure (σ.convexHull A)`. -/
def convexHull (A : Set X) : Set X :=
  ⋂₀ {C | A ⊆ C ∧ σ.IsConvex C}

/-- `d(x, σ_{xy}(t)) = t d(x, y)`. -/
theorem dist_toFun_left (x y : X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist x (σ x y t) = t * dist x y := by
  have h := σ.dist_toFun_toFun x y (left_mem_Icc.2 zero_le_one) ht
  rwa [σ.toFun_zero, zero_sub, abs_neg, abs_of_nonneg ht.1] at h

/-- `d(σ_{xy}(t), y) = (1 - t) d(x, y)`. -/
theorem dist_toFun_right (x y : X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (σ x y t) y = (1 - t) * dist x y := by
  have h := σ.dist_toFun_toFun x y ht (right_mem_Icc.2 zero_le_one)
  rwa [σ.toFun_one, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 ht.2)] at h

/-- The geodesic from `x` to `x` is constant. -/
theorem toFun_self (x : X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : σ x x t = x := by
  have h := σ.dist_toFun_left x x ht
  rw [dist_self, mul_zero] at h
  exact (dist_eq_zero.1 h).symm

/-- The conical inequality against a constant geodesic. -/
theorem dist_toFun_le (x y z : X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (σ x y t) z ≤ (1 - t) * dist x z + t * dist y z := by
  have h := σ.conical x y z z ht
  rwa [σ.toFun_self z ht] at h

/-- For fixed `t ∈ [0, 1]`, `(x, y) ↦ σ_{xy}(t)` is continuous (it is `1`-Lipschitz for the
max metric on `X × X`). -/
theorem continuous_toFun {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Continuous fun p : X × X ↦ σ p.1 p.2 t := by
  refine (LipschitzWith.mk_one fun p q ↦ ?_).continuous
  calc dist (σ p.1 p.2 t) (σ q.1 q.2 t) ≤ (1 - t) * dist p.1 q.1 + t * dist p.2 q.2 :=
        σ.conical _ _ _ _ ht
    _ ≤ (1 - t) * dist p q + t * dist p q :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.2 ht.2))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) ht.1)
    _ = dist p q := by ring

/-- The whole space is `σ`-convex. -/
theorem isConvex_univ : σ.IsConvex univ := by
  exact fun _ _ _ _ _ _ ↦ mem_univ _

/-- Intersections of `σ`-convex sets are `σ`-convex. -/
theorem isConvex_sInter {S : Set (Set X)} (hS : ∀ C ∈ S, σ.IsConvex C) :
    σ.IsConvex (⋂₀ S) := by
  intro x hx y hy t ht
  exact mem_sInter.2 fun C hC ↦ hS C hC x (mem_sInter.1 hx C hC) y (mem_sInter.1 hy C hC) t ht

/-- `A` is contained in its `σ`-convex hull. -/
theorem subset_convexHull (A : Set X) : A ⊆ σ.convexHull A := by
  exact fun _ ha ↦ mem_sInter.2 fun _ hC ↦ hC.1 ha

/-- The `σ`-convex hull is `σ`-convex. -/
theorem isConvex_convexHull (A : Set X) : σ.IsConvex (σ.convexHull A) := by
  exact σ.isConvex_sInter fun _ hC ↦ hC.2

/-- The `σ`-convex hull of `A` is contained in every `σ`-convex set containing `A`. -/
theorem convexHull_subset {A C : Set X} (hC : σ.IsConvex C) (hAC : A ⊆ C) :
    σ.convexHull A ⊆ C := by
  exact sInter_subset_of_mem ⟨hAC, hC⟩

/-- The `σ`-convex hull is monotone. -/
theorem convexHull_mono {A B : Set X} (h : A ⊆ B) : σ.convexHull A ⊆ σ.convexHull B := by
  exact σ.convexHull_subset (σ.isConvex_convexHull B) (h.trans (σ.subset_convexHull B))

/-- The closure of a `σ`-convex set is `σ`-convex (`σ` is continuous in the endpoints). -/
theorem IsConvex.closure {C : Set X} (hC : σ.IsConvex C) : σ.IsConvex (closure C) := by
  intro x hx y hy t ht
  exact map_mem_closure₂ (f := fun a b ↦ σ a b t) (σ.continuous_toFun ht) hx hy
    fun a ha b hb ↦ hC a ha b hb t ht

/-- The closed `σ`-convex hull is `σ`-convex. -/
theorem isConvex_closure_convexHull (A : Set X) : σ.IsConvex (closure (σ.convexHull A)) := by
  exact (σ.isConvex_convexHull A).closure

/-- The closed `σ`-convex hull of `A` is contained in every closed `σ`-convex set containing
`A`. -/
theorem closure_convexHull_subset {A C : Set X} (hC : σ.IsConvex C) (hCc : IsClosed C)
    (hAC : A ⊆ C) : closure (σ.convexHull A) ⊆ C := by
  exact closure_minimal (σ.convexHull_subset hC hAC) hCc

/-- The closed `σ`-convex hull is monotone. -/
theorem closure_convexHull_mono {A B : Set X} (h : A ⊆ B) :
    closure (σ.convexHull A) ⊆ closure (σ.convexHull B) := by
  exact closure_mono (σ.convexHull_mono h)

/-- The closed `σ`-convex hull is the intersection of all closed `σ`-convex sets containing `A`
(the definition in Descombes' thesis). -/
theorem closure_convexHull_eq_sInter (A : Set X) :
    closure (σ.convexHull A) = ⋂₀ {C | A ⊆ C ∧ IsClosed C ∧ σ.IsConvex C} := by
  refine Subset.antisymm (subset_sInter fun C hC ↦ σ.closure_convexHull_subset hC.2.2 hC.2.1 hC.1)
    (sInter_subset_of_mem ⟨(σ.subset_convexHull A).trans subset_closure, isClosed_closure,
      σ.isConvex_closure_convexHull A⟩)

end ConicalBicombing

end LipschitzExtension
