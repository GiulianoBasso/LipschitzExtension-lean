/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.LengthSpace
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Riemannian manifolds are length spaces

This file shows that a Riemannian manifold in the sense of Mathlib's `IsRiemannianManifold` (the
distance is the infimum of the lengths of `C¹` paths) is a length space in the sense of
`IsLengthSpace`. This is used to deduce Theorem 1.3 of [Basso2024], which is about Riemannian
manifolds, from the version for length spaces proved in this library.

## Main statements

* `isLengthSpace_of_isRiemannianManifold`: Riemannian manifolds are length spaces.

## Proof outline

Given `ε > 0`, choose a `C¹` path `γ` from `x` to `y` whose Riemannian length
`Manifold.pathELength I γ 0 1` is less than `d(x, y) + ε`
(`Manifold.exists_lt_of_riemannianEDist_lt`). For every partition `u 0 ≤ ⋯ ≤ u k` of `[0, 1]`,
the distance `d(γ (u i), γ (u (i + 1)))` is at most the Riemannian length of `γ` on
`[u i, u (i + 1)]`, and these lengths add up to at most the Riemannian length of `γ` on `[0, 1]`.
Hence the length `eVariationOn γ [0, 1]` of `γ` is less than `d(x, y) + ε`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
-/

open Set Metric Manifold Bundle
open scoped Manifold ContDiff

namespace LipschitzExtension

/-- Riemannian manifolds (in the sense of `IsRiemannianManifold`: the distance is the infimum of
the lengths of `C¹` paths) are length spaces. -/
theorem isLengthSpace_of_isRiemannianManifold {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M] :
    IsLengthSpace M := by
  intro x y ε hε
  have hr : riemannianEDist I x y < ENNReal.ofReal (dist x y + ε) := by
    rw [← IsRiemannianManifold.out (I := I) x y, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  refine ⟨γ, hγ.continuousOn, h0, h1, le_trans ?_ hlen.le⟩
  -- the length of `γ` is at most its Riemannian length
  have htel : ∀ (u : ℕ → ℝ), Monotone u → ∀ k : ℕ,
      ∑ i ∈ Finset.range k, pathELength I γ (u i) (u (i + 1)) = pathELength I γ (u 0) (u k) := by
    intro u hu k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, pathELength_add (hu (Nat.zero_le k)) (hu (Nat.le_succ k))]
  apply iSup_le
  rintro ⟨k, u, hu, us⟩
  calc ∑ i ∈ Finset.range k, edist (γ (u (i + 1))) (γ (u i))
      ≤ ∑ i ∈ Finset.range k, pathELength I γ (u i) (u (i + 1)) := by
        gcongr with i hi
        rw [edist_comm, IsRiemannianManifold.out (I := I)]
        exact riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc (us i).1 (us (i + 1)).2))
          rfl rfl (hu (Nat.le_succ i))
    _ = pathELength I γ (u 0) (u k) := htel u hu k
    _ ≤ pathELength I γ 0 1 := pathELength_mono (us 0).1 (us k).2

end LipschitzExtension
