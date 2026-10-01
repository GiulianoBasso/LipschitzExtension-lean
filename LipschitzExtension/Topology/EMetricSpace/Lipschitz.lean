/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Trivial cases of Lipschitz extension problems

The extension theorems of this library are stated in the form of Mathlib's
`LipschitzOnWith.extend_real`: a map `f : X → Y` which is Lipschitz on `A ⊆ X` has an extension
`F : X → Y`, i.e. `∃ F, LipschitzWith K F ∧ EqOn f F A`. This file collects the trivial cases of
such statements, which allow us to avoid side conditions such as `[Nonempty Y]`.

## Main results

* `exists_lipschitzWith_eqOn_of_subsingleton`: maps into a subsingleton extend with any constant.
* `exists_lipschitzWith_eqOn_empty`: every map has a `K`-Lipschitz "extension" from `∅`.
* `exists_lipschitzWith_eqOn_of_nonempty`: to find an extension one may assume that `Y` is
  nonempty.
-/

open Set NNReal

namespace LipschitzExtension

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- Every map into a subsingleton is `K`-Lipschitz for every `K`, so it is its own extension. -/
theorem exists_lipschitzWith_eqOn_of_subsingleton [Subsingleton Y] (f : X → Y) (A : Set X)
    (K : ℝ≥0) : ∃ F : X → Y, LipschitzWith K F ∧ EqOn f F A :=
  ⟨f, fun x y ↦ by simp [Subsingleton.elim (f x) (f y)], fun _ _ ↦ rfl⟩

/-- Every map `f : X → Y` has a `K`-Lipschitz extension from the empty set. -/
theorem exists_lipschitzWith_eqOn_empty (f : X → Y) (K : ℝ≥0) :
    ∃ F : X → Y, LipschitzWith K F ∧ EqOn f F ∅ := by
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y⟩⟩
  · -- if `Y` is empty, so is `X`, and `f` itself works
    exact ⟨f, fun x ↦ isEmptyElim (f x), eqOn_empty _ _⟩
  · exact ⟨fun _ ↦ y, LipschitzWith.const' y, eqOn_empty _ _⟩

/-- To construct an extension of `f : X → Y` one may assume that `Y` is nonempty. -/
theorem exists_lipschitzWith_eqOn_of_nonempty {K : ℝ≥0} {A : Set X} {f : X → Y}
    (h : Nonempty Y → ∃ F : X → Y, LipschitzWith K F ∧ EqOn f F A) :
    ∃ F : X → Y, LipschitzWith K F ∧ EqOn f F A := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · -- if `Y` is empty, so is `X`, and `f` itself works
    exact ⟨f, fun x ↦ isEmptyElim (f x), fun _ _ ↦ rfl⟩
  · exact h hY

end LipschitzExtension
