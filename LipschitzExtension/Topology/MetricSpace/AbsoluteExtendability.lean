/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Absolute Lipschitz extendability

This file defines the absolute Lipschitz extendability constant `æ(X)` of a metric space `X`
(Definition 1.4 of [Basso2024]): `X` is *absolutely Lipschitz extendable* with constant `L` if for
every metric space `Xᵉ` containing `X` and every Banach space `Y`, every `1`-Lipschitz map
`f : X → Y` extends to an `L`-Lipschitz map `F : Xᵉ → Y`, and `æ(X)` is the smallest such `L`.

The reformulation (1.6) of Theorem 1.5 of [Basso2024], `æ(X) ≤ 1000 log n / log log n` for metric
spaces `X` with at most `n ≥ 3` points (with the constant `1000` of item 1 of the errata
[BassoClaude2026] instead of `600`), is proved in `LipschitzExtension.Theorems.LeeNaorFinite`
(`absLipExtendableWith_of_card_le`, `absLipExtConst_le_of_card_le`).

## Main definitions

* `AbsLipExtendableWith X L`: `X` is absolutely Lipschitz extendable with constant `L`.
* `absLipExtConst X`: the absolute Lipschitz extendability constant `æ(X) ∈ [0, ∞]`.

## Implementation notes

"`Xᵉ` contains `X`" means that there is an isometric embedding `ι : X → Xᵉ`. The spaces `Xᵉ`
and `Y` range over fixed universes, which are universe parameters of `AbsLipExtendableWith` and
`absLipExtConst`. The constant `æ(X)` is defined as the infimum in `ℝ≥0∞` of all `L ≥ 0` for
which `X` is absolutely Lipschitz extendable with constant `L`; it is `∞` if there is no such `L`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
-/

open scoped ENNReal NNReal

namespace LipschitzExtension

/-- `AbsLipExtendableWith X L`: the metric space `X` is absolutely Lipschitz extendable with
constant `L` (Definition 1.4 of [Basso2024]), i.e. for every metric space `Xᵉ` (in `Type u'`)
containing `X` isometrically via `ι` and every real Banach space `Y` (in `Type v'`), every
`1`-Lipschitz map `f : X → Y` extends to an `L`-Lipschitz map `F : Xᵉ → Y`. -/
def AbsLipExtendableWith.{u', v', w'} (X : Type w') [MetricSpace X] (L : ℝ) : Prop :=
  ∀ (Xe : Type u') [MetricSpace Xe] (ι : X → Xe), Isometry ι →
    ∀ (Y : Type v') [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (f : X → Y),
      LipschitzWith 1 f →
        ∃ F : Xe → Y, (∀ x, F (ι x) = f x) ∧ ∀ x y, dist (F x) (F y) ≤ L * dist x y

/-- The absolute Lipschitz extendability constant `æ(X) ∈ [0, ∞]` of Definition 1.4 of
[Basso2024]: the infimum of all `L ≥ 0` such that `X` is absolutely Lipschitz extendable with
constant `L` (and `∞` if there is none). -/
noncomputable def absLipExtConst.{u', v', w'} (X : Type w') [MetricSpace X] : ℝ≥0∞ :=
  ⨅ (L : ℝ≥0) (_ : AbsLipExtendableWith.{u', v'} X L), (L : ℝ≥0∞)

end LipschitzExtension
