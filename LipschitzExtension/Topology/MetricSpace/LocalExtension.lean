/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.PointwiseLipschitz.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Cauchy
import LipschitzExtension.Topology.EMetricSpace.Lipschitz

/-!
# Reduction to normed spaces via the Kuratowski embedding

All extension theorems of [Basso2024] are proved by constructing an extension `F` of `f` whose
pointwise Lipschitz constant is bounded off `A` and which is continuous at the points of `A`;
Lemma 2.2 of [Basso2024] then shows that `F` is Lipschitz. Lemma 2.2 assumes that the domain is a
Banach space, and the paper reduces to this case via the Kuratowski embedding. As observed in
item 5 of the errata [BassoClaude2026], this reduction needs care: the set `A` need not be closed
in the Banach space `E`, and the construction has to be carried out in a space in which `A` is
closed. The remedy of the errata is to work in `E × ℝ`: two points `x, y` of `X = X × {0}` are
joined by the polygonal path through `(x, ε)` and `(y, ε)`, of length `‖x - y‖ + 2ε`, which meets
`A × {0}` at most in its endpoints.

We implement this reduction as follows. A map `f : X → Y` has the *local extension property* on
`A` with constant `L` (`LocalExtensionProperty A f L`) if for every nontrivial real normed space
`V` into which `X` embeds isometrically (via `ι`) there is `F : V → Y` extending `f` along `ι`,
with pointwise Lipschitz constant at most `L` at all points not in the closure of `ι '' A`, and
satisfying `d(F z, f a) ≤ C d(z, ι a)` for some constant `C`, all `a ∈ A` and all `z` not in the
closure of `ι '' A`. For nonempty `A`, this property yields an `L`-Lipschitz extension `X → Y` of
`f|_A`, for closed `A` (and any `Y`) or for arbitrary `A` when `Y` is complete. The proofs of
Theorems 1.1, 1.2 and 1.5 of [Basso2024] in this library establish the local extension property
for the constructions of the paper and then apply these results.

## Main definitions

* `kuratowski x₀`: the Kuratowski embedding `x ↦ d(x, ·) - d(x₀, ·)` of `X` into the Banach space
  `X →ᵇ ℝ` of bounded continuous functions.
* `LocalExtensionProperty A f L`: the local extension property described above.

## Main statements

* `isometry_kuratowski`: the Kuratowski embedding is an isometry.
* `lipschitzOnWith_comp_invFun`, `comp_invFun_apply`: transport of a map along an isometric
  embedding.
* `exists_lipschitz_extension_of_local`: if `A` is closed and nonempty and `f` has the local
  extension property with constant `L ≥ 0`, then `f|_A` has an `L`-Lipschitz extension `X → Y`.
* `exists_lipschitz_extension_of_local_of_completeSpace`: the same for an arbitrary nonempty `A`
  if `Y` is complete.

## Implementation notes

We use the model space `V = (X →ᵇ ℝ) × ℝ` with the isometric embedding `x ↦ (κ x, 0)`, where `κ`
is the Kuratowski embedding for a base point `x₀ ∈ A`. Mathlib's product carries the maximum of
the two norms instead of the norm `‖v‖ + |s|` of the errata; the argument is the same. Points of
positive height are at positive distance from the image of `A`, so Lemma 2.1 along segments
(`dist_le_of_lipAt_segment`) applies to every segment between two points of positive height.

* If `A` is closed, the extension is `x ↦ F(κ x, 0)`. For `x ∉ A`, the vertical segment from
  `(κ x, 0)` to `(κ x, ε)` stays off the closure of the image of `A`; for `x ∈ A`, we approach
  `(κ x, 0)` from above using `d(F z, f a) ≤ C d(z, ι a)`. In both cases
  `d(F(κ x, 0), F(κ x, ε)) ≤ L ε`, and together with the horizontal segment at height `ε` this
  gives `d(F(κ x, 0), F(κ y, 0)) ≤ L d(x, y) + 2 L ε` for every `ε > 0`.
* If `Y` is complete, the extension is `x ↦ lim_k F(κ x, 1/(k + 1))`, a limit of a Cauchy sequence
  by Lemma 2.1 along vertical segments. It agrees with `f` on `A` by the bound
  `d(F z, f a) ≤ C d(z, ι a)`, and the Lipschitz bound passes to the limit from the horizontal
  segments. Here `A` need not be closed; this version is used for Theorem 1.2 of [Basso2024],
  whose statement does not assume that `A` is closed.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
-/

open Set Metric Filter Topology
open scoped BoundedContinuousFunction

namespace LipschitzExtension

universe u v

section Kuratowski

/-! ### The Kuratowski embedding -/

variable {X : Type u} [MetricSpace X]

/-- The Kuratowski embedding `x ↦ d(x, ·) - d(x₀, ·)` of a metric space into the Banach space of
bounded continuous functions on it (an isometry, see `isometry_kuratowski`). -/
noncomputable def kuratowski (x₀ : X) (x : X) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y ↦ dist x y - dist x₀ y, by fun_prop⟩ (2 * dist x x₀) (by
      intro y z
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 := abs_dist_sub_le x x₀ y
      have h2 := abs_dist_sub_le x x₀ z
      calc |dist x y - dist x₀ y - (dist x z - dist x₀ z)|
          ≤ |dist x y - dist x₀ y| + |dist x z - dist x₀ z| := abs_sub _ _
        _ ≤ dist x x₀ + dist x x₀ := add_le_add h1 h2
        _ = 2 * dist x x₀ := by ring)

@[simp]
theorem kuratowski_apply (x₀ x y : X) : kuratowski x₀ x y = dist x y - dist x₀ y := rfl

/-- The Kuratowski embedding is an isometry. -/
theorem isometry_kuratowski (x₀ : X) : Isometry (kuratowski x₀) := by
  refine Isometry.of_dist_eq fun x x' ↦ le_antisymm ?_ ?_
  · refine (BoundedContinuousFunction.dist_le dist_nonneg).2 fun y ↦ ?_
    simp only [kuratowski_apply, Real.dist_eq]
    have := abs_dist_sub_le x x' y
    calc |dist x y - dist x₀ y - (dist x' y - dist x₀ y)| = |dist x y - dist x' y| := by
          congr 1; ring
      _ ≤ dist x x' := this
  · have := BoundedContinuousFunction.dist_coe_le_dist (f := kuratowski x₀ x)
      (g := kuratowski x₀ x') x'
    simp only [kuratowski_apply, Real.dist_eq, dist_self] at this
    calc dist x x' = |dist x x' - dist x₀ x' - (0 - dist x₀ x')| := by
          rw [show dist x x' - dist x₀ x' - (0 - dist x₀ x') = dist x x' by ring,
            abs_of_nonneg dist_nonneg]
      _ ≤ _ := this

end Kuratowski

section Transfer

/-! ### Transport along isometric embeddings -/

variable {X : Type u} [MetricSpace X] {Y : Type v} [MetricSpace Y]
  {V : Type*} [MetricSpace V]

/-- Transport of a map along an isometric embedding `ι`: if `f` is `K`-Lipschitz on `A`, then
`f ∘ Function.invFun ι` is `K`-Lipschitz on `ι '' A`. -/
theorem lipschitzOnWith_comp_invFun {ι : X → V} (hι : Isometry ι) [Nonempty X] {A : Set X}
    {f : X → Y} {K : NNReal} (hf : LipschitzOnWith K f A) :
    LipschitzOnWith K (f ∘ Function.invFun ι) (ι '' A) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  simp only [Function.comp_apply, Function.leftInverse_invFun hι.injective _]
  rw [hι.edist_eq]
  exact hf ha hb

omit [MetricSpace Y] in
/-- The map `f ∘ Function.invFun ι` extends `f` along an isometric embedding `ι`. -/
theorem comp_invFun_apply {ι : X → V} (hι : Isometry ι) [Nonempty X] (f : X → Y) (x : X) :
    (f ∘ Function.invFun ι) (ι x) = f x := by
  simp [Function.leftInverse_invFun hι.injective x]

end Transfer

section Reduction

/-! ### The reduction -/

variable {X : Type u} [MetricSpace X] {Y : Type v} [MetricSpace Y]

/-- The *local extension property* of `f` on `A` with constant `L`: for every nontrivial real
normed space `V` (in the universe of `X`) and every isometric embedding `ι : X → V` there is
`F : V → Y` with `F (ι a) = f a` for `a ∈ A` and `Lip F(z) ≤ L` at all points `z` with
`0 < infDist z (ι '' A)`, together with a constant `C` such that `d(F z, f a) ≤ C d(z, ι a)` for
all `a ∈ A` and all such `z`. See the module docstring. -/
def LocalExtensionProperty (A : Set X) (f : X → Y) (L : ℝ) : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] (ι : X → V),
    Isometry ι →
    ∃ F : V → Y, (∀ a ∈ A, F (ι a) = f a) ∧
      (∀ z, 0 < infDist z (ι '' A) → LipAt F z L) ∧
      ∃ C : ℝ, ∀ a ∈ A, ∀ z, 0 < infDist z (ι '' A) → dist (F z) (f a) ≤ C * dist z (ι a)

/-- In a nontrivial real normed space, no closed ball is the whole space. -/
theorem compl_closedBall_nonempty {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Nontrivial V] (z : V) (ρ : ℝ) : (closedBall z ρ)ᶜ.Nonempty := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
  refine ⟨z + ((|ρ| + 1) / ‖v‖) • v, ?_⟩
  simp only [mem_compl_iff, mem_closedBall, not_le, dist_self_add_left, norm_smul,
    Real.norm_eq_abs]
  rw [abs_of_pos (div_pos (by positivity) hnv), div_mul_cancel₀ _ hnv.ne']
  linarith [le_abs_self ρ]

/-- The model space `V = (X →ᵇ ℝ) × ℝ` of the reduction. -/
private noncomputable abbrev ModelSpace (X : Type u) [MetricSpace X] : Type u := (X →ᵇ ℝ) × ℝ

/-- The isometric embedding `x ↦ (κ x, 0)` of `X` into the model space, where
`κ = kuratowski x₀`. -/
private noncomputable def modelEmb (x₀ : X) (x : X) : ModelSpace X := (kuratowski x₀ x, 0)

private theorem dist_modelEmb (x₀ x y : X) : dist (modelEmb x₀ x) (modelEmb x₀ y) = dist x y := by
  simp only [modelEmb, Prod.dist_eq, dist_self, (isometry_kuratowski x₀).dist_eq]
  exact max_eq_left dist_nonneg

private theorem isometry_modelEmb (x₀ : X) : Isometry (modelEmb x₀) :=
  Isometry.of_dist_eq (dist_modelEmb x₀)

/-- Points at positive height are at positive distance from the image of `A`. -/
private theorem le_infDist_height (x₀ : X) {A : Set X} (hA : A.Nonempty) (v : X →ᵇ ℝ) {s : ℝ}
    (hs : 0 < s) : s ≤ infDist ((v, s) : ModelSpace X) (modelEmb x₀ '' A) := by
  refine (le_infDist (hA.image _)).2 ?_
  rintro _ ⟨a, -, rfl⟩
  simp only [modelEmb, Prod.dist_eq, Real.dist_eq, sub_zero, abs_of_pos hs]
  exact le_max_right _ _

private theorem dist_height (v : X →ᵇ ℝ) (s s' : ℝ) :
    dist ((v, s) : ModelSpace X) (v, s') = |s - s'| := by
  simp [Prod.dist_eq, Real.dist_eq]

private theorem dist_horizontal (x₀ x y : X) (s : ℝ) :
    dist ((kuratowski x₀ x, s) : ModelSpace X) (kuratowski x₀ y, s) = dist x y := by
  simp only [Prod.dist_eq, dist_self, (isometry_kuratowski x₀).dist_eq]
  exact max_eq_left dist_nonneg

/-- The second coordinate along a segment is a convex combination. -/
private theorem snd_mem_segment {p q : ModelSpace X} {z : ModelSpace X}
    (hz : z ∈ segment ℝ p q) : ∃ θ ∈ Icc (0 : ℝ) 1, z = (1 - θ) • p + θ • q := by
  rw [segment_eq_image] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  exact ⟨θ, hθ, rfl⟩

/-- Along a segment between two points of positive height, all points have positive height. -/
private theorem height_pos_of_mem_segment {p q z : ModelSpace X} (hp : 0 < p.2) (hq : 0 < q.2)
    (hz : z ∈ segment ℝ p q) : 0 < z.2 := by
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := snd_mem_segment hz
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  rcases eq_or_lt_of_le h1 with rfl | h1
  · simpa using hq
  · have : 0 < 1 - θ := by linarith
    positivity

/-- Segment estimate between two points of positive height. -/
private theorem dist_le_of_heights {A : Set X} (x₀ : X) (hA : A.Nonempty) {F : ModelSpace X → Y}
    {L : ℝ} (hF : ∀ z, 0 < infDist z (modelEmb x₀ '' A) → LipAt F z L) {p q : ModelSpace X}
    (hp : 0 < p.2) (hq : 0 < q.2) : dist (F p) (F q) ≤ L * dist p q := by
  refine dist_le_of_lipAt_segment fun z hz ↦ hF z ?_
  have hz2 := height_pos_of_mem_segment hp hq hz
  exact lt_of_lt_of_le hz2 (le_infDist_height x₀ hA z.1 hz2)

/-- **Reduction theorem** (Lemma 2.2 of [Basso2024] together with errata item 5), closed version:
if `A` is closed and nonempty and `f` has the local extension property with constant `L ≥ 0`, then
`f|_A` admits an `L`-Lipschitz extension `X → Y`. -/
theorem exists_lipschitz_extension_of_local {A : Set X} (hA : IsClosed A) (hAne : A.Nonempty)
    {f : X → Y} {L : ℝ} (hL : 0 ≤ L) (hloc : LocalExtensionProperty A f L) :
    ∃ F : X → Y, EqOn F f A ∧ ∀ x y, dist (F x) (F y) ≤ L * dist x y := by
  obtain ⟨x₀, hx₀⟩ := hAne
  obtain ⟨F, hF1, hF2, C, hC⟩ := hloc (ModelSpace X) (modelEmb x₀) (isometry_modelEmb x₀)
  refine ⟨fun x ↦ F (modelEmb x₀ x), fun a ha ↦ hF1 a ha, ?_⟩
  -- vertical estimate: `d(F(x, 0), F(x, ε)) ≤ L ε`
  have hvert : ∀ x : X, ∀ ε : ℝ, 0 < ε →
      dist (F (modelEmb x₀ x)) (F (kuratowski x₀ x, ε)) ≤ L * ε := by
    intro x ε hε
    by_cases hx : x ∈ A
    · -- approach the base point from above
      rw [hF1 x hx]
      refine le_of_forall_pos_le_add fun η hη ↦ ?_
      set s : ℝ := min ε (η / (|C| + 1)) with hs_def
      have hs : 0 < s := lt_min hε (div_pos hη (by positivity))
      have h1 : dist (F (kuratowski x₀ x, s)) (F (kuratowski x₀ x, ε)) ≤ L * ε := by
        have := dist_le_of_heights x₀ ⟨x, hx⟩ hF2 (p := (kuratowski x₀ x, s))
          (q := (kuratowski x₀ x, ε)) hs hε
        rw [dist_height, abs_of_nonpos (by linarith [min_le_left ε (η / (|C| + 1))])] at this
        calc _ ≤ L * -(s - ε) := this
          _ ≤ L * ε := by gcongr; linarith
      have h2 : dist (F (kuratowski x₀ x, s)) (f x) ≤ η := by
        have := hC x hx (kuratowski x₀ x, s)
          (lt_of_lt_of_le hs (le_infDist_height x₀ ⟨x, hx⟩ _ hs))
        have hd : dist ((kuratowski x₀ x, s) : ModelSpace X) (modelEmb x₀ x) = s := by
          simp [modelEmb, Prod.dist_eq, hs.le]
        rw [hd] at this
        calc _ ≤ C * s := this
          _ ≤ |C| * s := by gcongr; exact le_abs_self C
          _ ≤ |C| * (η / (|C| + 1)) := by gcongr; exact min_le_right _ _
          _ ≤ η := by
            rw [mul_div_assoc']
            rw [div_le_iff₀ (by positivity)]
            nlinarith [abs_nonneg C]
      calc dist (f x) (F (kuratowski x₀ x, ε))
          ≤ dist (f x) (F (kuratowski x₀ x, s)) + dist (F (kuratowski x₀ x, s))
              (F (kuratowski x₀ x, ε)) := dist_triangle _ _ _
        _ ≤ η + L * ε := by rw [dist_comm]; exact add_le_add h2 h1
        _ = L * ε + η := by ring
    · -- the whole vertical segment lies off the closure of `A`
      have hpos : 0 < infDist (modelEmb x₀ x) (modelEmb x₀ '' A) := by
        rw [infDist_image (isometry_modelEmb x₀)]
        exact (hA.notMem_iff_infDist_pos ⟨x₀, hx₀⟩).1 hx
      have := dist_le_of_lipAt_segment (G := F) (p := modelEmb x₀ x)
        (q := (kuratowski x₀ x, ε)) (L := L) (fun z hz ↦ hF2 z (by
          obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := snd_mem_segment hz
          rcases eq_or_lt_of_le h0 with rfl | h0
          · simpa [modelEmb] using hpos
          · have hz2 : 0 < ((1 - θ) • modelEmb x₀ x + θ • (kuratowski x₀ x, ε) :
                ModelSpace X).2 := by
              simp only [modelEmb, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_zero,
                zero_add]
              positivity
            exact lt_of_lt_of_le hz2 (le_infDist_height x₀ ⟨x₀, hx₀⟩ _ hz2)))
      have hd : dist (modelEmb x₀ x) ((kuratowski x₀ x, ε) : ModelSpace X) = ε := by
        simp [modelEmb, Prod.dist_eq, Real.dist_eq, abs_of_pos hε, hε.le]
      rwa [hd] at this
  -- combine: vertical, horizontal, vertical
  have hmain : ∀ x y : X, ∀ ε : ℝ, 0 < ε →
      dist (F (modelEmb x₀ x)) (F (modelEmb x₀ y)) ≤ L * dist x y + 2 * L * ε := by
    intro x y ε hε
    have hh := dist_le_of_heights x₀ ⟨x₀, hx₀⟩ hF2 (p := (kuratowski x₀ x, ε))
      (q := (kuratowski x₀ y, ε)) hε hε
    rw [dist_horizontal] at hh
    calc dist (F (modelEmb x₀ x)) (F (modelEmb x₀ y))
        ≤ dist (F (modelEmb x₀ x)) (F (kuratowski x₀ x, ε)) +
            dist (F (kuratowski x₀ x, ε)) (F (kuratowski x₀ y, ε)) +
            dist (F (kuratowski x₀ y, ε)) (F (modelEmb x₀ y)) := dist_triangle4 _ _ _ _
      _ ≤ L * ε + L * dist x y + L * ε := by
          gcongr
          · exact hvert x ε hε
          · rw [dist_comm]; exact hvert y ε hε
      _ = L * dist x y + 2 * L * ε := by ring
  intro x y
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  have := hmain x y (η / (2 * L + 1)) (div_pos hη (by positivity))
  refine this.trans ?_
  gcongr
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-- **Reduction theorem** (Lemma 2.2 of [Basso2024] together with errata item 5), complete
version: if `Y` is complete, `A` is nonempty and `f` has the local extension property with
constant `L ≥ 0`, then `f|_A` admits an `L`-Lipschitz extension `X → Y` (no closedness assumption
on `A`). -/
theorem exists_lipschitz_extension_of_local_of_completeSpace [CompleteSpace Y] {A : Set X}
    (hAne : A.Nonempty) {f : X → Y} {L : ℝ} (hL : 0 ≤ L) (hloc : LocalExtensionProperty A f L) :
    ∃ F : X → Y, EqOn F f A ∧ ∀ x y, dist (F x) (F y) ≤ L * dist x y := by
  obtain ⟨x₀, hx₀⟩ := hAne
  obtain ⟨F, -, hF2, C, hC⟩ := hloc (ModelSpace X) (modelEmb x₀) (isometry_modelEmb x₀)
  -- the approximating sequence `u x k = F (κ x, 1/(k+1))`
  set u : X → ℕ → Y := fun x k ↦ F (kuratowski x₀ x, 1 / ((k : ℝ) + 1)) with hu
  have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k ↦ by positivity
  have hcauchy : ∀ x, CauchySeq (u x) := by
    intro x
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ ↦ L * (1 / ((N : ℝ) + 1))) ?_ ?_
    · intro k l N hk hl
      have := dist_le_of_heights x₀ ⟨x₀, hx₀⟩ hF2 (p := (kuratowski x₀ x, 1 / ((k : ℝ) + 1)))
        (q := (kuratowski x₀ x, 1 / ((l : ℝ) + 1))) (hpos k) (hpos l)
      rw [dist_height] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hL)
      have hk' : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        gcongr
      have hl' : 1 / ((l : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        gcongr
      rw [abs_le]
      constructor <;> linarith [hpos k, hpos l]
    · have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul L
      simpa using this
  have hlim : ∀ x, ∃ y, Tendsto (u x) atTop (𝓝 y) := fun x ↦ cauchySeq_tendsto_of_complete
    (hcauchy x)
  choose G hG using hlim
  refine ⟨G, fun a ha ↦ ?_, fun x y ↦ ?_⟩
  · -- on `A` the limit is `f a`
    refine tendsto_nhds_unique (hG a) ?_
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ ?_)
      ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul |C|).trans (by simp))
    have := hC a ha (kuratowski x₀ a, 1 / ((k : ℝ) + 1))
      (lt_of_lt_of_le (hpos k) (le_infDist_height x₀ ⟨x₀, hx₀⟩ _ (hpos k)))
    have hd : dist ((kuratowski x₀ a, 1 / ((k : ℝ) + 1)) : ModelSpace X) (modelEmb x₀ a) =
        1 / ((k : ℝ) + 1) := by
      have h0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
      simp [modelEmb, Prod.dist_eq, h0]
    rw [hd] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hpos k).le)
  · -- the Lipschitz bound passes to the limit
    have hle : ∀ k, dist (u x k) (u y k) ≤ L * dist x y := by
      intro k
      have := dist_le_of_heights x₀ ⟨x₀, hx₀⟩ hF2 (p := (kuratowski x₀ x, 1 / ((k : ℝ) + 1)))
        (q := (kuratowski x₀ y, 1 / ((k : ℝ) + 1))) (hpos k) (hpos k)
      rwa [dist_horizontal] at this
    exact le_of_tendsto' ((hG x).dist (hG y)) hle

end Reduction

end LipschitzExtension
