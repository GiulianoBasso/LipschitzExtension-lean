/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Algebra.Affine

/-!
# Pointwise Lipschitz constants

For a map `f : X → Y` between pseudometric spaces, the *(upper) pointwise Lipschitz constant* of
`f` at `x` is `Lip f(x) = limsup_{x' → x} d(f x, f x') / d(x, x')` (Section 2.2 of [Basso2024]).
Instead of working with this `limsup` directly, we work with the predicate `LipAt f x L`, meaning
`Lip f(x) ≤ L`: for every `L' > L` we have `d(f x, f x') ≤ L' d(x, x')` for all `x'` close to `x`.
Its relative version `LipAtWithin f s x L` only takes the points `x' ∈ s` into account.

The main result of this file is the folklore Lemma 2.1 of [Basso2024] along segments: if the
pointwise Lipschitz constant of a map `G` is at most `L` at every point of a segment `[p, q]` of a
real normed space, then `d(G p, G q) ≤ L ‖p - q‖`. This is the form of Lemma 2.1 used in the proof
of Lemma 2.2 (`dist_le_of_lipAt_of_continuousAt`) and in the reduction of item 5 of the errata
[BassoClaude2026] (`exists_lipschitz_extension_of_local`). Lemma 2.1 for quasiconvex spaces and
for length spaces is proved in `LipschitzExtension.Topology.MetricSpace.LengthSpace`.

## Main definitions

* `LipAt f x L`: the upper pointwise Lipschitz constant `Lip f(x)` is at most `L`.
* `LipAtWithin f s x L`: the same, computed within the set `s`.

## Main statements

* `LipAtWithin.continuousWithinAt`, `LipAt.continuousAt`: a pointwise Lipschitz bound implies
  continuity.
* `lipAt_of_eventually_le`: a Lipschitz estimate near `x` bounds `Lip f(x)`.
* `dist_le_of_lipAtWithin_Icc`: Lemma 2.1 of [Basso2024] on an interval of `ℝ`.
* `dist_le_of_lipAtWithin_segment`, `dist_le_of_lipAt_segment`: Lemma 2.1 of [Basso2024] along a
  segment of a real normed space.

## Proof outline

For `dist_le_of_lipAtWithin_Icc`, fix `ε > 0` and let `S = {t | d(g a, g t) ≤ (L + ε) (t - a)}`.
The set `S ∩ [a, b]` is closed (by continuity of `g`) and contains `a`, and for every
`x ∈ S ∩ [a, b)` the set `S` contains a right neighborhood of `x` (by the pointwise bound at `x`
and the triangle inequality). By real induction (`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`)
we get `[a, b] ⊆ S`; finally let `ε → 0`. The version for segments follows by composing with the
affine parametrization `t ↦ AffineMap.lineMap p q t`, which multiplies distances by `‖p - q‖`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* [G. Basso and Claude, *Errata to the single-author papers of Giuliano Basso*][BassoClaude2026]
-/

open Filter Topology Set Metric

namespace LipschitzExtension

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- `LipAtWithin f s x L` means that the upper pointwise Lipschitz constant of `f` at `x`,
computed within `s`, is at most `L`: for every `L' > L` we have `d(f x, f x') ≤ L' d(x, x')` for
all `x' ∈ s` close to `x`. -/
def LipAtWithin (f : X → Y) (s : Set X) (x : X) (L : ℝ) : Prop :=
  ∀ L' > L, ∀ᶠ x' in 𝓝[s] x, dist (f x) (f x') ≤ L' * dist x x'

/-- `LipAt f x L` means that the upper pointwise Lipschitz constant
`Lip f(x) = limsup_{x' → x} d(f x, f x') / d(x, x')` is at most `L`: for every `L' > L` we have
`d(f x, f x') ≤ L' d(x, x')` for all `x'` close to `x`. -/
def LipAt (f : X → Y) (x : X) (L : ℝ) : Prop :=
  ∀ L' > L, ∀ᶠ x' in 𝓝 x, dist (f x) (f x') ≤ L' * dist x x'

theorem LipAt.lipAtWithin {f : X → Y} {x : X} {L : ℝ} (h : LipAt f x L) (s : Set X) :
    LipAtWithin f s x L := fun L' hL' ↦ nhdsWithin_le_nhds (h L' hL')

theorem LipAtWithin.mono_set {f : X → Y} {s t : Set X} {x : X} {L : ℝ} (h : LipAtWithin f t x L)
    (hst : s ⊆ t) : LipAtWithin f s x L := fun L' hL' ↦ nhdsWithin_mono x hst (h L' hL')

theorem LipAt.mono {f : X → Y} {x : X} {L L₂ : ℝ} (h : LipAt f x L) (hL : L ≤ L₂) :
    LipAt f x L₂ := fun L' hL' ↦ h L' (lt_of_le_of_lt hL hL')

theorem LipAtWithin.mono {f : X → Y} {s : Set X} {x : X} {L L₂ : ℝ} (h : LipAtWithin f s x L)
    (hL : L ≤ L₂) : LipAtWithin f s x L₂ := fun L' hL' ↦ h L' (lt_of_le_of_lt hL hL')

/-- A pointwise Lipschitz bound within `s` at `x` implies continuity within `s` at `x`. -/
theorem LipAtWithin.continuousWithinAt {f : X → Y} {s : Set X} {x : X} {L : ℝ}
    (h : LipAtWithin f s x L) : ContinuousWithinAt f s x := by
  have hL : L < |L| + 1 := by linarith [le_abs_self L]
  have h1 := h (|L| + 1) hL
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  have h2 : Tendsto (fun x' ↦ (|L| + 1) * dist x' x) (𝓝[s] x) (𝓝 0) := by
    have : Tendsto (fun x' ↦ dist x' x) (𝓝[s] x) (𝓝 0) := by
      have := ((tendsto_id (x := 𝓝 x)).dist (tendsto_const_nhds (x := x))).mono_left
        (nhdsWithin_le_nhds (s := s))
      simpa using this
    simpa using this.const_mul (|L| + 1)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ h2
  filter_upwards [h1] with x' hx'
  rw [dist_comm (f x'), dist_comm x']
  exact hx'

/-- A pointwise Lipschitz bound at `x` implies continuity at `x`. -/
theorem LipAt.continuousAt {f : X → Y} {x : X} {L : ℝ} (h : LipAt f x L) : ContinuousAt f x := by
  have := (h.lipAtWithin univ).continuousWithinAt
  rwa [continuousWithinAt_univ] at this

/-- If `d(f x, f x') ≤ K d(x, x')` for all `x'` near `x`, then `Lip f (x) ≤ K`. -/
theorem lipAt_of_eventually_le {f : X → Y} {x : X} {K : ℝ}
    (h : ∀ᶠ x' in 𝓝 x, dist (f x) (f x') ≤ K * dist x x') : LipAt f x K := by
  intro L' hL'
  filter_upwards [h] with x' hx'
  exact hx'.trans (mul_le_mul_of_nonneg_right hL'.le dist_nonneg)

/-- **Lemma 2.1** of [Basso2024] on an interval: if the pointwise Lipschitz constant of
`g : ℝ → Y` within `[a, b]` is at most `L` at every point of `[a, b]`, then
`d(g a, g b) ≤ L (b - a)`. -/
theorem dist_le_of_lipAtWithin_Icc {g : ℝ → Y} {a b L : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Icc a b, LipAtWithin g (Icc a b) t L) : dist (g a) (g b) ≤ L * (b - a) := by
  have hcont : ContinuousOn g (Icc a b) := fun t ht ↦ (h t ht).continuousWithinAt
  -- main claim for a fixed `ε > 0`
  have key : ∀ ε > 0, dist (g a) (g b) ≤ (L + ε) * (b - a) := by
    intro ε hε
    set S : Set ℝ := {t | dist (g a) (g t) ≤ (L + ε) * (t - a)} with hS
    have hclosed : IsClosed (S ∩ Icc a b) := by
      have hc : ContinuousOn (fun t ↦ (L + ε) * (t - a) - dist (g a) (g t)) (Icc a b) := by
        fun_prop
      have := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := (0 : ℝ)))
      convert this using 1
      ext t
      simp only [hS, mem_inter_iff, mem_preimage, mem_Ici, sub_nonneg, Set.mem_ofPred_eq]
      tauto
    have haS : a ∈ S := by simp [hS]
    have hstep : ∀ x ∈ S ∩ Ico a b, S ∈ 𝓝[>] x := by
      rintro x ⟨hxS, hxa, hxb⟩
      have h1 := h x ⟨hxa, hxb.le⟩ (L + ε) (by linarith)
      have h2 : ∀ᶠ t in 𝓝[>] x, dist (g x) (g t) ≤ (L + ε) * dist x t := by
        have hsub : 𝓝[Ioo x b] x ≤ 𝓝[Icc a b] x :=
          nhdsWithin_mono x (fun t ht ↦ ⟨hxa.trans ht.1.le, ht.2.le⟩)
        have heq : 𝓝[Ioo x b] x = 𝓝[>] x := nhdsWithin_Ioo_eq_nhdsGT hxb
        rw [← heq]
        exact hsub h1
      filter_upwards [h2, self_mem_nhdsWithin] with t ht hxt
      have hxt' : x < t := hxt
      simp only [hS, Set.mem_ofPred_eq] at hxS ⊢
      calc dist (g a) (g t) ≤ dist (g a) (g x) + dist (g x) (g t) := dist_triangle _ _ _
        _ ≤ (L + ε) * (x - a) + (L + ε) * dist x t := add_le_add hxS ht
        _ = (L + ε) * (t - a) := by
          rw [Real.dist_eq, abs_of_neg (by linarith)]
          ring
    have hsub := IsClosed.Icc_subset_of_forall_mem_nhdsWithin hclosed haS hstep
    exact hsub ⟨hab, le_rfl⟩
  -- let `ε → 0`
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  have hpos : 0 < b - a + 1 := by linarith
  have := key (η / (b - a + 1)) (div_pos hη hpos)
  calc dist (g a) (g b) ≤ (L + η / (b - a + 1)) * (b - a) := this
    _ = L * (b - a) + η * ((b - a) / (b - a + 1)) := by ring
    _ ≤ L * (b - a) + η * 1 := by
        gcongr
        rw [div_le_one hpos]
        linarith
    _ = L * (b - a) + η := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lemma 2.1** of [Basso2024] along a segment of a real normed space: if the pointwise
Lipschitz constant of `G` within a set `S` containing the segment `[p, q]` is at most `L` at every
point of `[p, q]`, then `d(G p, G q) ≤ L ‖p - q‖`. -/
theorem dist_le_of_lipAtWithin_segment {G : E → Y} {S : Set E} {p q : E} {L : ℝ}
    (hS : segment ℝ p q ⊆ S) (h : ∀ z ∈ segment ℝ p q, LipAtWithin G S z L) :
    dist (G p) (G q) ≤ L * dist p q := by
  rcases eq_or_ne p q with rfl | hpq
  · simp
  have hd : 0 < dist p q := dist_pos.2 hpq
  set g : ℝ → Y := fun t ↦ G (AffineMap.lineMap p q t) with hg
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap p q t ∈ segment ℝ p q := by
    intro t ht
    rw [segment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  have key : ∀ t ∈ Icc (0 : ℝ) 1, LipAtWithin g (Icc 0 1) t (L * dist p q) := by
    intro t ht L' hL'
    have hL'' : L < L' / dist p q := by rwa [lt_div_iff₀ hd]
    have h1 := h _ (hmem t ht) (L' / dist p q) hL''
    have htend : Tendsto (fun s : ℝ ↦ AffineMap.lineMap p q s) (𝓝[Icc 0 1] t)
        (𝓝[S] (AffineMap.lineMap p q t)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hc : Continuous (fun s : ℝ ↦ AffineMap.lineMap p q s) :=
          AffineMap.lineMap_continuous
        exact (hc.tendsto t).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact hS (hmem s hs)
    filter_upwards [htend h1] with s hs
    simp only [hg]
    calc dist (G (AffineMap.lineMap p q t)) (G (AffineMap.lineMap p q s))
        ≤ L' / dist p q * dist (AffineMap.lineMap p q t) (AffineMap.lineMap p q s) := hs
      _ = L' * dist t s := by
        rw [dist_lineMap_lineMap]
        field_simp
  have := dist_le_of_lipAtWithin_Icc (zero_le_one) key
  simpa [hg] using this

/-- **Lemma 2.1** of [Basso2024] along a segment: the version of
`dist_le_of_lipAtWithin_segment` for pointwise bounds in the whole space. -/
theorem dist_le_of_lipAt_segment {G : E → Y} {p q : E} {L : ℝ}
    (h : ∀ z ∈ segment ℝ p q, LipAt G z L) : dist (G p) (G q) ≤ L * dist p q :=
  dist_le_of_lipAtWithin_segment (S := univ) (subset_univ _)
    (fun z hz ↦ (h z hz).lipAtWithin univ)

end LipschitzExtension
