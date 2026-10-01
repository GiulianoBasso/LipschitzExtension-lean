/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import LipschitzExtension.Topology.MetricSpace.Nagata.Defs
import Mathlib.Order.Zorn

/-!
# Doubling spaces satisfy the Nagata condition

A metric space is `M`-doubling if every closed ball can be covered by at most `M` closed balls
of half the radius. Before Theorem 1.4, [Basso2024] quotes from Lemma 2.3 of Lang–Schlichenmaier
that an `M`-doubling space satisfies `Nagata(M³, 2)`. We prove the slightly stronger statement
`Nagata(M² - 1, 2)`.

## Main definitions

* `Doubling M A`: the subset `A` (with the induced metric) is `M`-doubling.

## Main statements

* `Doubling.nagata`: an `M`-doubling set satisfies `Nagata(M² - 1, 2)`.
* `Doubling.nagata_cube`: an `M`-doubling set satisfies `Nagata(M³, 2)`, the form quoted in
  [Basso2024] (used for Theorem 1.4).
* `doubling_of_ncard_le`: a set with at most `n` points is `n`-doubling.

## Proof outline

At scale `s > 0` choose (Zorn) a maximal subset `N ⊆ A` whose points are pairwise at distance
`> s` and cover `A` by the sets `A ∩ B(p, s)`, `p ∈ N` (diameter `≤ 2s`; covering by maximality).
If `E ⊆ A` has diameter `< s` and `e₀ ∈ E`, every member met by `E` has center `p` with
`d(p, e₀) < 2s`. Covering `A ∩ B(e₀, 2s)` by `M` balls of radius `s` and each of those by `M`
balls of radius `s/2` gives `M²` balls of radius `s/2`, each containing at most one point of `N`.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* U. Lang and T. Schlichenmaier, *Nagata dimension, quasisymmetric embeddings, and Lipschitz
  extensions*, Int. Math. Res. Not. 2005 (2005), no. 58, 3625–3655
-/

open Set Metric

namespace LipschitzExtension

variable {X : Type*} [PseudoMetricSpace X]

/-- `Doubling M A`: the subset `A` (with the induced metric) is `M`-doubling, i.e. every closed
ball of `A` of positive radius can be covered by at most `M` closed balls of `A` of half the
radius. -/
def Doubling (M : ℕ) (A : Set X) : Prop :=
  ∀ a ∈ A, ∀ ρ : ℝ, 0 < ρ → ∃ S : Finset X, (↑S : Set X) ⊆ A ∧ S.card ≤ M ∧
    A ∩ closedBall a ρ ⊆ ⋃ b ∈ S, closedBall b (ρ / 2)

/-- Existence of a maximal `s`-separated subset of `A`: every point of `A` is within `s` of it. -/
private theorem exists_maximal_separated (A : Set X) {s : ℝ} (hs : 0 < s) :
    ∃ N ⊆ A, (∀ p ∈ N, ∀ q ∈ N, p ≠ q → s < dist p q) ∧ ∀ a ∈ A, ∃ p ∈ N, dist a p ≤ s := by
  set S : Set (Set X) := {N | N ⊆ A ∧ ∀ p ∈ N, ∀ q ∈ N, p ≠ q → s < dist p q} with hS
  obtain ⟨N, ⟨hNA, hNsep⟩, hNmax⟩ : ∃ N, Maximal (· ∈ S) N := by
    apply zorn_subset
    intro c hcS hc
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun N hN ↦ subset_sUnion_of_mem hN⟩
    · rintro x ⟨N, hN, hxN⟩
      exact (hcS hN).1 hxN
    · rintro p ⟨N₁, hN₁, hp⟩ q ⟨N₂, hN₂, hq⟩ hpq
      rcases hc.total hN₁ hN₂ with h12 | h21
      · exact (hcS hN₂).2 p (h12 hp) q hq hpq
      · exact (hcS hN₁).2 p hp q (h21 hq) hpq
  refine ⟨N, hNA, hNsep, fun a ha ↦ ?_⟩
  by_contra hcon
  push Not at hcon
  have hmem : insert a N ∈ S := by
    refine ⟨insert_subset ha hNA, ?_⟩
    rintro p (rfl | hp) q (rfl | hq) hpq
    · exact absurd rfl hpq
    · exact hcon q hq
    · rw [dist_comm]; exact hcon p hp
    · exact hNsep p hp q hq hpq
  have haN : a ∈ N := hNmax hmem (subset_insert a N) (mem_insert a N)
  have := hcon a haN
  rw [dist_self] at this
  exact absurd this (not_lt.2 hs.le)

/-- An `M`-doubling set satisfies `Nagata(M² - 1, 2)`. -/
theorem Doubling.nagata {M : ℕ} {A : Set X} (h : Doubling M A) : Nagata (M ^ 2 - 1) 2 A := by
  classical
  intro s hs
  obtain ⟨N, hNA, hNsep, hcovN⟩ := exists_maximal_separated A hs
  refine ⟨(fun p ↦ A ∩ closedBall p s) '' N, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact inter_subset_left
  · intro a ha
    obtain ⟨p, hp, hap⟩ := hcovN a ha
    exact ⟨_, ⟨p, hp, rfl⟩, ha, hap⟩
  · rintro _ ⟨p, hp, rfl⟩ x ⟨-, hx⟩ y ⟨-, hy⟩
    rw [mem_closedBall] at hx hy
    calc dist x y ≤ dist x p + dist p y := dist_triangle _ _ _
      _ ≤ s + s := add_le_add hx (by rw [dist_comm]; exact hy)
      _ = 2 * s := by ring
  · intro E hE hEs
    rcases E.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
    · simp
    have he₀A : e₀ ∈ A := hE he₀
    -- the centers of the members met by `E` lie in `T`
    set T : Set X := {p ∈ N | dist p e₀ < 2 * s} with hT
    have hsubT : {B ∈ (fun p ↦ A ∩ closedBall p s) '' N | (B ∩ E).Nonempty} ⊆
        (fun p ↦ A ∩ closedBall p s) '' T := by
      rintro _ ⟨⟨p, hp, rfl⟩, e, ⟨-, hep⟩, heE⟩
      refine ⟨p, ⟨hp, ?_⟩, rfl⟩
      rw [mem_closedBall] at hep
      have hee₀ : dist e e₀ < s := by
        rw [← edist_lt_ofReal]
        exact lt_of_le_of_lt (Metric.edist_le_ediam_of_mem heE he₀) hEs
      calc dist p e₀ ≤ dist p e + dist e e₀ := dist_triangle _ _ _
        _ < s + s := add_lt_add_of_le_of_lt (by rw [dist_comm]; exact hep) hee₀
        _ = 2 * s := by ring
    -- cover `A ∩ closedBall e₀ (2s)` by at most `M²` closed balls of radius `s / 2`
    obtain ⟨S₁, hS₁A, hS₁card, hS₁cov⟩ := h e₀ he₀A (2 * s) (by positivity)
    have h₂ : ∀ b, ∃ S : Finset X, b ∈ A → S.card ≤ M ∧
        A ∩ closedBall b s ⊆ ⋃ b' ∈ S, closedBall b' (s / 2) := by
      intro b
      by_cases hb : b ∈ A
      · obtain ⟨S, -, hScard, hScov⟩ := h b hb s hs
        exact ⟨S, fun _ ↦ ⟨hScard, hScov⟩⟩
      · exact ⟨∅, fun h ↦ absurd h hb⟩
    choose S₂ hS₂ using h₂
    set T₂ : Finset X := S₁.biUnion S₂ with hT₂
    have hT₂card : T₂.card ≤ M ^ 2 := by
      calc T₂.card ≤ ∑ b ∈ S₁, (S₂ b).card := Finset.card_biUnion_le
        _ ≤ ∑ _b ∈ S₁, M := Finset.sum_le_sum fun b hb ↦ (hS₂ b (hS₁A hb)).1
        _ = S₁.card * M := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ M * M := Nat.mul_le_mul_right M hS₁card
        _ = M ^ 2 := (sq M).symm
    have hf : ∀ p, ∃ b', p ∈ T → b' ∈ T₂ ∧ dist p b' ≤ s / 2 := by
      intro p
      by_cases hp : p ∈ T
      · have hpA : p ∈ A := hNA hp.1
        have : p ∈ A ∩ closedBall e₀ (2 * s) := ⟨hpA, by rw [mem_closedBall]; exact hp.2.le⟩
        have := hS₁cov this
        simp only [mem_iUnion, mem_closedBall] at this
        obtain ⟨b, hb, hpb⟩ := this
        have hbA : b ∈ A := hS₁A hb
        have : p ∈ A ∩ closedBall b s := ⟨hpA, by rw [mem_closedBall]; linarith⟩
        have := (hS₂ b hbA).2 this
        simp only [mem_iUnion, mem_closedBall] at this
        obtain ⟨b', hb', hpb'⟩ := this
        exact ⟨b', fun _ ↦ ⟨Finset.mem_biUnion.2 ⟨b, hb, hb'⟩, hpb'⟩⟩
      · exact ⟨p, fun h ↦ absurd h hp⟩
    choose f hf using hf
    have hinj : InjOn f T := by
      intro p hp q hq hpq
      by_contra hne
      have hsep := hNsep p hp.1 q hq.1 hne
      have h1 := (hf p hp).2
      have h2 := (hf q hq).2
      rw [hpq] at h1
      have : dist p q ≤ s := by
        calc dist p q ≤ dist p (f q) + dist (f q) q := dist_triangle _ _ _
          _ ≤ s / 2 + s / 2 := add_le_add h1 (by rw [dist_comm]; exact h2)
          _ = s := by ring
      linarith
    have hmaps : MapsTo f T (↑T₂ : Set X) := fun p hp ↦ (hf p hp).1
    calc {B ∈ (fun p ↦ A ∩ closedBall p s) '' N | (B ∩ E).Nonempty}.encard
        ≤ ((fun p ↦ A ∩ closedBall p s) '' T).encard := encard_le_encard hsubT
      _ ≤ T.encard := encard_image_le _ _
      _ ≤ (↑T₂ : Set X).encard := encard_le_encard_of_injOn hmaps hinj
      _ = (T₂.card : ℕ∞) := encard_coe_eq_coe_finsetCard _
      _ ≤ ((M ^ 2 : ℕ) : ℕ∞) := Nat.cast_le.2 hT₂card
      _ ≤ ((M ^ 2 - 1 : ℕ) : ℕ∞) + 1 := by
        norm_cast
        exact le_tsub_add

/-- An `M`-doubling set satisfies `Nagata(M³, 2)` (the form quoted in [Basso2024] before
Theorem 1.4, from Lemma 2.3 of Lang–Schlichenmaier). -/
theorem Doubling.nagata_cube {M : ℕ} {A : Set X} (h : Doubling M A) : Nagata (M ^ 3) 2 A :=
  h.nagata.mono (by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · have : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM (by norm_num)
      omega) le_rfl

/-- If `A` has at most `n` points, then `A` is `n`-doubling. -/
theorem doubling_of_ncard_le {A : Set X} (hA : A.Finite)
    {n : ℕ} (hcard : A.ncard ≤ n) : Doubling n A := by
  intro a _ ρ hρ
  refine ⟨hA.toFinset, by simp, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card A hA]
    exact hcard
  · rintro x ⟨hxA, -⟩
    exact Set.mem_iUnion₂.2 ⟨x, hA.mem_toFinset.2 hxA, mem_closedBall_self (by positivity)⟩

end LipschitzExtension
