/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The radial projection onto the boundary of a convex body

Let `K` be a convex set in a real inner product space with `0 ∈ interior K`. For `x ≠ 0`, the
*radial projection* `radialProj K x = x / gauge K x` is the point of the ray `ℝ_{>0} x` on the
boundary of `K` (`radialProj_mem_frontier`).

This file proves Vrecica's bound for the Lipschitz constant of the radial projection, which is
quoted in the proof of Lemma 7.1 of [Basso2024] (Theorem 1 of Vrecica's paper): if `K` is a convex
body with `B(0, r) ⊆ K ⊆ B(0, R)`, then the radial projection of the sphere `S(t)` onto the
boundary `∂K` is `R²/(r t)`-Lipschitz. We give a self-contained elementary proof.

## Main definitions

* `radialProj K x`: the radial projection of `x` onto the boundary of `K`.

## Main statements

* `norm_smul_sub_smul_le`: the key inequality behind Vrecica's bound, see below.
* `norm_sub_le_of_mem_frontier`: Vrecica's bound: if `B(0, r) ⊆ K` and `‖·‖ ≤ R` on `∂K`, then
  `|P - Q| ≤ (R²/r) |P/|P| - Q/|Q||` for all `P, Q ∈ ∂K`.
* `dist_radialProj_le`: the radial projection onto `∂K` is `(R/r)²`-Lipschitz on
  `{x | r ≤ ‖x‖}`, the form in which Vrecica's bound is used in the proof of Lemma 7.1 of
  [Basso2024].

## Implementation notes

We work in a complete real inner product space, so that a supporting functional is represented by
a vector (`InnerProductSpace.toDual`). In Vrecica's bound, `K` need not be closed or bounded, and
the bound `‖·‖ ≤ R` is only assumed on `∂K = frontier K`.

## Proof outline

*The key inequality* (`norm_smul_sub_smul_le`). Let `u, v` be unit vectors, `P = a u`, `Q = b v`
with `0 < r ≤ a ≤ b ≤ R`, and let `ν` be a vector with `‖ν‖ ≤ 1`, `r ≤ ⟨ν, P⟩` and
`⟨ν, Q⟩ ≤ ⟨ν, P⟩` (a unit normal of a supporting hyperplane at `P` of a convex set containing
`B(0, r)` and `Q`). Then `|P - Q| ≤ (R²/r) |u - v|`.

Put `C = ⟨u, v⟩`, `S = √(1 - C²)`, `c = |u - v|` (so `c² = 2 - 2C`), `A = √(a² - r²)`,
`B' = √(R² - r²)` and `κ = C - S A / r`. Since `x = ⟨ν, u⟩ ≥ r/a` and `|ν - x u| ≤ √(1 - x²)`, we
have `⟨ν, v⟩ ≥ x C - √(1 - x²) S ≥ x κ`, hence `b κ ≤ a`. Recall that
`|P - Q|² = (b - a)² + a b c²`, which is increasing in `b ≥ a`.

* If `R κ ≥ a`, then `b ≤ a/κ ≤ R` and, by the identity
  `(1 - κ)² + κ c² = (a²/r²) c² (1 - c²/4)`, we get
  `|P - Q|² ≤ (a/κ)² (a²/r²) c² (1 - c²/4) ≤ R⁴ c² / r²`.
* If `R κ < a`, then `C < C* = (r² + A B')/(a R)` (for `C ≥ 0`, since the function
  `C ↦ C - √(1 - C²) A/r` is increasing on `[0, 1]` and equals `a/R` at `C*`), so
  `c² > 2 - 2 C* = 2 r² (R - a)² / (a R (a R - r² + A B'))` (using
  `(a R - r²)² - A² B'² = r² (R - a)²`). Now `a (a R - r² + A B') ≤ 2 R (R² - r²) ≤ 2 (R³ - a r²)`
  gives `(R - a)² ≤ c² R (R³ - a r²)/r²`, i.e. `|P - Q|² ≤ (R - a)² + a R c² ≤ R⁴ c²/r²`.

*Vrecica's bound* (`norm_sub_le_of_mem_frontier`). Let `P, Q ∈ ∂K`, where `K` is convex with
`B(0, r) ⊆ K` and `‖·‖ ≤ R` on `∂K`. A supporting hyperplane at `P` (Hahn–Banach,
`geometric_hahn_banach_open_point`, applied to `interior K`) has distance `≥ r` from `0`, and `Q`
lies on its inner side since `Q ∈ closure (interior K)`. Apply the key inequality at the point of
smaller norm. Consequently, the radial projection is `(R/r)²`-Lipschitz on `{x | r ≤ ‖x‖}`
(`dist_radialProj_le`), since `x ↦ x/‖x‖` is `1/r`-Lipschitz there.

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* S. Vrecica, *A note on starshaped sets*, Publ. Inst. Math. (Beograd) (N.S.) 29 (1981), 283–288
-/

open Set Metric Filter Topology

namespace LipschitzExtension

/-- Case `R κ ≥ a` of the key inequality (with `κ' = r κ`). -/
private lemma key_real_case1 {r a b R C S A : ℝ} (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (hbR : b ≤ R) (hC : C ≤ 1) (hS2 : S ^ 2 = 1 - C ^ 2) (hA2 : A ^ 2 = a ^ 2 - r ^ 2)
    (hκ : b * (r * C - S * A) ≤ a * r) (h1 : a * r ≤ R * (r * C - S * A)) :
    r ^ 2 * (a ^ 2 + b ^ 2 - 2 * a * b * C) ≤ R ^ 4 * (2 - 2 * C) := by
  have ha : 0 < a := hr.trans_le hra
  have hR : 0 < R := ha.trans_le (hab.trans hbR)
  have har : 0 < a * r := mul_pos ha hr
  have hκpos : 0 < r * C - S * A := by
    by_contra h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hR.le (not_lt.1 h)]
  set β := a * r / (r * C - S * A) with hβdef
  have hβκ : β * (r * C - S * A) = a * r := div_mul_cancel₀ _ hκpos.ne'
  have hbβ : b ≤ β := by rw [hβdef, le_div_iff₀ hκpos]; exact hκ
  have hβR : β ≤ R := by rw [hβdef, div_le_iff₀ hκpos]; exact h1
  have hβ0 : 0 ≤ β := (ha.le.trans hab).trans hbβ
  have hmono : a ^ 2 + b ^ 2 - 2 * a * b * C ≤ a ^ 2 + β ^ 2 - 2 * a * β * C := by
    have h2 : 0 ≤ β + b - 2 * a * C := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hbβ) h2]
  have hid : r ^ 2 * (a ^ 2 + β ^ 2 - 2 * a * β * C) = β ^ 2 * a ^ 2 * S ^ 2 := by
    linear_combination (β * r * C + β * S * A - a * r) * hβκ + (-(β ^ 2 * r ^ 2)) * hS2 +
      (β ^ 2 * S ^ 2) * hA2
  have hS2le : S ^ 2 ≤ 2 - 2 * C := by nlinarith
  calc r ^ 2 * (a ^ 2 + b ^ 2 - 2 * a * b * C)
      ≤ r ^ 2 * (a ^ 2 + β ^ 2 - 2 * a * β * C) := by gcongr
    _ = β ^ 2 * a ^ 2 * S ^ 2 := hid
    _ ≤ R ^ 2 * R ^ 2 * (2 - 2 * C) := by
      have hβ2 : β ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hβ0 hβR 2
      have ha2 : a ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ ha.le ((hab.trans hbβ).trans hβR) 2
      gcongr
    _ = R ^ 4 * (2 - 2 * C) := by ring

/-- Case `R κ < a` of the key inequality. -/
private lemma key_real_case2 {r a b R C S A : ℝ} (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (hbR : b ≤ R) (hC : C ≤ 1) (hS2 : S ^ 2 = 1 - C ^ 2) (hA : 0 ≤ A)
    (hA2 : A ^ 2 = a ^ 2 - r ^ 2) (h2 : R * (r * C - S * A) < a * r) :
    r ^ 2 * (a ^ 2 + b ^ 2 - 2 * a * b * C) ≤ R ^ 4 * (2 - 2 * C) := by
  have ha : 0 < a := hr.trans_le hra
  have haR : a ≤ R := hab.trans hbR
  have hR : 0 < R := ha.trans_le haR
  have hrR : r ≤ R := hra.trans haR
  set B := √(R ^ 2 - r ^ 2) with hBdef
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hB2 : B ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  have hAB : A ≤ B := by
    have : A ^ 2 ≤ B ^ 2 := by rw [hA2, hB2]; nlinarith
    exact (sq_le_sq₀ hA hB).1 this
  -- `C ≤ C* = (r² + A B') / (a R)`
  have hclaim : a * R * C ≤ r ^ 2 + A * B := by
    by_contra hcon
    replace hcon := not_le.1 hcon
    have h0 : 0 ≤ r ^ 2 + A * B := by positivity
    have h3 : (r ^ 2 + A * B) ^ 2 < (a * R * C) ^ 2 := pow_lt_pow_left₀ hcon h0 two_ne_zero
    have hid : (a * R) ^ 2 - (r ^ 2 + A * B) ^ 2 = (r * (B - A)) ^ 2 := by
      linear_combination (-B ^ 2 - r ^ 2) * hA2 + (-a ^ 2) * hB2
    have h4 : (a * R * S) ^ 2 < (r * (B - A)) ^ 2 := by
      have : (a * R * S) ^ 2 = (a * R) ^ 2 - (a * R * C) ^ 2 := by
        rw [mul_pow, hS2]; ring
      rw [this, ← hid]
      linarith
    have h5 : a * R * S < r * (B - A) :=
      lt_of_pow_lt_pow_left₀ 2 (mul_nonneg hr.le (sub_nonneg.2 hAB)) h4
    have h6 : a * R * (a * r) < a * R * (R * (r * C - S * A)) := by
      have e : a * R * (R * (r * C - S * A)) = R * (r * (a * R * C) - (a * R * S) * A) := by ring
      rw [e]
      have e2 : a * R * (a * r) = R * (r * (r ^ 2 + A * B) - (r * (B - A)) * A) := by
        linear_combination (-(R * r)) * hA2
      rw [e2]
      apply mul_lt_mul_of_pos_left _ hR
      nlinarith [mul_le_mul_of_nonneg_right h5.le hA]
    have h7 : a * r < R * (r * C - S * A) := lt_of_mul_lt_mul_left h6 (by positivity)
    linarith
  -- `r² (R - a)² ≤ 2 (1 - C) R (R³ - a r²)`
  have hX : 0 ≤ a * R - r ^ 2 - A * B := by
    have hid : (a * R - r ^ 2) ^ 2 - (A * B) ^ 2 = r ^ 2 * (R - a) ^ 2 := by
      linear_combination (-B ^ 2) * hA2 + (-(a ^ 2 - r ^ 2)) * hB2
    have h1 : 0 ≤ a * R - r ^ 2 := by nlinarith
    have h2 : (A * B) ^ 2 ≤ (a * R - r ^ 2) ^ 2 := by nlinarith [sq_nonneg (R - a)]
    have := (sq_le_sq₀ (by positivity) h1).1 h2
    linarith
  have hXY : (a * R - r ^ 2 - A * B) * (a * R - r ^ 2 + A * B) = r ^ 2 * (R - a) ^ 2 := by
    linear_combination (-B ^ 2) * hA2 + (-(a ^ 2 - r ^ 2)) * hB2
  have hY : a * (a * R - r ^ 2 + A * B) ≤ 2 * (R ^ 3 - a * r ^ 2) := by
    have h1 : A * B ≤ R ^ 2 - r ^ 2 := by
      rw [← hB2]; nlinarith [mul_le_mul_of_nonneg_right hAB hB]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha.le]
  have hR3 : 0 ≤ R ^ 3 - a * r ^ 2 := by
    have : a * r ^ 2 ≤ R * R ^ 2 :=
      mul_le_mul haR (pow_le_pow_left₀ hr.le hrR 2) (sq_nonneg r) hR.le
    nlinarith
  have hG2 : a * (r ^ 2 * (R - a) ^ 2) ≤ a * (2 * (1 - C) * R * (R ^ 3 - a * r ^ 2)) := by
    calc a * (r ^ 2 * (R - a) ^ 2)
        = (a * R - r ^ 2 - A * B) * (a * (a * R - r ^ 2 + A * B)) := by rw [← hXY]; ring
      _ ≤ (a * R - r ^ 2 - A * B) * (2 * (R ^ 3 - a * r ^ 2)) := by gcongr
      _ ≤ (a * R * (1 - C)) * (2 * (R ^ 3 - a * r ^ 2)) := by
          gcongr
          linarith
      _ = a * (2 * (1 - C) * R * (R ^ 3 - a * r ^ 2)) := by ring
  have hG2' := le_of_mul_le_mul_left hG2 ha
  have hmono : (b - a) ^ 2 + 2 * a * b * (1 - C) ≤ (R - a) ^ 2 + 2 * a * R * (1 - C) := by
    have h1 : (b - a) ^ 2 ≤ (R - a) ^ 2 :=
      pow_le_pow_left₀ (sub_nonneg.2 hab) (by linarith) 2
    have h2 : 2 * a * b * (1 - C) ≤ 2 * a * R * (1 - C) := by
      have : 0 ≤ 1 - C := by linarith
      gcongr
    linarith
  calc r ^ 2 * (a ^ 2 + b ^ 2 - 2 * a * b * C)
      = r ^ 2 * ((b - a) ^ 2 + 2 * a * b * (1 - C)) := by ring
    _ ≤ r ^ 2 * ((R - a) ^ 2 + 2 * a * R * (1 - C)) := by gcongr
    _ ≤ 2 * (1 - C) * R * (R ^ 3 - a * r ^ 2) + r ^ 2 * (2 * a * R * (1 - C)) := by
        nlinarith
    _ = R ^ 4 * (2 - 2 * C) := by ring

/-- The key inequality in terms of the real parameters: `r² (a² + b² - 2abC) ≤ R⁴ (2 - 2C)`, i.e.
`r² |P - Q|² ≤ R⁴ |u - v|²`. -/
private lemma key_real {r a b R C S A : ℝ} (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (hbR : b ≤ R) (hC : C ≤ 1) (hS2 : S ^ 2 = 1 - C ^ 2) (hA : 0 ≤ A)
    (hA2 : A ^ 2 = a ^ 2 - r ^ 2) (hκ : b * (r * C - S * A) ≤ a * r) :
    r ^ 2 * (a ^ 2 + b ^ 2 - 2 * a * b * C) ≤ R ^ 4 * (2 - 2 * C) := by
  rcases le_or_gt (a * r) (R * (r * C - S * A)) with h1 | h2
  · exact key_real_case1 hr hra hab hbR hC hS2 hA2 hκ h1
  · exact key_real_case2 hr hra hab hbR hC hS2 hA hA2 h2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gram inequality for `ν` and the unit vectors `u, v`. -/
private lemma gram_ineq {u v ν : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hν : ‖ν‖ ≤ 1) :
    (inner ℝ ν v - inner ℝ u v * inner ℝ ν u) ^ 2 ≤
      (1 - inner ℝ ν u ^ 2) * (1 - inner ℝ u v ^ 2) := by
  have h1 := real_inner_mul_inner_self_le (ν - inner ℝ ν u • u) (v - inner ℝ u v • u)
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hνν : inner ℝ ν ν = ‖ν‖ ^ 2 := real_inner_self_eq_norm_sq ν
  have hvu : inner ℝ v u = inner ℝ u v := real_inner_comm u v
  have huν : inner ℝ u ν = inner ℝ ν u := real_inner_comm ν u
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, huu,
    hvv, hνν, hvu, huν] at h1
  have h2 : (inner ℝ ν v - inner ℝ u v * inner ℝ ν u) ^ 2 ≤
      (‖ν‖ ^ 2 - inner ℝ ν u ^ 2) * (1 - inner ℝ u v ^ 2) := by
    convert h1 using 1 <;> ring
  have hC : inner ℝ u v ^ 2 ≤ 1 := by
    have := abs_real_inner_le_norm u v
    rw [hu, hv, mul_one] at this
    nlinarith [abs_nonneg (inner ℝ u v), sq_abs (inner ℝ u v)]
  have hν2 : ‖ν‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ν]
  nlinarith [mul_le_mul_of_nonneg_right hν2 (sub_nonneg.2 hC)]

/-- The key inequality behind Vrecica's bound: let `u, v` be unit vectors, let
`0 < r ≤ a ≤ b ≤ R`, and let `‖ν‖ ≤ 1` with `r ≤ ⟨ν, a u⟩` and `⟨ν, b v⟩ ≤ ⟨ν, a u⟩`. Then
`‖a u - b v‖ ≤ (R²/r) ‖u - v‖`. See the module docstring for the proof. -/
theorem norm_smul_sub_smul_le {u v ν : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hν : ‖ν‖ ≤ 1)
    {r a b R : ℝ} (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b) (hbR : b ≤ R)
    (hsupp : r ≤ a * inner ℝ ν u) (hQ : b * inner ℝ ν v ≤ a * inner ℝ ν u) :
    ‖a • u - b • v‖ ≤ R ^ 2 / r * ‖u - v‖ := by
  have hgram := gram_ineq hu hv hν
  set C := inner ℝ u v with hCdef
  set x := inner ℝ ν u with hxdef
  set y := inner ℝ ν v with hydef
  have ha : 0 < a := hr.trans_le hra
  have hb : 0 < b := ha.trans_le hab
  have hC1 : C ≤ 1 := by
    have := real_inner_le_norm u v
    rw [hu, hv, mul_one] at this
    exact this
  have hC2 : C ^ 2 ≤ 1 := by
    have := abs_real_inner_le_norm u v
    rw [hu, hv, mul_one] at this
    nlinarith [abs_nonneg C, sq_abs C]
  have hx : 0 < x := by
    by_contra h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le (not_lt.1 h)]
  set S := √(1 - C ^ 2) with hSdef
  set A := √(a ^ 2 - r ^ 2) with hAdef
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = 1 - C ^ 2 := Real.sq_sqrt (by linarith)
  have hA2 : A ^ 2 = a ^ 2 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  -- `r (y - C x) ≥ - x S A`
  have h5 : (r * (y - C * x)) ^ 2 ≤ (x * S * A) ^ 2 := by
    have h1 : r ^ 2 * (1 - x ^ 2) ≤ x ^ 2 * A ^ 2 := by
      rw [hA2]
      have : r ^ 2 ≤ (a * x) ^ 2 := pow_le_pow_left₀ hr.le hsupp 2
      nlinarith
    calc (r * (y - C * x)) ^ 2 = r ^ 2 * (y - C * x) ^ 2 := by ring
      _ ≤ r ^ 2 * ((1 - x ^ 2) * (1 - C ^ 2)) := by gcongr
      _ = r ^ 2 * (1 - x ^ 2) * S ^ 2 := by rw [hS2]; ring
      _ ≤ x ^ 2 * A ^ 2 * S ^ 2 := by gcongr
      _ = (x * S * A) ^ 2 := by ring
  have h6 : -(x * S * A) ≤ r * (y - C * x) :=
    (abs_le_of_sq_le_sq' h5 (by positivity)).1
  have hκ : b * (r * C - S * A) ≤ a * r := by
    have h7 : x * (b * (r * C - S * A)) ≤ x * (a * r) := by
      have : x * (b * (r * C - S * A)) = b * (r * (C * x) - x * S * A) := by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left h6 hb.le]
    exact le_of_mul_le_mul_left h7 hx
  have hmain := key_real hr hra hab hbR hC1 hS2 hA hA2 hκ
  have hn1 : ‖a • u - b • v‖ ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * C := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hu,
      hv, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb]
    ring
  have hn2 : ‖u - v‖ ^ 2 = 2 - 2 * C := by
    rw [norm_sub_sq_real, hu, hv]
    ring
  have hrhs : 0 ≤ R ^ 2 / r * ‖u - v‖ := by positivity
  rw [← sq_le_sq₀ (norm_nonneg _) hrhs, hn1, mul_pow, hn2, div_pow, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity)]
  calc (a ^ 2 + b ^ 2 - 2 * a * b * C) * r ^ 2 = r ^ 2 * (a ^ 2 + b ^ 2 - 2 * a * b * C) := by
        ring
    _ ≤ R ^ 4 * (2 - 2 * C) := hmain
    _ = (R ^ 2) ^ 2 * (2 - 2 * C) := by ring

/-- The radial projection `x ↦ x / gauge K x` onto the boundary of `K`. It is meaningful for a
convex set `K` with `0 ∈ interior K` and `x ≠ 0`. -/
noncomputable def radialProj (K : Set E) (x : E) : E :=
  (gauge K x)⁻¹ • x

private lemma gauge_pos_of_bounded {K : Set E} (hK0 : K ∈ 𝓝 (0 : E))
    (hKb : Bornology.IsBounded K) {x : E} (hx : x ≠ 0) : 0 < gauge K x :=
  (gauge_pos (absorbent_nhds_zero hK0) (NormedSpace.isVonNBounded_of_isBounded ℝ hKb)).2 hx

/-- If `K` is a bounded convex set with `0 ∈ interior K` and `x ≠ 0`, then `radialProj K x` lies
on the boundary of `K`. -/
theorem radialProj_mem_frontier {K : Set E} (hKc : Convex ℝ K) (hK0 : K ∈ 𝓝 (0 : E))
    (hKb : Bornology.IsBounded K) {x : E} (hx : x ≠ 0) : radialProj K x ∈ frontier K := by
  have hpos := gauge_pos_of_bounded hK0 hKb hx
  rw [← gauge_eq_one_iff_mem_frontier hKc hK0, radialProj,
    gauge_smul_of_nonneg (inv_nonneg.2 hpos.le), smul_eq_mul, inv_mul_cancel₀ hpos.ne']

/-- The radial projection fixes the boundary points of a convex set `K` with `0 ∈ interior K`. -/
theorem radialProj_eq_self {K : Set E} (hKc : Convex ℝ K) (hK0 : K ∈ 𝓝 (0 : E)) {x : E}
    (hx : x ∈ frontier K) : radialProj K x = x := by
  rw [radialProj, (gauge_eq_one_iff_mem_frontier hKc hK0).2 hx, inv_one, one_smul]

/-- The radial projection is invariant under multiplication by positive scalars. -/
theorem radialProj_smul {K : Set E} {t : ℝ} (ht : 0 < t) (x : E) :
    radialProj K (t • x) = radialProj K x := by
  rw [radialProj, radialProj, gauge_smul_of_nonneg ht.le, smul_eq_mul, smul_smul, mul_inv,
    mul_right_comm, inv_mul_cancel₀ ht.ne', one_mul]

/-- Vrecica's bound at the point of smaller norm. -/
private lemma norm_sub_le_of_mem_frontier_aux [CompleteSpace E] {K : Set E} (hKc : Convex ℝ K)
    {r R : ℝ} (hr : 0 < r) (hball : ball (0 : E) r ⊆ K) (hR : ∀ x ∈ frontier K, ‖x‖ ≤ R)
    {P Q : E} (hP : P ∈ frontier K) (hQ : Q ∈ frontier K) (hPQ : ‖P‖ ≤ ‖Q‖) :
    ‖P - Q‖ ≤ R ^ 2 / r * ‖‖P‖⁻¹ • P - ‖Q‖⁻¹ • Q‖ := by
  have hint : ball (0 : E) r ⊆ interior K := interior_maximal hball isOpen_ball
  have hPint : P ∉ interior K := hP.2
  have hrP : r ≤ ‖P‖ := by
    by_contra h
    exact hPint (hint (mem_ball_zero_iff.2 (not_le.1 h)))
  have hPpos : 0 < ‖P‖ := hr.trans_le hrP
  have hQpos : 0 < ‖Q‖ := hPpos.trans_le hPQ
  -- a supporting functional at `P`
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hKc.interior isOpen_interior hPint
  have hcl : ∀ z ∈ closure (interior K), f z ≤ f P := fun z hz ↦
    closure_minimal (fun w hw ↦ (hf w hw).le) (isClosed_le f.continuous continuous_const) hz
  have hne : (interior K).Nonempty := ⟨0, hint (mem_ball_self hr)⟩
  have hfQ : f Q ≤ f P := by
    apply hcl
    rw [hKc.closure_interior_eq_closure_of_nonempty_interior hne]
    exact hQ.1
  -- represent `f` by a vector `n`
  set n := (InnerProductSpace.toDual ℝ E).symm f with hndef
  have hn : ∀ z, inner ℝ n z = f z := fun z ↦ InnerProductSpace.toDual_symm_apply
  have hfP : 0 < f P := by
    have := hf 0 (hint (mem_ball_self hr))
    rwa [map_zero] at this
  have hn0 : n ≠ 0 := by
    intro h
    have := hn P
    rw [h, inner_zero_left] at this
    linarith
  have hnpos : 0 < ‖n‖ := norm_pos_iff.2 hn0
  have hrn : r * ‖n‖ ≤ f P := by
    have hz : (r / ‖n‖) • n ∈ closedBall (0 : E) r := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_mul_cancel₀ _ hnpos.ne']
    have hcb : closedBall (0 : E) r ⊆ closure (interior K) := by
      rw [← closure_ball (0 : E) hr.ne']
      exact closure_mono hint
    have := hcl _ (hcb hz)
    rw [← hn, real_inner_smul_right, real_inner_self_eq_norm_sq] at this
    calc r * ‖n‖ = r / ‖n‖ * ‖n‖ ^ 2 := by field_simp
      _ ≤ f P := this
  -- the unit normal `ν`
  set ν := ‖n‖⁻¹ • n with hνdef
  have hν : ‖ν‖ ≤ 1 := by
    rw [hνdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnpos.ne']
  have hνz : ∀ z, inner ℝ ν z = ‖n‖⁻¹ * f z := by
    intro z
    rw [hνdef, real_inner_smul_left, hn]
  have hu : ‖‖P‖⁻¹ • P‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hPpos.ne']
  have hv : ‖‖Q‖⁻¹ • Q‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hQpos.ne']
  have hPu : ‖P‖ • ‖P‖⁻¹ • P = P := by rw [smul_smul, mul_inv_cancel₀ hPpos.ne', one_smul]
  have hQv : ‖Q‖ • ‖Q‖⁻¹ • Q = Q := by rw [smul_smul, mul_inv_cancel₀ hQpos.ne', one_smul]
  have key := norm_smul_sub_smul_le hu hv hν hr hrP hPQ (hR Q hQ) ?_ ?_
  · rwa [hPu, hQv] at key
  · rw [← real_inner_smul_right, hPu, hνz, le_inv_mul_iff₀ hnpos, mul_comm]
    exact hrn
  · rw [← real_inner_smul_right, ← real_inner_smul_right, hPu, hQv, hνz, hνz]
    exact mul_le_mul_of_nonneg_left hfQ (inv_nonneg.2 (norm_nonneg _))

/-- **Vrecica's bound** (Theorem 1 of Vrecica's paper, quoted in the proof of Lemma 7.1 of
[Basso2024]): for boundary points `P, Q` of a convex set `K` with `B(0, r) ⊆ K` and `‖·‖ ≤ R` on
`∂K`, we have `|P - Q| ≤ (R²/r) |P/|P| - Q/|Q||`. -/
theorem norm_sub_le_of_mem_frontier [CompleteSpace E] {K : Set E} (hKc : Convex ℝ K) {r R : ℝ}
    (hr : 0 < r) (hball : ball (0 : E) r ⊆ K) (hR : ∀ x ∈ frontier K, ‖x‖ ≤ R) {P Q : E}
    (hP : P ∈ frontier K) (hQ : Q ∈ frontier K) :
    ‖P - Q‖ ≤ R ^ 2 / r * ‖‖P‖⁻¹ • P - ‖Q‖⁻¹ • Q‖ := by
  rcases le_total ‖P‖ ‖Q‖ with h | h
  · exact norm_sub_le_of_mem_frontier_aux hKc hr hball hR hP hQ h
  · rw [norm_sub_rev P Q, norm_sub_rev (‖P‖⁻¹ • P)]
    exact norm_sub_le_of_mem_frontier_aux hKc hr hball hR hQ hP h

/-- `x ↦ x / ‖x‖` is `1/r`-Lipschitz on `{x | r ≤ ‖x‖}`. -/
private lemma norm_inv_smul_sub_le {x y : E} {r : ℝ} (hr : 0 < r) (hx : r ≤ ‖x‖)
    (hy : r ≤ ‖y‖) : ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ ‖x - y‖ / r := by
  have hx0 : 0 < ‖x‖ := hr.trans_le hx
  have hy0 : 0 < ‖y‖ := hr.trans_le hy
  set N := ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ with hNdef
  have h1 : ‖x‖ * ‖y‖ * N ^ 2 = 2 * ‖x‖ * ‖y‖ - 2 * inner ℝ x y := by
    rw [hNdef, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, norm_inv, norm_norm, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne',
      inv_mul_cancel₀ hy0.ne']
    field_simp
    ring
  have h2 : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := norm_sub_sq_real x y
  have h3 : (r * N) ^ 2 ≤ ‖x - y‖ ^ 2 := by
    have : r * r ≤ ‖x‖ * ‖y‖ := mul_le_mul hx hy hr.le hx0.le
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg N]
  rw [le_div_iff₀ hr, mul_comm]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 h3

/-- The radial projection onto `∂K` is `(R/r)²`-Lipschitz on `{x | r ≤ ‖x‖}` if `K` is a bounded
convex set with `B(0, r) ⊆ K` and `‖·‖ ≤ R` on `∂K` (a consequence of Vrecica's bound, used in the
proof of Lemma 7.1 of [Basso2024]). -/
theorem dist_radialProj_le [CompleteSpace E] {K : Set E} (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) {r R : ℝ} (hr : 0 < r) (hball : ball (0 : E) r ⊆ K)
    (hR : ∀ x ∈ frontier K, ‖x‖ ≤ R) {x y : E} (hx : r ≤ ‖x‖) (hy : r ≤ ‖y‖) :
    dist (radialProj K x) (radialProj K y) ≤ (R / r) ^ 2 * dist x y := by
  have hK0 : K ∈ 𝓝 (0 : E) := Filter.mem_of_superset (ball_mem_nhds 0 hr) hball
  have hx0 : x ≠ 0 := norm_pos_iff.1 (hr.trans_le hx)
  have hy0 : y ≠ 0 := norm_pos_iff.1 (hr.trans_le hy)
  have hV := norm_sub_le_of_mem_frontier hKc hr hball hR
    (radialProj_mem_frontier hKc hK0 hKb hx0) (radialProj_mem_frontier hKc hK0 hKb hy0)
  have hnorm : ∀ z : E, z ≠ 0 → ‖radialProj K z‖⁻¹ • radialProj K z = ‖z‖⁻¹ • z := by
    intro z hz
    have hg := gauge_pos_of_bounded hK0 hKb hz
    have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [radialProj, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hg), smul_smul]
    congr 1
    field_simp
  rw [hnorm x hx0, hnorm y hy0] at hV
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖radialProj K x - radialProj K y‖ ≤ R ^ 2 / r * ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ := hV
    _ ≤ R ^ 2 / r * (‖x - y‖ / r) := by gcongr; exact norm_inv_smul_sub_le hr hx hy
    _ = (R / r) ^ 2 * ‖x - y‖ := by ring

end LipschitzExtension
