/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# CAT(0) spaces

This file defines CAT(0) spaces, following Chapter II.1 of Bridson and Haefliger, and proves the
CN inequality of Bruhat and Tits for them. In [Basso2024], complete CAT(0) spaces appear as the
target spaces of Theorem 1.3 and as examples of spaces of generalized non-positive curvature
(Section 1.5 of [Basso2024], see `IsCAT0.isGNPC`).

* A *geodesic* from `x` to `y` is a map `γ : ℝ → X` with `γ 0 = x` and `γ (d(x, y)) = y` which is
  isometric on `[0, d(x, y)]`. A *geodesic space* is a metric space in which any two points are
  joined by a geodesic.
* A *geodesic triangle* consists of three vertices `x 0, x 1, x 2` and three geodesics `γ i` from
  `x i` to `x (i + 1)` (indices in `Fin 3`). A *comparison triangle* consists of three points
  `p i ∈ 𝔼² = EuclideanSpace ℝ (Fin 2)` with `|p i - p j| = d(x i, x j)`. The point of the side
  `γ i` at distance `s d(x i, x (i + 1))` from `x i` (`s ∈ [0, 1]`) has the comparison point
  `(1 - s) p i + s p (i + 1)`.
* `X` is a *CAT(0) space* (Definition II.1.1 of Bridson and Haefliger) if it is a geodesic space
  in which every geodesic triangle satisfies the CAT(0) inequality: the distance between any two
  of its points is at most the distance between the corresponding comparison points.

## Main definitions

* `IsGeodesic γ x y`: `γ` is a geodesic from `x` to `y`.
* `IsGeodesicSpace X`: `X` is a geodesic space.
* `IsComparisonTriangle x p`: `p` is a comparison triangle in `𝔼²` for the points `x 0, x 1, x 2`.
* `IsCAT0 X`: `X` is a CAT(0) space.

## Main statements

* `exists_comparisonTriangle`: any three points of a metric space have a comparison triangle.
* `IsCAT0.dist_sq_le`: the CN inequality along geodesics,
  `d(z, γ(t d(x, y)))² ≤ (1 - t) d(z, x)² + t d(z, y)² - t (1 - t) d(x, y)²`.
* `IsCAT0.exists_midpoint`: the *CN inequality of Bruhat and Tits*: for all `x, y` there is a
  point `m` with `d(x, m) = d(m, y) = d(x, y)/2` such that for every `z`,
  `d(z, m)² ≤ (d(z, x)² + d(z, y)²)/2 - d(x, y)²/4`.

## Implementation notes

In `IsCAT0`, the CAT(0) inequality is required for every comparison triangle `p` (they are unique
up to isometries of `𝔼²`), and a point of the side `γ i` is parametrized as
`γ i (s * d(x i, x (i + 1)))` with `s ∈ [0, 1]`, with comparison point
`AffineMap.lineMap (p i) (p (i + 1)) s`.

## Proof outline

For the CN inequality, `m` is the midpoint of a geodesic from `x` to `y`. For the geodesic
triangle with vertices `x, y, z`, the CAT(0) inequality compares `d(z, γ(t d(x, y)))` with the
distance from the comparison vertex `z̄` to the point `(1 - t) x̄ + t ȳ`, which is given by the
identity `|(1 - t) a + t b - c|² = (1 - t) |a - c|² + t |b - c|² - t (1 - t) |a - b|²` in `𝔼²`
(Apollonius' identity for `t = 1/2`). A comparison triangle for `x 0, x 1, x 2` is given
explicitly by `(0, 0)`, `(c, 0)` and `(u, √(b² - u²))`, where `c = d(x 0, x 1)`, `b = d(x 0, x 2)`,
`a = d(x 1, x 2)` and `u = (c² + b² - a²)/(2c)` (with `u = 0` if `c = 0`).

## References

* [G. Basso, *Lipschitz extension theorems with explicit constants*][Basso2024]
* M. R. Bridson and A. Haefliger, *Metric spaces of non-positive curvature*, Grundlehren Math.
  Wiss. 319, Springer, Berlin, 1999
-/

open Set Metric

namespace LipschitzExtension

variable {X : Type*} [MetricSpace X]

/-- `γ` is a geodesic from `x` to `y`: `γ 0 = x`, `γ (d(x, y)) = y` and `γ` is isometric on
`[0, d(x, y)]`. -/
def IsGeodesic (γ : ℝ → X) (x y : X) : Prop :=
  γ 0 = x ∧ γ (dist x y) = y ∧
    ∀ s ∈ Icc (0 : ℝ) (dist x y), ∀ t ∈ Icc (0 : ℝ) (dist x y), dist (γ s) (γ t) = |s - t|

/-- `X` is a geodesic space: any two points are joined by a geodesic. -/
def IsGeodesicSpace (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ : ℝ → X, IsGeodesic γ x y

/-- `p` is a comparison triangle in `𝔼²` for the three points `x 0, x 1, x 2`. -/
def IsComparisonTriangle (x : Fin 3 → X) (p : Fin 3 → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∀ i j, dist (p i) (p j) = dist (x i) (x j)

/-- **CAT(0) spaces** (Bridson–Haefliger, Definition II.1.1): `X` is a geodesic space and for every
geodesic triangle (vertices `x i`, sides `γ i` from `x i` to `x (i + 1)`) and every comparison
triangle `p`, any two points of the triangle are at distance at most the distance of their
comparison points. -/
def IsCAT0 (X : Type*) [MetricSpace X] : Prop :=
  IsGeodesicSpace X ∧
    ∀ (x : Fin 3 → X) (γ : Fin 3 → ℝ → X), (∀ i, IsGeodesic (γ i) (x i) (x (i + 1))) →
      ∀ p : Fin 3 → EuclideanSpace ℝ (Fin 2), IsComparisonTriangle x p →
        ∀ i j : Fin 3, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ i (s * dist (x i) (x (i + 1)))) (γ j (t * dist (x j) (x (j + 1)))) ≤
            dist (AffineMap.lineMap (p i) (p (i + 1)) s)
              (AffineMap.lineMap (p j) (p (j + 1)) t)

/-- Comparison triangles exist: any three points of a metric space have a comparison triangle in
`𝔼²`. -/
theorem exists_comparisonTriangle (x : Fin 3 → X) :
    ∃ p : Fin 3 → EuclideanSpace ℝ (Fin 2), IsComparisonTriangle x p := by
  -- `p 0 = (0, 0)`, `p 1 = (c, 0)`, `p 2 = (u, v)` with `u = (c² + b² - a²)/(2c)`,
  -- `v = √(b² - u²)`; if `c = 0` then `u = 0` (division by zero) and `a = b`.
  set c := dist (x 0) (x 1) with hcdef
  set b := dist (x 0) (x 2) with hbdef
  set a := dist (x 1) (x 2) with hadef
  set u := (c ^ 2 + b ^ 2 - a ^ 2) / (2 * c) with hudef
  set v := √(b ^ 2 - u ^ 2) with hvdef
  have hc : 0 ≤ c := dist_nonneg
  have hb : 0 ≤ b := dist_nonneg
  have ha : 0 ≤ a := dist_nonneg
  have h1 : a ≤ c + b := by
    have := dist_triangle (x 1) (x 0) (x 2)
    rw [dist_comm (x 1) (x 0)] at this
    linarith
  have h2 : b ≤ c + a := dist_triangle (x 0) (x 1) (x 2)
  have h3 : c ≤ b + a := by
    have := dist_triangle (x 0) (x 2) (x 1)
    rw [dist_comm (x 2) (x 1)] at this
    linarith
  have hu : u ^ 2 ≤ b ^ 2 := by
    rcases hc.eq_or_lt with hc0 | hc0
    · rw [hudef, ← hc0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, div_zero]
      positivity
    · rw [hudef, div_pow, div_le_iff₀ (by positivity)]
      have := mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ a - b + c)
        (by linarith : (0 : ℝ) ≤ a + b - c)) (by linarith : (0 : ℝ) ≤ b + c - a))
        (by linarith : (0 : ℝ) ≤ b + c + a)
      nlinarith
  have huv : u ^ 2 + v ^ 2 = b ^ 2 := by
    rw [hvdef, Real.sq_sqrt (by linarith)]
    ring
  have key : (c - u) ^ 2 + v ^ 2 = a ^ 2 := by
    rcases hc.eq_or_lt with hc0 | hc0
    · have hx : x 0 = x 1 := dist_eq_zero.1 hc0.symm
      have hab : a = b := by rw [hadef, hbdef, hx]
      have hu0 : u = 0 := by
        rw [hudef, ← hc0]
        simp only [mul_zero, div_zero]
      rw [← hc0, hu0, hab]
      nlinarith
    · have : 2 * c * u = c ^ 2 + b ^ 2 - a ^ 2 := by
        rw [hudef]
        field_simp
      nlinarith
  have e01 : dist (x 1) (x 0) = c := dist_comm _ _
  have e02 : dist (x 2) (x 0) = b := dist_comm _ _
  have e12 : dist (x 2) (x 1) = a := dist_comm _ _
  refine ⟨![!₂[0, 0], !₂[c, 0], !₂[u, v]], fun i j ↦ ?_⟩
  refine (sq_eq_sq₀ dist_nonneg dist_nonneg).1 ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Matrix.cons_val_fin_one, dist_self, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, EuclideanSpace.dist_sq_eq, Real.dist_eq,
      sq_abs, Fin.sum_univ_two, zero_sub, even_two, Even.neg_pow, sub_self, sub_zero, add_zero, e01,
      e02, e12] <;>
    first | rfl | exact huv | exact key | linarith [key]

/-- The Euclidean identity behind the CN inequality: for the point `(1 - t) a + t b` of the
segment `[a, b]` in a real inner product space and any point `c`,
`|(1 - t) a + t b - c|² = (1 - t) |a - c|² + t |b - c|² - t (1 - t) |a - b|²`. -/
private lemma norm_lineMap_sub_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) (t : ℝ) :
    ‖AffineMap.lineMap a b t - c‖ ^ 2 =
      (1 - t) * ‖a - c‖ ^ 2 + t * ‖b - c‖ ^ 2 - t * (1 - t) * ‖a - b‖ ^ 2 := by
  have e1 : AffineMap.lineMap a b t - c = (1 - t) • (a - c) + t • (b - c) := by
    rw [AffineMap.lineMap_apply_module]
    module
  have e2 : a - b = (a - c) - (b - c) := by abel
  rw [e1, e2]
  generalize a - c = u
  generalize b - c = v
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

/-- **The CN inequality along geodesics** in a CAT(0) space: if `γ` is a geodesic from `x` to `y`
and `t ∈ [0, 1]`, then
`d(z, γ(t d(x, y)))² ≤ (1 - t) d(z, x)² + t d(z, y)² - t (1 - t) d(x, y)²` for every `z` (compare
with the identity for the point `(1 - t) x̄ + t ȳ` of a comparison triangle in `𝔼²`). -/
theorem IsCAT0.dist_sq_le (hX : IsCAT0 X) {γ : ℝ → X} {x y : X} (hγ : IsGeodesic γ x y) (z : X)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist z (γ (t * dist x y)) ^ 2 ≤
      (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2 := by
  -- the geodesic triangle `x, y, z` with sides `γ`, `γ₁ : y → z`, `γ₂ : z → x`
  obtain ⟨γ₁, hγ₁⟩ := hX.1 y z
  obtain ⟨γ₂, hγ₂⟩ := hX.1 z x
  obtain ⟨p, hp⟩ := exists_comparisonTriangle ![x, y, z]
  have hgeo : ∀ i, IsGeodesic (![γ, γ₁, γ₂] i) (![x, y, z] i) (![x, y, z] (i + 1)) := by
    intro i
    fin_cases i
    · exact hγ
    · exact hγ₁
    · exact hγ₂
  -- compare `γ (t d(x, y))` on the side `γ` with the vertex `z = γ₂ 0`
  have h := hX.2 ![x, y, z] ![γ, γ₁, γ₂] hgeo p hp 0 2 t ht 0 ⟨le_rfl, zero_le_one⟩
  simp only [Fin.isValue, Matrix.cons_val_zero, zero_add, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.cons_val_fin_one, Matrix.cons_val, Fin.reduceAdd, zero_mul,
    AffineMap.lineMap_apply_zero] at h
  rw [hγ₂.1] at h
  have h01 := hp 0 1
  have h02 := hp 0 2
  have h12 := hp 1 2
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h01 h02 h12
  have e : dist (AffineMap.lineMap (p 0) (p 1) t) (p 2) ^ 2 =
      (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2 := by
    rw [dist_eq_norm, norm_lineMap_sub_sq, ← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm, h01,
      h02, h12, dist_comm x z, dist_comm y z]
  rw [dist_comm, ← e]
  exact pow_le_pow_left₀ dist_nonneg h 2

/-- **The CN inequality of Bruhat–Tits** in a CAT(0) space: every pair of points has a midpoint `m`
with `d(z, m)² ≤ (d(z, x)² + d(z, y)²)/2 - d(x, y)²/4` for all `z`. -/
theorem IsCAT0.exists_midpoint (hX : IsCAT0 X) (x y : X) :
    ∃ m : X, dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : X, dist z m ^ 2 ≤ (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4 := by
  obtain ⟨γ, hγ⟩ := hX.1 x y
  have hd : 0 ≤ dist x y := dist_nonneg
  have hmem : 1 / 2 * dist x y ∈ Icc (0 : ℝ) (dist x y) := ⟨by positivity, by linarith⟩
  refine ⟨γ (1 / 2 * dist x y), ?_, ?_, fun z ↦ ?_⟩
  · have := hγ.2.2 0 ⟨le_rfl, hd⟩ _ hmem
    rw [hγ.1] at this
    rw [this, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    ring
  · have := hγ.2.2 _ hmem (dist x y) ⟨hd, le_rfl⟩
    rw [hγ.2.1] at this
    rw [this, abs_of_nonpos (by linarith)]
    ring
  · have := hX.dist_sq_le hγ z (t := 1 / 2) ⟨by norm_num, by norm_num⟩
    linarith

end LipschitzExtension
