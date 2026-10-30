import Mathlib

/-!
# Geometric curvature lower bound and near-critical consequences

This formalizes the curvature square-completion of
Fu-Guo Yang, arXiv:2610.40043 (2026-10-29).

Let W be the spherical Weyl amplitude, e=q^2/r^4 be the
electromagnetic invariant, and s=pi*(grad phi)^2, which can have
either sign. The exact curvature decomposition is

  K = 48 W^2 + 8 e^2 - 32 e s + (320/3) s^2.

Completion of squares gives
  K >= (28/5) e^2 = (28/5) q^4/r^8.

In the gamma problem write X=r^2. If 0<X<=c*(A*-A),
then K*c^4*(A*-A)^4 >= (28/5)q^4.
This rules out a uniformly bounded K*(A*-A)^3 all the way to
the charged singularity at fixed nonzero q.

The geometric curvature decomposition is a *physical premise*
identified in the cited source, not derived from a tensor library
here. Lean checks the exact square-completion, inequalities and
scaling implications, with no proof placeholders.
-/

namespace GammaHalf

private def geometricK (W e s : ℝ) : ℝ :=
  48 * W ^ 2 + 8 * e ^ 2 - 32 * e * s +
     (320 / 3 : ℝ) * s ^ 2

/-- Exact completion of the square for charged Einstein-real-scalar
    spherical curvature. -/
theorem curvature_square_completion (W e s : ℝ) :
    geometricK W e s =
      48 * W ^ 2 +
      (320 / 3 : ℝ) * (s - 3 * e / 20) ^ 2 +
      (28 / 5 : ℝ) * e ^ 2 := by
  unfold geometricK
  ring

/-- At every regular point this algebra yields a positive electric
    curvature floor, regardless of the scalar-gradient sign. -/
theorem curvature_electric_floor (W e s : ℝ) :
    (28 / 5 : ℝ) * e ^ 2 ≤ geometricK W e s := by
  rw [curvature_square_completion]
  have hw : 0 ≤ 48 * W ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg W)
  have hs : 0 ≤ (320 / 3 : ℝ) * (s - 3 * e / 20) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  linarith

/-- Write X=r^2, e=q^2/X^2. The exact bound contains no
    denominator after multiplying through by X^4. -/
theorem curvature_area_power_lower
    (K X q e W s : ℝ)
    (hX : 0 < X) (he : e * X ^ 2 = q ^ 2)
    (hK : K = geometricK W e s) :
    (28 / 5 : ℝ) * q ^ 4 ≤ K * X ^ 4 := by
  have hbound := curvature_electric_floor W e s
  have hpow : 0 ≤ X ^ 4 := pow_nonneg (le_of_lt hX) 4
  have hmul := mul_le_mul_of_nonneg_right hbound hpow
  have heq : e ^ 2 * X ^ 4 = q ^ 4 := by
    calc
      e ^ 2 * X ^ 4 = (e * X ^ 2) ^ 2 := by ring
      _ = (q ^ 2) ^ 2 := by rw [he]
      _ = q ^ 4 := by ring
  rw [hK]
  nlinarith [hmul, heq]

/-- If the area has a one-sided linear upper bound X<=c*delta,
    then the true curvature diverges at least as delta^(-4).
    No differentiability of X in delta is assumed here. -/
theorem linear_area_forces_inverse_fourth_curvature
    (K X q c delta : ℝ)
    (hX : 0 < X) (hc : 0 < c) (hd : 0 < delta)
    (harea : X ≤ c * delta)
    (hcurv : (28 / 5 : ℝ) * q ^ 4 ≤ K * X ^ 4) :
    (28 / 5 : ℝ) * q ^ 4 ≤ K * c ^ 4 * delta ^ 4 := by
  have hK : 0 ≤ K := by
    by_contra hh
    have hKn : K < 0 := lt_of_not_ge hh
    have hp : 0 < X ^ 4 := pow_pos hX 4
    have hm := mul_neg_of_neg_of_pos hKn hp
    have hq : 0 ≤ (28 / 5 : ℝ) * q ^ 4 := by positivity
    linarith
  have hpow : X ^ 4 ≤ (c * delta) ^ 4 := by
    gcongr
  calc
    (28 / 5 : ℝ) * q ^ 4 ≤ K * X ^ 4 := hcurv
    _ ≤ K * (c * delta) ^ 4 :=
      mul_le_mul_of_nonneg_left hpow hK
    _ = K * c ^ 4 * delta ^ 4 := by ring

/-- A radius sixth-power bound K*X^3<=C together with charge
    forces X to be bounded away from zero at fixed q and C. -/
theorem sixth_power_law_excludes_tiny_charged_radius
    (K X q C : ℝ)
    (hX : 0 < X)
    (hcurv : (28 / 5 : ℝ) * q ^ 4 ≤ K * X ^ 4)
    (hsixth : K * X ^ 3 ≤ C) :
    (28 / 5 : ℝ) * q ^ 4 ≤ C * X := by
  have hmul := mul_le_mul_of_nonneg_right hsixth (le_of_lt hX)
  nlinarith [hmul, hcurv]

/-- On a linear-area branch, any finite upper bound K*delta^3<=M
    forces a lower bound on delta: the mass-dominated inverse-cube
    stage cannot be the exact critical limit at fixed nonzero charge. -/
theorem inverse_cube_stage_must_end
    (K X q c delta M : ℝ)
    (hX : 0 < X) (hc : 0 < c) (hd : 0 < delta)
    (harea : X ≤ c * delta)
    (hcurv : (28 / 5 : ℝ) * q ^ 4 ≤ K * X ^ 4)
    (hcube : K * delta ^ 3 ≤ M) :
    (28 / 5 : ℝ) * q ^ 4 ≤ M * c ^ 4 * delta := by
  have hfloor :=
    linear_area_forces_inverse_fourth_curvature K X q c delta
      hX hc hd harea hcurv
  have hmult := mul_le_mul_of_nonneg_right hcube (le_of_lt hd)
  have hcsq : 0 ≤ c ^ 4 := pow_nonneg (le_of_lt hc) 4
  have hmult2 := mul_le_mul_of_nonneg_right hmult hcsq
  nlinarith [hfloor, hmult2]

end GammaHalf
