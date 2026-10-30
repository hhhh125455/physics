import Mathlib

/-!
# Initial-data response at the reflection-symmetric center

On t=0 the original Hamiltonian Einstein constraint is, in X=r²,

 Xxx + sigma_x*Xx - Xx²/(4X) + k*X*phi_x²
    - E*(1-q²/X) = 0,   k=4*pi.

Multiply by 4X (assuming X>0) to make it polynomial:

 4X Xxx + 4X sigma_x Xx - Xx²
    + 4k X² phi_x² - 4E(X-q²) = 0.

For odd initial profile phi(0,x;A)=A*tanh(x/C), the center x=0 has
 phi_x=A/C, Xx=0 and sigma_x=0. The center X0=r_+², E and C are
 independent of A (the paper's fixed initial conformal gauge).
 Therefore the initial spatial curvature is
 X_xx(0;A) = E(1-q²/X0) - k X0 A²/C².

This file formalizes the exact center reduction and proves that this
initial curvature strictly decreases as A increases in the positive
amplitude family. It does NOT imply monotonicity of X_S at later times.
-/

namespace GammaHalf

private def initConstraintP
    (X Xx Xxx Sx E Phix q2 k : ℝ) : ℝ :=
    4 * X * Xxx + 4 * X * Sx * Xx - Xx ^ 2 +
      4 * k * X ^ 2 * Phix ^ 2 - 4 * E * (X - q2)

noncomputable def initialCenterCurvature
    (X0 E q2 k B A : ℝ) : ℝ :=
  E * (1 - q2 / X0) - k * X0 * A ^ 2 * B ^ 2

theorem initial_center_constraint_reduction
    (X0 E q2 k B A Xxx : ℝ) (hX : X0 ≠ 0)
    (hconstraint : initConstraintP X0 0 Xxx 0 E (A * B) q2 k = 0) :
    Xxx = initialCenterCurvature X0 E q2 k B A := by
  unfold initConstraintP at hconstraint
  unfold initialCenterCurvature
  field_simp [hX]
  nlinarith [hconstraint]

/-- Exact finite-amplitude variation of the initial constraint
    curvature at the center; no approximation. -/
theorem center_curvature_finite_difference
    (X0 E q2 k B A h : ℝ) :
    initialCenterCurvature X0 E q2 k B (A + h) -
      initialCenterCurvature X0 E q2 k B A =
      -(k * X0 * B ^ 2 * h * (2 * A + h)) := by
  unfold initialCenterCurvature
  ring

/-- For positive coupling, horizon radius, and slope magnitude,
    increasing the positive initial amplitude makes X_xx strictly smaller. -/
theorem center_curvature_strictly_decreasing
    (X0 E q2 k B A h : ℝ)
    (hX0 : 0 < X0) (hk : 0 < k) (hB : B ≠ 0)
    (hA : 0 ≤ A) (hh : 0 < h) :
    initialCenterCurvature X0 E q2 k B (A + h) <
      initialCenterCurvature X0 E q2 k B A := by
  have hs : 0 < 2 * A + h := by linarith
  have hBs : 0 < B ^ 2 := sq_pos_of_ne_zero hB
  have hpos : 0 < k * X0 * B ^ 2 * h * (2 * A + h) := by
    positivity
  have hdiff := center_curvature_finite_difference X0 E q2 k B A h
  linarith

/-- The infinitesimal initial source in the variational constraint
    at x=0 is strictly negative for A>0. -/
theorem negative_center_initial_kick
    (X0 k B A : ℝ)
    (hX0 : 0 < X0) (hk : 0 < k) (hB : B ≠ 0)
    (hA : 0 < A) :
    -(2 * k * X0 * B ^ 2 * A) < 0 := by
  have hBs : 0 < B ^ 2 := sq_pos_of_ne_zero hB
  have hpos : 0 < 2 * k * X0 * B ^ 2 * A := by positivity
  linarith

/-- The linearized area evolution equation at the initial symmetric
    center forces the time and space second variations to coincide.
    If the initial area and conformal factor are fixed there (Y=Z=0),
    the negative initial spatial kick is also the time kick. -/
theorem negative_initial_time_kick
    (X0 E q2 k A B Ytt Yxx Y Z : ℝ)
    (hX0 : X0 ≠ 0)
    (hY : Y = 0) (hZ : Z = 0)
    (harea :
      X0 ^ 2 * (Ytt - Yxx) +
        2 * E * q2 * Y + 4 * E * X0 * Z * (q2 - X0) = 0)
    (hxx : Yxx = -(2 * k * X0 * B ^ 2 * A)) :
    Ytt = -(2 * k * X0 * B ^ 2 * A) := by
  have hprod : (X0 ^ 2) * (Ytt - Yxx) = 0 := by
    simpa only [hY, hZ, mul_zero, zero_mul, add_zero] using harea
  have hcoef : X0 ^ 2 ≠ 0 := pow_ne_zero 2 hX0
  have hdiff : Ytt - Yxx = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hcoef
  linarith [hxx]


end GammaHalf
