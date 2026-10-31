import Mathlib

/-!
# TTbar TFD: exact first nontrivial Jacobi data and Hagedorn scaling

This file rigorously verifies the algebraic link from four/five cumulants to
a_1, b_2, a_2, and the EXACT rescaling identities near the Hagedorn branch.

There is no weak-deformation expansion. The all-n near-critical asymptotic
still requires an analytic orthogonal-polynomial convergence theorem;
we do not claim it is fully proved by this file.

Definitions:
  d = sqrt(beta^2 - betaH^2)
  betaH = 2 sqrt(mu A)
  t = d^2 / (2 beta)   (inverse emerging spectral energy scale)
  b_1^2=2 A / d^3, etc.
-/

namespace TTbarAnalyticCritical

noncomputable def k2 (A d : ℝ) : ℝ := 2*A/d^3
noncomputable def k3 (A β d : ℝ) : ℝ := 6*A*β/d^5
noncomputable def k4 (A β d : ℝ) : ℝ := 6*A*(5*β^2-d^2)/d^7
noncomputable def k5 (A β d : ℝ) : ℝ := 30*A*β*(7*β^2-3*d^2)/d^9

noncomputable def B2 (A β d : ℝ) : ℝ :=
  (4*A*d+6*β^2-3*d^2)/d^4

noncomputable def A1offset (β d : ℝ) : ℝ := 3*β/d^2

noncomputable def A2offset (A β d : ℝ) : ℝ :=
  3*β*(8*A*d+14*β^2-9*d^2)/
    (d^2*(4*A*d+6*β^2-3*d^2))

noncomputable def scale (β d : ℝ) : ℝ := d^2/(2*β)

/-- Central fourth moment and third cumulant give the EXACT b_2²,
    written without any division by a cumulant. -/
theorem exact_b2_cumulant_identity (A β d : ℝ) (hd : d ≠ 0) :
    (k2 A d)^2 * B2 A β d =
      (k2 A d)*(k4 A β d) +
        2*(k2 A d)^3 - (k3 A β d)^2 := by
  unfold k2 k3 k4 B2
  field_simp [hd] <;> ring

/-- Denominator-cleared polynomial identity for a_2. This is a
    nontrivial exact cumulant identity, requiring only d ≠ 0. -/
theorem exact_a2_cumulant_poly (A β d : ℝ) (hd : d ≠ 0) :
    (k2 A d)^3 * B2 A β d *
      (3*β*(8*A*d+14*β^2-9*d^2)) =
    ((k2 A d)^2*k5 A β d +
      4*(k2 A d)^3*k3 A β d -
      2*k2 A d*k3 A β d*k4 A β d +
      (k3 A β d)^3) *
       (d^2*(4*A*d+6*β^2-3*d^2)) := by
  unfold k2 k3 k4 k5 B2
  field_simp [hd] <;> ring

/-- The centered fifth moment gives the exact a_2 correction
    after combining the second and fourth moment equations. -/
theorem exact_a2_cumulant_identity (A β d : ℝ)
    (hd : d ≠ 0)
    (hH : 4*A*d+6*β^2-3*d^2 ≠ 0) :
    (k2 A d)^3 * B2 A β d * A2offset A β d =
      (k2 A d)^2 * k5 A β d +
      4*(k2 A d)^3 * k3 A β d -
      2*k2 A d*k3 A β d*k4 A β d +
      (k3 A β d)^3 := by
  have hden : d^2*(4*A*d+6*β^2-3*d^2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hd) hH
  have hp := exact_a2_cumulant_poly A β d hd
  unfold A2offset
  calc
    (k2 A d)^3 * B2 A β d *
        (3*β*(8*A*d+14*β^2-9*d^2)/
          (d^2*(4*A*d+6*β^2-3*d^2))) =
      ((k2 A d)^3 * B2 A β d *
        (3*β*(8*A*d+14*β^2-9*d^2))) /
          (d^2*(4*A*d+6*β^2-3*d^2)) := by ring
    _ = (((k2 A d)^2*k5 A β d +
      4*(k2 A d)^3*k3 A β d -
      2*k2 A d*k3 A β d*k4 A β d +
      (k3 A β d)^3) *
      (d^2*(4*A*d+6*β^2-3*d^2))) /
        (d^2*(4*A*d+6*β^2-3*d^2)) := by rw [hp]
    _ = (k2 A d)^2*k5 A β d +
      4*(k2 A d)^3*k3 A β d -
      2*k2 A d*k3 A β d*k4 A β d +
      (k3 A β d)^3 := by
      field_simp [hden]

/-- First shifted Jacobi diagonal in the centered variable. -/
theorem exact_a1_from_variance (A β d : ℝ)
    (hA : A ≠ 0) (hd : d ≠ 0) :
    k3 A β d / k2 A d = A1offset β d := by
  unfold k2 k3 A1offset
  field_simp [hA, hd] <;> ring

/-- Near-Hagedorn scale: exact a_1 shift, independent of deformation. -/
theorem scaled_a1 (β d : ℝ) (hβ : β ≠ 0) (hd : d ≠ 0) :
    scale β d * A1offset β d = 3/2 := by
  unfold scale A1offset
  field_simp [hβ, hd] <;> ring

/-- Exact first off-diagonal critical relation: t² b_1² ~ A d/(2β²). -/
theorem scaled_b1_sq (A β d : ℝ) (hβ : β ≠ 0) (hd : d ≠ 0) :
    (scale β d)^2 * k2 A d = A*d/(2*β^2) := by
  unfold scale k2
  field_simp [hβ, hd] <;> ring

/-- Exact second off-diagonal critical relation, no asymptotic symbol. -/
theorem scaled_b2_sq (A β d : ℝ) (hβ : β ≠ 0) (hd : d ≠ 0) :
    (scale β d)^2 * B2 A β d =
      (4*A*d+6*β^2-3*d^2)/(4*β^2) := by
  unfold scale B2
  field_simp [hβ, hd] <;> ring

/-- Exact second shifted diagonal critical relation. -/
theorem scaled_a2 (A β d : ℝ) (hβ : β ≠ 0) (hd : d ≠ 0) :
    scale β d * A2offset A β d =
      3*(8*A*d+14*β^2-9*d^2)/
        (2*(4*A*d+6*β^2-3*d^2)) := by
  unfold scale A2offset
  field_simp [hβ, hd] <;> ring

/-- Critical limiting values are regular rational functions in d,
    and their values at d=0 are 3/2 and 7/2. -/
theorem scaled_a2_at_d_zero (A β : ℝ) (hβ : β ≠ 0) :
    3*(8*A*0+14*β^2-9*0^2)/
      (2*(4*A*0+6*β^2-3*0^2)) = 7/2 := by
  field_simp [hβ] <;> ring

theorem scaled_b2_at_d_zero (A β : ℝ) (hβ : β ≠ 0) :
    (4*A*0+6*β^2-3*0^2)/(4*β^2) = 3/2 := by
  field_simp [hβ] <;> ring

/-- Connection between the new scale t and delta=beta-betaH. -/
theorem exact_hagedorn_scale (β betaH d : ℝ)
    (h : d^2 = β^2-betaH^2) :
    d^2 = (β-betaH)*(β+betaH) := by
  rw [h]
  ring

theorem scale_over_gap (β betaH d : ℝ)
    (hβ : β ≠ 0) (hgap : β-betaH ≠ 0)
    (h : d^2 = β^2-betaH^2) :
    scale β d / (β-betaH) = (β+betaH)/(2*β) := by
  unfold scale
  rw [exact_hagedorn_scale β betaH d h]
  field_simp [hβ, hgap] <;> ring

/-- The limiting scaled moments have the gamma-shift recurrence:
    c_1=1/2, c_(n+1)=(n-1/2)c_n.
    These are the moments of x^(-3/2) exp(-x) (for n>=1),
    up to a positive common factor. -/
def limitingMoment : ℕ → ℚ
  | 0 => 0
  | 1 => 1/2
  | n+2 => ((2*(n:ℚ)+1)/2) * limitingMoment (n+1)

theorem limiting_moment_one : limitingMoment 1 = 1/2 := rfl

theorem limiting_moment_succ (n : ℕ) :
    limitingMoment (n+2) =
      ((2*(n:ℚ)+1)/2)*limitingMoment (n+1) := rfl

theorem limiting_moment_pos (n : ℕ) :
    0 < limitingMoment (n+1) := by
  induction n with
  | zero =>
    norm_num [limitingMoment]
  | succ n ih =>
    rw [limiting_moment_succ]
    apply mul_pos
    · positivity
    · exact ih

end TTbarAnalyticCritical
