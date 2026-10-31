import Mathlib

/-!
# Five-dimensional free scalar spectrum, JHEP11(2024)014

Exact analytic Laplace integrals underlying the untruncated moment series.
This file does not assume the original weight is Meixner-Pollaczek.
-/

open MeasureTheory Set Real

namespace Scalar2024

theorem laplace_monomial (k : ℕ) (a : ℝ) (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), x ^ k * Real.exp (-(a * x))) =
      (k.factorial : ℝ) / a ^ (k + 1) := by
  have hk : (0 : ℝ) < ↑k + 1 := by positivity
  have h := integral_rpow_mul_exp_neg_mul_Ioi hk ha
  calc
    (∫ x in Ioi (0 : ℝ), x ^ k * Real.exp (-(a * x))) =
      (∫ x in Ioi (0 : ℝ),
        x ^ ((k : ℝ) + 1 - 1) * Real.exp (-(a * x))) := by
          congr 1
          funext x
          simp [Real.rpow_natCast]
    _ = (1 / a) ^ ((k : ℝ) + 1) * Gamma ((k : ℝ) + 1) := h
    _ = (k.factorial : ℝ) / a ^ (k + 1) := by
          have hG : Gamma ((k : ℝ) + 1) = (k.factorial : ℝ) :=
            Gamma_nat_eq_factorial k
          have hpow : (1 / a) ^ ((k : ℝ) + 1) = (1 / a) ^ (k + 1) := by
            norm_cast
          rw [hG, hpow]
          simp [one_div, inv_pow, div_eq_mul_inv, mul_comm]

theorem massive_gap_shift (m x : ℝ) :
    (m + x) ^ 2 - m ^ 2 = x ^ 2 + 2 * m * x := by ring

theorem massive_shifted_integrand (m x : ℝ) (n : ℕ) :
    ((m + x) ^ 2 - m ^ 2) * (m + x) ^ (2 * n) =
      x ^ 2 * (m + x) ^ (2 * n) +
      2 * m * x * (m + x) ^ (2 * n) := by
  rw [massive_gap_shift]
  ring

theorem gamma_tail_at_degree_zero (m a : ℝ) (ha : a ≠ 0) :
    (2 : ℝ) / a ^ 3 + 2 * m / a ^ 2 =
      2 * (m * a + 1) / a ^ 3 := by
  field_simp
  <;> ring

/-- massless moments carry an exact beta^-2n dimensional scaling. -/
theorem massless_moment_scale (n : ℕ) (beta z3 zOdd : ℝ)
    (hb : beta ≠ 0) (hz : z3 ≠ 0) :
    ((n * 2 + 2).factorial : ℝ) * zOdd /
      (2 * z3 * beta ^ (2 * n)) =
    (1 / beta ^ (2 * n)) *
      (((n * 2 + 2).factorial : ℝ) * zOdd / (2 * z3)) := by
  field_simp
  <;> ring

theorem massless_second_polynomial_norm (mu2 mu4 : ℝ) :
    mu4 - 2 * mu2 * mu2 + mu2 ^ 2 = mu4 - mu2 ^ 2 := by ring

/-- First two Lanczos coefficients from two even moments, as a
    Gram-Schmidt identity, without assuming a specific spectral family. -/
theorem massless_lanczos_first_two
    (mu2 mu4 b1sq b2sq : ℝ) (h2 : mu2 ≠ 0)
    (hb1 : b1sq = mu2)
    (hnorm : b1sq * b2sq = mu4 - mu2 ^ 2) :
    b2sq = mu4 / mu2 - mu2 := by
  rw [hb1] at hnorm
  apply (mul_left_cancel₀ h2)
  calc
    mu2 * b2sq = mu4 - mu2 ^ 2 := hnorm
    _ = mu2 * (mu4 / mu2 - mu2) := by field_simp

end Scalar2024
