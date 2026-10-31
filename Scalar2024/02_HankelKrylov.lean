import Mathlib

/-!
# Exact first Krylov coefficients of the five-dimensional massless scalar.

This is a formal algebraic part of the frozen original Wightman measure.
Moments are not replaced by a Meixner-Pollaczek model.

Independent analytic integration identifies the concrete moments with
Riemann zeta values; that analytic identification is NOT a hypothesis
silently inferred by Lean from these abstract moment variables.
-/

namespace Scalar2024

/-- The even moment Hankel determinant H_4 factorizes exactly. -/
theorem even_hankel_four_factor (A B C : ℝ) :
    (B - A ^ 2) * (A * C - B ^ 2) =
      A * B * C - B ^ 3 - A ^ 3 * C + A ^ 2 * B ^ 2 := by ring

/-- Exact third Lanczos coefficient obtained from the 4x4 Hankel
determinant, with no odd moments in a symmetric Wightman spectrum. -/
theorem massless_b3_hankel (A B C : ℝ)
    (hA : A ≠ 0) (hvar : B - A ^ 2 ≠ 0) :
    (((B - A ^ 2) * (A * C - B ^ 2)) * A) /
        (A * (B - A ^ 2)) ^ 2 =
      (A * C - B ^ 2) / (A * (B - A ^ 2)) := by
  field_simp
  <;> ring

/-- Meixner-Pollaczek obstruction, at the first two Lanczos steps:
for the actual 5D massless moment values B < 3*A²,
the squared coefficient ratio is smaller than two. -/
theorem massless_not_symmetric_mp_if_kurtosis_small
    (A B : ℝ) (hA : 0 < A) (hB : B < 3 * A ^ 2) :
    B / A - A < 2 * A := by
  apply (div_lt_iff₀ hA).mpr
  nlinarith

/-- Positive-parameter symmetric Meixner-Pollaczek coefficients have
b_2² / b_1² = 2 + 1/lambda > 2, contradicting the preceding bound. -/
theorem mp_positive_parameter_ratio (lambda : ℝ) (hl : 0 < lambda) :
    2 < 2 + 1 / lambda := by
  have h : 0 < 1 / lambda := div_pos one_pos hl
  linarith

/-- t^4 coefficient of the exact Krylov expansion from the first
two Lanczos coefficients. An analytic propagator argument is separately
needed to establish the Taylor remainder. -/
theorem fourth_order_krylov_coefficient
    (A B b2sq : ℝ) (hb2 : A * b2sq = B - A ^ 2) :
    -(A ^ 2) / 3 + (A * b2sq) / 6 =
      (B - 3 * A ^ 2) / 6 := by
  linarith

/-- Fourth cumulant of a centered even spectral measure is B-3A². -/
theorem fourth_cumulant_sign
    (A B : ℝ) (hB : B < 3 * A ^ 2) :
    (B - 3 * A ^ 2) / 6 < 0 := by linarith

end Scalar2024
