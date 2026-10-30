import ClassicalSpinKrylov

/-!
# Reduced classical-spin correlation integral

This module defines the one-dimensional correlation integral as a genuine
interval integral. It verifies normalization at zero time, its evenness,
and the zero-coupling case.

It does not yet derive the reduced weight from the spherical measure, and
it does not yet prove the trigonometric closed form.
-/

open MeasureTheory intervalIntegral

namespace ClassicalSpinKrylov

/-- Reduced spectral correlation associated with ρ(z)=(3/4)(1-z²). -/
noncomputable def correlation (c t : ℝ) : ℝ :=
  (3 / 4 : ℝ) *
    (∫ z : ℝ in -1..1, (1 - z ^ 2) * Real.cos (c * z * t))

/-- The reduced weight is normalized without making a new assumption. -/
theorem reduced_weight_integral :
    (∫ z : ℝ in -1..1, 1 - z ^ 2) = 4 / 3 := by
  simpa using (spin_weight_integral 0)

/-- Exact normalization C(0)=1. -/
theorem correlation_zero (c : ℝ) : correlation c 0 = 1 := by
  have h := reduced_weight_integral
  norm_num [correlation, h]

/-- Exact evenness under time reversal C(-t)=C(t). -/
theorem correlation_even (c t : ℝ) :
    correlation c (-t) = correlation c t := by
  unfold correlation
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  simp only [mul_neg, Real.cos_neg]

/-- If the rotation frequency is zero the correlation remains 1. -/
theorem correlation_zero_frequency (t : ℝ) :
    correlation 0 t = 1 := by
  have h := reduced_weight_integral
  norm_num [correlation, h]

end ClassicalSpinKrylov
