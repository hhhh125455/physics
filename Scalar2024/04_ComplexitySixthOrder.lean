import Mathlib

/-!
# Sixth-order exact short-time Krylov complexity for JHEP11(2024)014

For ANY symmetric scalar Wightman measure having finite positive moments
A=mu_2, B=mu_4, C=mu_6, the t^6 Taylor coefficient is
C/60 + A*B/12 - B^2/(18*A). The proof checks the exact algebra
of the Lanczos paths b1,b2,b3 and the moment identities.

Finite-order Taylor expansion of exp(-itJ) and uniform control of its
O(t^8) remainder are analytic inputs, not asserted as Lean-proven here.
-/

namespace Scalar2024

/-- The sixth moment from length-three paths on an even Jacobi chain. -/
theorem even_sixth_moment_paths (b1 b2 b3 : ℝ) :
    b1 ^ 2 * ((b1 ^ 2 + b2 ^ 2) ^ 2 + b2 ^ 2 * b3 ^ 2) =
    b1 ^ 6 + 2 * b1 ^ 4 * b2 ^ 2 +
      b1 ^ 2 * b2 ^ 4 + b1 ^ 2 * b2 ^ 2 * b3 ^ 2 := by
  ring

/-- Fourth-order complexity coefficient written using the second
and fourth spectral moments. -/
theorem fourth_order_complexity_from_moments
    (b1 b2 A B : ℝ)
    (hA : A = b1 ^ 2)
    (hB : B = b1 ^ 2 * (b1 ^ 2 + b2 ^ 2)) :
    b1 ^ 2 * (b2 ^ 2 / 6 - b1 ^ 2 / 3) =
      (B - 3 * A ^ 2) / 6 := by
  rw [hA, hB]
  ring

/-- Sixth-order coefficient after summing the contributions from
the first three Krylov sites at order t^6. -/
theorem sixth_order_complexity_from_moments
    (b1 b2 b3 A B C : ℝ)
    (hA : A = b1 ^ 2)
    (hApos : A ≠ 0)
    (hB : B = b1 ^ 2 * (b1 ^ 2 + b2 ^ 2))
    (hC : C = b1 ^ 2 *
      ((b1 ^ 2 + b2 ^ 2) ^ 2 + b2 ^ 2 * b3 ^ 2)) :
    b1 ^ 2 *
      ( (2 / 45 : ℝ) * (b1 ^ 2 + b2 ^ 2) ^ 2
        - (1 / 12 : ℝ) * b2 ^ 2 * (b1 ^ 2 + b2 ^ 2)
        + (1 / 60 : ℝ) * b2 ^ 2 * b3 ^ 2) =
      C / 60 + A * B / 12 - B ^ 2 / (18 * A) := by
  have hb1 : b1 ^ 2 ≠ 0 := by
    rw [hA] at hApos
    exact hApos
  rw [hA, hB, hC]
  field_simp [hb1]
  <;> ring

/-- The alternative simplified numerator for the same t^6 coefficient. -/
theorem sixth_order_coefficient_numerator
    (A B C : ℝ) (hA : A ≠ 0) :
    C / 60 + A * B / 12 - B ^ 2 / (18 * A) =
      (3 * A * C + 15 * A ^ 2 * B - 10 * B ^ 2) /
        (180 * A) := by
  field_simp [hA]
  <;> ring

/-- Exact dimensionless scaling of the sixth-order coefficient under
the true moment scaling mu_{2n}(beta,m)=beta^{-2n} f_{2n}(beta*m). -/
theorem sixth_order_temperature_scaling
    (beta A B C : ℝ) (hbeta : beta ≠ 0) (hA : A ≠ 0) :
    (C / beta ^ 6) / 60 +
      (A / beta ^ 2) * (B / beta ^ 4) / 12 -
      (B / beta ^ 4) ^ 2 / (18 * (A / beta ^ 2)) =
      (C / 60 + A * B / 12 - B ^ 2 / (18 * A)) / beta ^ 6 := by
  field_simp [hbeta, hA]
  <;> ring

end Scalar2024
