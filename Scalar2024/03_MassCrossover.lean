import Mathlib

/-!
# JHEP11(2024)014: exact mass-dependence algebra and frequency scaling

Frozen spectral measure: (omega^2-m^2) / sinh(beta*abs omega/2),
supported on |omega|>=m. Let M=beta*m and define
I_{2n}(M) as the dimensionless unnormalized positive-side moments.

Theorems in this file check ratio identities and Lanczos scaling exactly.
The leading M^2*log(M) normalization expansion is derived by analytic
integration in the accompanying report; it is NOT claimed proved by
the generic ratio identity alone.
-/

namespace Scalar2024

/-- How any correction to an unnormalized spectral moment and its
normalization propagates to the normalized moment. -/
theorem normalized_moment_exact_difference
    (Z J dZ dJ : ℝ) (hZ : Z ≠ 0)
    (hZnew : Z + dZ ≠ 0) :
    (J + dJ) / (Z + dZ) - J / Z =
      (Z * dJ - J * dZ) / (Z * (Z + dZ)) := by
  field_simp [hZ, hZnew]
  <;> ring

/-- When the raw moments are I0,I2,I4, the common normalization
cancels from the ratio mu4/mu2. -/
theorem lanczos_second_square_from_unnormalized
    (I0 I2 I4 : ℝ) (hI0 : I0 ≠ 0) (hI2 : I2 ≠ 0) :
    (I4 / I0) / (I2 / I0) - I2 / I0 =
      I4 / I2 - I2 / I0 := by
  field_simp [hI0, hI2]
  <;> ring

/-- Exact cancellation of the large mass parameter in the even
sector norm ratio, with the physical polynomial x^2 rescaling. -/
theorem even_sector_mass_cancel
    (M hEven hOdd hReference : ℝ)
    (hM : M ≠ 0) (hRef : hReference ≠ 0)
    (hOddEq : hOdd = M ^ 2 * hReference) :
    (2 * M) ^ 2 * hEven / hOdd =
      4 * hEven / hReference := by
  rw [hOddEq]
  field_simp [hM, hRef]
  <;> ring

/-- The exact algebraic remainder for the large-M odd coefficient:
if b²=M²+2 M a+r, then b-(M+a)=(r-a²)/(b+M+a).
An O(1/M) consequence requires a separate uniform bound on r. -/
theorem odd_sector_exact_remainder
    (M a b r : ℝ) (hden : b + M + a ≠ 0)
    (hb : b ^ 2 = M ^ 2 + 2 * M * a + r) :
    b - (M + a) = (r - a ^ 2) / (b + M + a) := by
  field_simp [hden]
  nlinarith [hb]

/-- Arbitrary-degree real Jacobi recurrence has exact beta scaling;
no assumption is made that the scalar field is an MP model. -/
theorem rescaled_jacobi_recurrence
    (p : ℕ → ℝ → ℝ) (b : ℕ → ℝ)
    (beta : ℝ) (hbeta : beta ≠ 0)
    (hRec : ∀ (n : ℕ) (x : ℝ),
      x * p (n + 1) x =
        b (n + 2) * p (n + 2) x + b (n + 1) * p n x)
    (n : ℕ) (omega : ℝ) :
    omega * p (n + 1) (beta * omega) =
      (b (n + 2) / beta) * p (n + 2) (beta * omega)
        + (b (n + 1) / beta) * p n (beta * omega) := by
  calc
    omega * p (n + 1) (beta * omega) =
      ((beta * omega) * p (n + 1) (beta * omega)) / beta := by
        field_simp [hbeta]
    _ = (b (n + 2) * p (n + 2) (beta * omega) +
         b (n + 1) * p n (beta * omega)) / beta := by
           rw [hRec n (beta * omega)]
    _ = (b (n + 2) / beta) * p (n + 2) (beta * omega)
          + (b (n + 1) / beta) * p n (beta * omega) := by ring

/-- Low-temperature Gamma(shape=2,scale=2) reference recurrence
has monic Laguerre norm ratio 4*n*(n+1). This lemma verifies
the conversion to the even Krylov coefficient. -/
theorem laguerre_even_coefficient_identity (n : ℕ) :
    4 * (4 * (n : ℝ) * ((n : ℝ) + 1)) =
      (4 * Real.sqrt ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 := by
  have hn : 0 ≤ (n : ℝ) * ((n : ℝ) + 1) := by positivity
  rw [mul_pow, Real.sq_sqrt hn]
  ring

end Scalar2024
