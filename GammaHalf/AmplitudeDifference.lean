import Mathlib

/-!
# The exact two-amplitude difference equation for the charged area source

For any two regular positive-area solutions with X_i=r_i^2 and
E_i=exp(-2*sigma_i), the area equation is
  (X_i)_uv = E_i/2 * (q^2/X_i-1).

This file checks the *exact* finite-difference identity:
  Y_uv + q^2*E2/(2*X1*X2)*Y
    = (E2-E1)/2*(q^2/X1-1),
  where Y=X2-X1.

The coefficient of Y is positive when charge, E2, X1 and X2 are
positive. The source has no definite sign because E changes with
the initial amplitude. Consequently null focusing positivity by itself
does not prove transversality with respect to the amplitude.
-/ 

namespace GammaHalf

noncomputable def chargedAreaSource (X E q : ℝ) : ℝ :=
  E / 2 * (q ^ 2 / X - 1)

/-- Exact nonlinear source difference; no linearization or smallness. -/
theorem charged_area_source_difference
    (X1 X2 E1 E2 q : ℝ)
    (hX1 : X1 ≠ 0) (hX2 : X2 ≠ 0) :
    chargedAreaSource X2 E2 q - chargedAreaSource X1 E1 q =
      (E2 - E1) / 2 * (q ^ 2 / X1 - 1) -
        q ^ 2 * E2 / (2 * X1 * X2) * (X2 - X1) := by
  unfold chargedAreaSource
  field_simp
  <;> ring

/-- Rearranged as a wave equation for the finite amplitude difference Y. -/
theorem finite_parameter_difference
    (X1 X2 E1 E2 q Yuv : ℝ)
    (hX1 : X1 ≠ 0) (hX2 : X2 ≠ 0)
    (hfield : Yuv = chargedAreaSource X2 E2 q -
       chargedAreaSource X1 E1 q) :
    Yuv + q ^ 2 * E2 / (2 * X1 * X2) * (X2 - X1) =
      (E2 - E1) / 2 * (q ^ 2 / X1 - 1) := by
  rw [hfield, charged_area_source_difference X1 X2 E1 E2 q hX1 hX2]
  ring

/-- The coefficient is strictly positive in the charged positive-area region. -/
theorem difference_potential_positive
    (X1 X2 E2 q : ℝ)
    (hX1 : 0 < X1) (hX2 : 0 < X2)
    (hE2 : 0 < E2) (hq : q ≠ 0) :
    0 < q ^ 2 * E2 / (2 * X1 * X2) := by
  have hq2 : 0 < q ^ 2 := sq_pos_of_ne_zero hq
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hden : 0 < 2 * X1 * X2 :=
    mul_pos (mul_pos htwo hX1) hX2
  exact div_pos (mul_pos hq2 hE2) hden

end GammaHalf
