import Mathlib

/-!
# Full Einstein-constraint obstruction to a reduced-area counterfamily

For the toy geometry solving EXACTLY the charged area equation at q^2=1:
   X = delta^n + U + V + U*V,
   E = exp(-2*sigma) = 2*X/(1-X),
at the reflection-invariant center U=V one has X_U=X_V=P=1+U,
X_UV=1, X_UU=X_VV=0.

The U-null Einstein constraint determines
   4*pi*phi_U^2 = P^2*(3-X)/(4*X^2*(1-X)).
An odd reflection-symmetric scalar requires phi_V=-phi_U, so
   4*pi*phi_U*phi_V = -4*pi*phi_U^2.

Substituting these facts into the sigma Einstein equation
 sigma_UV - r_UV/r - 4*pi*phi_U*phi_V - E/(4*X^2) = 0
gives the algebraic residual recorded below, which is
strictly positive at the regular interior point U=V=1/100, delta=0.

Thus the exact charged-AREA equation family is not an example of a
solution of the FULL Einstein-Maxwell-odd-scalar system.

Lean proves the rational identity and positivity of its numerical
value. The geometric derivative substitutions are derived separately
using calculus/SymPy; they are not yet formalized in Lean.
-/

namespace GammaHalf

noncomputable def oddConstraintResidual (X P : ℝ) : ℝ :=
  -(1 / (2 * X * (1 - X)) -
        P ^ 2 * (1 - 2 * X) / (2 * X ^ 2 * (1 - X) ^ 2)) -
  (1 / (2 * X) - P ^ 2 / (4 * X ^ 2)) +
  P ^ 2 * (3 - X) / (4 * X ^ 2 * (1 - X)) -
  1 / (2 * X * (1 - X))

theorem odd_constraint_residual_factor
    (X P : ℝ) (hX : X ≠ 0) (hden : 1 - X ≠ 0) :
    oddConstraintResidual X P =
      (P ^ 2 * (X ^ 2 - 5 * X + 3) -
         X * (1 - X) * (3 - X)) /
      (2 * X ^ 2 * (1 - X) ^ 2) := by
  unfold oddConstraintResidual
  field_simp
  <;> ring

/-- At delta=0 and U=V=1/100 we have X=201/10000, P=101/100.
    The full Einstein sigma residual must vanish but is positive. -/
theorem odd_area_family_not_full_einstein :
    0 < oddConstraintResidual (201 / 10000 : ℝ) (101 / 100 : ℝ) := by
  unfold oddConstraintResidual
  norm_num

end GammaHalf
