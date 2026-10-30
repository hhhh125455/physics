import Mathlib

/-!
# Second amplitude variation of the exact charged area equation

Set X=r², E=e^(-2sigma), q2=q².
The exact polynomial Einstein area equation is

  P(X,Xuv,E):= 2*X*Xuv-E*(q2-X)=0.

For amplitude A, denote
  Y=X_A, V=X_AA, Z=sigma_A, T=sigma_AA.
Then E_A=-2EZ and E_AA=E*(4Z²-2T).

The Taylor jets below are complete to fourth order in eps;
hence their eps² coefficient is the EXACT second amplitude
variation at regular X>0 points, conditional on C²(A) regularity.

Importantly, the second-variation source includes both positive
quadratic terms and terms with T, so no sign propagation is claimed.

At the time-symmetric initial center with fixed X0 and E0,
  X_xx(0;A)=E0*(1-q²/X0)-k*X0*A²*B²
where k=4*pi and B=1/C. Consequently
  d_AA X_xx(0;A)=-2*k*X0*B²<0.
Time-symmetric area evolution gives the same second response
for X_tt at the initial center.

Lean proves the algebra and its sign, not an actual global
C²-dependence of the singular spacetime solutions on A.
-/

namespace GammaHalf

private def chargedAreaPolynomial (X Xuv E q2 : ℝ) : ℝ :=
  2 * X * Xuv - E * (q2 - X)

private def firstAreaJet
    (X Xuv E q2 Y Yuv Z : ℝ) : ℝ :=
  2 * Y * Xuv + 2 * X * Yuv + E * Y + 2 * E * Z * (q2-X)

private def halfSecondAreaJet
    (X Xuv E q2 Y Yuv V Vuv Z T : ℝ) : ℝ :=
  X * Vuv + V * Xuv + 2 * Y * Yuv +
  E * (V / 2 - 2 * Z * Y - (2 * Z^2 - T) * (q2-X))

theorem exact_second_variation_taylor
    (X Xuv E q2 Y Yuv V Vuv Z T eps : ℝ) :
    chargedAreaPolynomial
       (X + eps * Y + eps^2 * V/2)
       (Xuv + eps * Yuv + eps^2 * Vuv/2)
       (E * (1-2*eps*Z+eps^2*(2*Z^2-T))) q2 =
      chargedAreaPolynomial X Xuv E q2
      + eps * firstAreaJet X Xuv E q2 Y Yuv Z
      + eps^2 * halfSecondAreaJet X Xuv E q2
          Y Yuv V Vuv Z T
      + eps^3 * (Y * Vuv + V * Yuv -
          E*(Z*V-(2*Z^2-T)*Y))
      + eps^4 * (V*Vuv/2 + E*(2*Z^2-T)*V/2) := by
  unfold chargedAreaPolynomial firstAreaJet halfSecondAreaJet
  ring

/-- The coefficient of eps² is the second variation after
    setting the polynomial's first two jets to zero. -/
theorem second_variation_area_coefficient
    (X Xuv E q2 Y Yuv V Vuv Z T : ℝ)
    (hsecond : halfSecondAreaJet X Xuv E q2
      Y Yuv V Vuv Z T = 0) :
    X * Vuv + V * Xuv + 2 * Y * Yuv +
      E * (V/2 - 2*Z*Y - (2*Z^2-T)*(q2-X)) = 0 := by
  exact hsecond

noncomputable def centerSecondKick (X0 k B : ℝ) : ℝ :=
  -(2*k*X0*B^2)

theorem center_second_kick_strict_negative
    (X0 k B : ℝ) (hX : 0 < X0) (hk : 0 < k) (hB : B ≠ 0) :
    centerSecondKick X0 k B < 0 := by
  unfold centerSecondKick
  have hB2 : 0 < B ^ 2 := sq_pos_of_ne_zero hB
  have hp : 0 < 2*k*X0*B^2 := by positivity
  linarith

/-- The initial area-curvature formula is exactly quadratic
    in A, and the symmetric finite difference is its second
    derivative coefficient for any step. -/
theorem center_amplitude_quadratic_second_difference
    (X0 E q2 k B A h : ℝ) (hX : X0 ≠ 0) :
    (E*(1-q2/X0)-k*X0*(A+h)^2*B^2)
      - 2*(E*(1-q2/X0)-k*X0*A^2*B^2)
      + (E*(1-q2/X0)-k*X0*(A-h)^2*B^2) =
        centerSecondKick X0 k B * h^2 := by
  unfold centerSecondKick
  ring

end GammaHalf
