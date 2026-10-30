import Mathlib

/-!
# Initial Hamiltonian constraint: exact amplitude response ODE

On the time-symmetric initial slice let X=r², sigma be fixed
independently of amplitude A, and phi=A*f(x), p2=(f'(x))².
The Einstein Hamiltonian constraint, multiplied by 4X, is

  4 X Xxx + 4 X sigma_x Xx - Xx²
     + 4k X² A² p2 - 4E(X-q²)=0, k=4*pi.

Let Y=d_A X, with Y(0)=Y_x(0)=0 due to the fixed center
radius, then the EXACT differentiated initial ODE is

 Yxx + (sigma_x-Xx/(2X))*Yx
    +(Xx²/(4X²)+k*A²*p2-E*q²/X²)*Y
      = -2k*A*X*p2.

The coefficient of Y is NOT sign-definite. Hence a maximum
principle / strictly negative global response does not follow
only from positive scalar energy.

Lean verifies all algebraic coefficients and elimination; it
does not claim sign propagation of the ODE or the later PDE.
-/

namespace GammaHalf

private def initialP (X Xx Xxx sigx E q2 k A p2 : ℝ) : ℝ :=
  4*X*Xxx + 4*X*sigx*Xx - Xx^2
    + 4*k*X^2*A^2*p2 - 4*E*(X-q2)

private def initialL
    (X Xx Xxx sigx E q2 k A p2 Y Yx Yxx : ℝ) : ℝ :=
  4*Y*Xxx + 4*X*Yxx +
    4*Y*sigx*Xx + 4*X*sigx*Yx - 2*Xx*Yx +
    8*k*X*Y*A^2*p2 + 8*k*X^2*A*p2 - 4*E*Y

theorem initial_full_taylor_first_jet
    (X Xx Xxx sigx E q2 k A p2 Y Yx Yxx eps : ℝ) :
    initialP (X+eps*Y) (Xx+eps*Yx) (Xxx+eps*Yxx)
       sigx E q2 k (A+eps) p2 =
    initialP X Xx Xxx sigx E q2 k A p2 +
    eps * initialL X Xx Xxx sigx E q2 k A p2 Y Yx Yxx +
    eps^2 * (4*Y*Yxx+4*sigx*Y*Yx-Yx^2+
       4*k*p2*(X^2+4*A*X*Y+A^2*Y^2)) +
    eps^3 * (4*k*p2*(2*X*Y+2*A*Y^2)) +
    eps^4 * (4*k*p2*Y^2) := by
  unfold initialP initialL
  ring

/-- This is the canonical forced linear ODE, derived using BOTH
    the original Hamiltonian constraint and its A-variation. -/
theorem initial_response_ode
    (X Xx Xxx sigx E q2 k A p2 Y Yx Yxx : ℝ)
    (hX : X ≠ 0)
    (hinit : initialP X Xx Xxx sigx E q2 k A p2 = 0)
    (hvar : initialL X Xx Xxx sigx E q2 k A p2 Y Yx Yxx = 0) :
    Yxx + (sigx - Xx/(2*X))*Yx +
      (Xx^2/(4*X^2)+k*A^2*p2-E*q2/X^2)*Y =
        -2*k*A*X*p2 := by
  unfold initialP at hinit
  unfold initialL at hvar
  have hYX : Y*(4*X*Xxx +4*X*sigx*Xx-Xx^2+
       4*k*X^2*A^2*p2-4*E*(X-q2))=0 := by
    simpa using congrArg (fun t : ℝ => Y*t) hinit
  have hXV : X*(4*Y*Xxx+4*X*Yxx+
       4*Y*sigx*Xx+4*X*sigx*Yx-2*Xx*Yx+
       8*k*X*Y*A^2*p2+8*k*X^2*A*p2-4*E*Y)=0 := by
    simpa using congrArg (fun t : ℝ => X*t) hvar
  field_simp [hX]
  nlinarith [hYX,hXV]

/-- The force is strictly negative for a nonzero local scalar slope,
    provided A,k,X>0. -/
theorem initial_response_force_negative
    (k A X p : ℝ)
    (hk : 0 < k) (hA : 0 < A) (hX : 0 < X)
    (hp : p ≠ 0) :
    -2*k*A*X*p^2 < 0 := by
  have hpsq : 0 < p^2 := sq_pos_of_ne_zero hp
  have hprod : 0 < 2*k*A*X*p^2 := by positivity
  linarith

end GammaHalf
