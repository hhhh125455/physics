import Mathlib

/-!
TTbar/TFD Part 08: a closed nonlinear Toda differential--difference
recurrence for the Hankel determinants of the Lah moment sequence.

Let mu_k(u) = k! [t^k] exp(u*t/(1-t)), mu_0=1, and
Delta_n(u)=det(mu_{i+j}(u))_{0<=i,j<n}.

The derived recurrence is
 Delta_(n+1) Delta_(n-1)
 = (n(n-1)+2nu) Delta_n^2 + 2u Delta_n Delta'_n
   + u^2 (Delta_n Delta''_n - (Delta'_n)^2).

* All-index gauge transformation (Toda tau to Lah Delta) is proven
  as an algebraic identity below.
* The actual Lah determinant recurrence is symbolically checked at
  n=1,2,3,4 for explicit determinant polynomials.
* The all-index Wronskian/Toda determinant identity is a classical
  mathematical input and is NOT yet proved in Lean here.
-/

namespace TTbarLahToda

open Polynomial

/-- Delta_0 and Delta_1 are one. -/
noncomputable def D0 : Polynomial ℚ := 1
noncomputable def D1 : Polynomial ℚ := 1
noncomputable def D2 : Polynomial ℚ := 2*X
noncomputable def D3 : Polynomial ℚ :=
  4*X^2*(4*X+3)
noncomputable def D4 : Polynomial ℚ :=
  48*X^3*(16*X^3+48*X^2+45*X+12)
noncomputable def D5 : Polynomial ℚ :=
  4608*X^4*(64*X^6+480*X^5+1440*X^4+
    2175*X^3+1710*X^2+648*X+90)

/-- A standalone polynomial operator yielding the RHS of the Toda
    differential-difference equation. The variable is X=u. -/
noncomputable def TodaRHS (n : ℕ) (d : Polynomial ℚ) : Polynomial ℚ :=
  (C ((n : ℚ)*((n : ℚ)-1)) + C (2*(n : ℚ))*X)*d^2
   + 2*X*d*(derivative d)
   + X^2*(d*(derivative (derivative d)) - (derivative d)^2)

/-- Algebraic core of the change-of-variable beta -> u=A/beta.
   In the Wronskian tau equation, s=nu+n(n-1), t=nu. -/
theorem gauge_transform_identity (s t u d dp dpp : ℚ) :
    d*((s*(s+1)+t)*d+2*u*(s+1)*dp+u^2*dpp)
      -(s*d+u*dp)^2 =
    (s+t)*d^2+2*u*d*dp+u^2*(d*dpp-dp^2) := by
  ring

/-- The n=1 Toda step produces Delta_2=2u. -/
theorem toda_step_1 : D2*D0 = TodaRHS 1 D1 := by
  simp [D0,D1,D2,TodaRHS]
  exact (Polynomial.C_eq_natCast 2).symm

/-- n=2 produces Delta_3=4u^2(4u+3). -/
theorem toda_step_2 : D3*D1 = TodaRHS 2 D2 := by
  simp [D1,D2,D3,TodaRHS, derivative_mul,
    derivative_pow, derivative_X, derivative_C]
  polynomial

/-- n=3 reproduces the known Lah Hankel determinant Delta_4. -/
theorem toda_step_3 : D4*D2 = TodaRHS 3 D3 := by
  simp [D2,D3,D4,TodaRHS, derivative_mul,
    derivative_pow, derivative_X, derivative_C]
  polynomial

/-- n=4 produces Delta_5 with ten-degree polynomial in u. -/
theorem toda_step_4 : D5*D3 = TodaRHS 4 D4 := by
  simp [D3,D4,D5,TodaRHS, derivative_mul,
    derivative_pow, derivative_X, derivative_C]
  polynomial

/-- All-index algebraic reduction of the shifted-Hankel Jacobi
    coefficient to the logarithmic derivative of Delta_(n+1)/Delta_n.
    Assumes the shifted-Hankel determinant identity (shown below for
    small n and derived from Wronskian gauge analytically).
-/
theorem alpha_from_delta_algebra
    (n : ℕ) (u p q dp dq : ℚ)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    ((((n : ℚ)+1)*u+((n : ℚ)+1)*(n : ℚ))*p+u*dp)/p -
      (((n : ℚ)*u+(n : ℚ)*((n : ℚ)-1))*q+u*dq)/q =
    u+2*(n : ℚ)+u*(dp/p-dq/q) := by
  field_simp [hp,hq] <;> ring

/-- Shifted Lah determinant at size 1. -/
theorem shifted_identity_1 :
    X = X*D1 := by
  simp [D1]

/-- Shifted-Hankel identity at size 2:
    tildeDelta_2 = 2u(2u+3). -/
theorem shifted_identity_2 :
    2*X*(2*X+3) = (2*X+2)*D2+X*(derivative D2) := by
  simp [D2, derivative_mul, derivative_pow, derivative_X, derivative_C]
  polynomial

/-- Shifted-Hankel identity at size 3. -/
theorem shifted_identity_3 :
    12*X^2*(4*X^2+15*X+8) =
      (3*X+6)*D3+X*(derivative D3) := by
  simp [D3, derivative_mul, derivative_pow, derivative_X, derivative_C]
  polynomial

/-- Shifted-Hankel identity at size 4. -/
theorem shifted_identity_4 :
    192*X^3*(16*X^4+120*X^3+249*X^2+192*X+45) =
      (4*X+12)*D4+X*(derivative D4) := by
  simp [D4, derivative_mul, derivative_pow, derivative_X, derivative_C]
  polynomial


end TTbarLahToda
