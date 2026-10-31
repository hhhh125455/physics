import Mathlib

/-!
# PIII sigma: arbitrary-index denominator-clearing identity

For any alpha, n, s and formal derivatives D,D',D'',D''', set
  U = D' D + s (D'' D - D'^2),
  V = 2(D''D - D'^2) D + s(D'''D^2 - 3D'D''D + 2D'^3).
Then H=s D'/D, H'=U/D^2, H''=V/D^3.

The Painleve sigma identity, after multiplying by D^6, becomes a
polynomial equation in the displayed quantities. Both its rational
and polynomial forms are checked below at arbitrary n and alpha.

Combining this with the classical complex identity theorem extends a
published alpha>-1 result to any alpha for positive s, assuming the
moment determinant and its first three s-derivatives are entire in
alpha. The entire-function hypothesis and identity theorem application
are not formalized here; only the all-parameter algebraic step is.
-/

namespace PIIISigmaAnalyticContinuation

def U (D A B s : ℚ) : ℚ := A*D+s*(B*D-A^2)

def V (D A B C s : ℚ) : ℚ :=
  2*(B*D-A^2)*D+s*(C*D^2-3*A*B*D+2*A^3)

def sigmaResidual (D A U V s n alpha : ℚ) : ℚ :=
  (s*(V/D^3))^2 - (n-(2*n+alpha)*(U/D^2))^2 +
  4*(U/D^2)*(U/D^2-1)*
    (s*(U/D^2)-s*(A/D)+n*(n+alpha))

def polynomialResidual (D A U V s n alpha : ℚ) : ℚ :=
  (s*V)^2 -D^2*(n*D^2-(2*n+alpha)*U)^2+
  4*U*(U-D^2)*(s*U-s*A*D+n*(n+alpha)*D^2)

/-- For arbitrary n and alpha, multiplying sigma by D^6 gives the polynomial. -/
theorem clear_denominators (D A U V s n alpha : ℚ) (hD : D ≠ 0) :
    D^6*sigmaResidual D A U V s n alpha =
      polynomialResidual D A U V s n alpha := by
  unfold sigmaResidual polynomialResidual
  field_simp [hD] <;> ring

/-- Algebraic equivalence of PIII sigma and its entire-polynomial version. -/
theorem polynomial_iff_sigma (D A U V s n alpha : ℚ) (hD : D ≠ 0) :
    sigmaResidual D A U V s n alpha = 0 ↔
      polynomialResidual D A U V s n alpha = 0 := by
  have h := clear_denominators D A U V s n alpha hD
  constructor
  · intro hr
    rw [hr, mul_zero] at h
    exact h.symm
  · intro hp
    rw [hp] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 6 hD)

end PIIISigmaAnalyticContinuation
