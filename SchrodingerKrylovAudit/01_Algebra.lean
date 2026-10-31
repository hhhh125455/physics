import Mathlib

/-!
# Equation-level audit of JHEP 02 (2026) 259

This file proves *only* the explicitly stated algebraic claims below.
It does not formalize the Wightman field theory, an integral representation,
the numerical figures, or late-time Krylov dynamics.
All proofs use the repository's existing Lean and Mathlib foundations.
-/

namespace SchrodingerKrylovAudit

-- Equation (3.1): algebraic form of the fermionic spectral factor
-- with u = exp(beta * omega / 2), u > 0.
theorem eq_3_1_fermionic_factor (u : ℝ) (hu : u > 0) :
    u / (1 + u ^ 2) = 1 / (u + u⁻¹) := by
  have hun : u ≠ 0 := ne_of_gt hu
  field_simp
  <;> ring

-- Equation (3.17): the square of the fitted b_n has a residual c2^2.
-- The expression without that term is an approximation, not an identity.
theorem eq_3_17_exact_square (beta c2 n : ℝ) (hb : beta ≠ 0) :
    (2 * n / beta + c2) ^ 2 =
      (4 / beta ^ 2) * (n ^ 2 + beta * c2 * n) + c2 ^ 2 := by
  field_simp
  <;> ring

-- Equations (3.9), (3.15), (3.18): exact matching of diagonal parameters.
theorem eq_3_18_diagonal_match (beta c1 c2 n : ℝ) (hb : beta ≠ 0) :
    (-4 / beta) * ((beta * c2 + 1) / 2 + n)
      + (c1 + 2 * (beta * c2 + 1) / beta) =
    -4 * n / beta + c1 := by
  field_simp
  <;> ring

-- Equation (3.13): the matching slopes are on the degenerate boundary.
theorem eq_3_13_degenerate (alpha : ℝ) :
    (-2 * alpha) ^ 2 = 4 * alpha ^ 2 := by ring

-- Equation (4.4): the engineered one-sided spectrum has gamma = -2 alpha.
theorem eq_4_4_degenerate (kappa : ℝ) :
    (-2 / kappa) ^ 2 = 4 * (1 / kappa) ^ 2 := by ring

-- Equations (3.13), (4.4), (4.5): exact algebraic value of the
-- degenerate SL(2,R) expression, conditional on (3.13) being applicable.
theorem eq_4_5_coefficient (kappa t : ℝ) :
    2 * ((1 : ℝ) / 2) * (1 / kappa) ^ 2 * t ^ 2 =
      t ^ 2 / kappa ^ 2 := by ring

-- Equations (4.12), (4.15): substitution a = beta / 2.
theorem eq_4_15_substitution (beta pi t : ℝ) (hb : beta ≠ 0) :
    pi * t / (2 * (beta / 2)) = pi * t / beta := by
  field_simp
  <;> ring

-- Equation (A.18): change of spectral variables, x = beta*(mu-omega)/2.
theorem eq_A_18_exponent (beta mu omega : ℝ) :
    beta * omega / 2 =
      beta * mu / 2 - beta * (mu - omega) / 2 := by ring

-- Equation (A.20): only for the large-n approximation b_n ~ (2n+1)/beta.
theorem eq_A_20_approx_combination (beta mu n : ℝ) (hb : beta ≠ 0) :
    (mu - (4 * n + 4) / beta) + 2 * ((2 * n + 1) / beta) =
      mu - 2 / beta := by
  field_simp
  <;> ring

-- Equations (A.24), (A.25): solve the heuristic edge matching equation.
theorem eq_A_25_edge_match (beta mu pi : ℝ)
    (hb : beta ≠ 0) (hp : pi ≠ 0) :
    (pi / beta) * (2 * ((beta * mu + pi) / (2 * pi)) - 1) = mu := by
  field_simp
  <;> ring

-- Equations (A.32), (A.36), (A.37): the epsilon factor must be
-- retained when x = epsilon*n. b(x) = pi*x/(beta*epsilon).
theorem eq_A_36_correct_rescaling (epsilon beta pi x : ℝ)
    (he : epsilon ≠ 0) (hb : beta ≠ 0) :
    2 * epsilon * (pi * x / (beta * epsilon)) =
      2 * pi * x / beta := by
  field_simp
  <;> ring

-- Explicit counterexample to using b(x)=pi*x/beta and epsilon != 1.
theorem eq_A_37_missing_epsilon_counterexample :
    (2 : ℚ) * (1 / 2) * (3 * 5 / 7) ≠
      2 * (3 * 5 / 7) := by norm_num

-- Appendix B: exact right-hand side of printed equation (B.2).
private def a1Printed (m1 m2 m3 : ℚ) : ℚ :=
    -(m1 ^ 3 - 2 * m1 * m2 + m3) / (m1 ^ 2 - m2)

-- Equation (B.7): reflection gives a1 -> -a1.
theorem eq_B_2_reflection (m1 m2 m3 : ℚ) :
    a1Printed (-m1) m2 (-m3) = -a1Printed m1 m2 m3 := by
  unfold a1Printed
  ring

-- Appendix B: exact right-hand side of the printed equation (B.6).
-- The right-hand side computes b2^2, not b2.
def b2Printed (m1 m2 m3 m4 : ℚ) : ℚ :=
    -(m3 ^ 2 + m2 ^ 3 + m1 ^ 2 * m4 -
       m2 * (2 * m1 * m3 + m4)) / (m1 ^ 2 - m2) ^ 2

-- Equation (4.2) at kappa=1 gives moments (-1)^n n!.
-- For these moments (B.6) evaluates to 4, whereas (4.3) gives b2 = 2.
theorem eq_B_6_exp_spectrum_rhs :
    b2Printed (-1) 2 (-6) 24 = 4 := by norm_num [b2Printed]

theorem eq_B_6_conflicts_with_4_3 :
    b2Printed (-1) 2 (-6) 24 ≠ 2 := by norm_num [b2Printed]

-- A second independent counterexample uses unit-variance Gaussian moments.
theorem eq_B_6_gaussian_rhs :
    b2Printed 0 1 0 3 = 2 := by norm_num [b2Printed]

-- Reflection invariance of the *squared* coefficient survives the typo.
theorem eq_B_6_reflection (m1 m2 m3 m4 : ℚ) :
    b2Printed (-m1) m2 (-m3) m4 = b2Printed m1 m2 m3 m4 := by
  unfold b2Printed
  ring


-- Equations (4.11) and (4.17): set a=b and n=2, and write
-- D = zeta(3,1/4)-zeta(3,3/4).
-- The printed (4.17) yields D/(4*a^2), while (4.11) gives
-- D/(8*pi*a^2): their ratio is exactly 2*pi.
theorem eq_4_17_inconsistent_with_4_11 (a D : ℝ) (ha : a ≠ 0) :
    D / (4 * a ^ 2) = (2 * Real.pi) * (D / (8 * Real.pi * a ^ 2)) := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  <;> ring

-- Equation (B.6) calculates the square of the Laguerre b2 coefficient.
theorem eq_B_6_matches_square_not_coefficient :
    b2Printed (-1) 2 (-6) 24 = (2 : ℚ) ^ 2 := by
  norm_num [b2Printed]

-- The printed (B.5) is likewise a variance and equals b1^2.
theorem eq_B_5_is_square_for_variance_four :
    (-(0 : ℚ) ^ 2 + 4) = (2 : ℚ) ^ 2 := by norm_num

-- Equations (B.3)-(B.4): independent check using the exact
-- exponential-spectrum moments, for which a2=-5 (kappa=1).
private def a2Printed (m1 m2 m3 m4 m5 : ℚ) : ℚ :=
  (m3 ^ 3 - 2 * m2 * m3 * m4
     - m1 * m2 * (m2 ^ 3 + 2 * m3 ^ 2 - 2 * m2 * m4)
     - m1 ^ 3 * (m3 ^ 2 + 2 * m2 * m4)
     + m1 ^ 4 * m5 + m2 ^ 2 * m5
     + m1 ^ 2 * (3 * m2 ^ 2 * m3 + 2 * m3 * m4 - 2 * m2 * m5))
    / ((m1 ^ 2 - m2) *
       (m2 ^ 3 + m3 ^ 2 + m1 ^ 2 * m4 -
          m2 * (2 * m1 * m3 + m4)))

theorem eq_B_3_exp_spectrum_example :
    a2Printed (-1) 2 (-6) 24 (-120) = -5 := by
  norm_num [a2Printed]


end SchrodingerKrylovAudit
