import Mathlib

/-!
# Initial constraint under w = X^(3/4), X=r^4, w=r^3

This change of dependent variable cancels the derivative-square term
-X_x^2/(4X) in the exact initial Hamiltonian constraint:

  w_xx + sigma_x w_x
    + 3k/4 A^2 f_x^2 w
    - 3E/4 w^(-1/3) + 3Eq^2/4 w^(-5/3) = 0.

Here k=4*pi and E=e^(-2sigma) is independent of A on
the prescribed RN initial slice.

Its amplitude Jacobi equation h=partial_A w is

  h_xx + sigma_x h_x + Qw h
     = -(3k/2) A f_x^2 w,

  Qw=3k/4 A^2 f_x^2 + E*(X-5q^2)/(4X^2).

The new equation is self-adjoint with integrating factor e^sigma,
independent of the unknown nonlinear X. Its potential is nonnegative
where X>=5q^2 (which must be separately certified for the RN IVP).

Lean checks the exact algebra of this transformation, the potential
factorization and nonnegativity; the actual chain rule X=r^4,
w=r^3 is not formalized here, so its derivatives are inserted
explicitly from the ordinary chain rule.
-/

namespace GammaHalf

theorem cubic_root_constraint_algebra
    (r wp wpp sigx E q2 k A p2 : ℝ) (hr : r ≠ 0) :
    4 * r^4 * (4*r*wpp/3 + 4*wp^2/(9*r^2)) +
       4*r^4*sigx*(4*r*wp/3) - (4*r*wp/3)^2 +
       4*k*r^8*A^2*p2 - 4*E*(r^4-q2) =
    (16*r^5/3) *
      (wpp + sigx*wp + (3*k/4)*A^2*r^3*p2 -
       3*E/(4*r) + 3*E*q2/(4*r^5)) := by
  field_simp
  <;> ring

noncomputable def cubicPotential (X E q2 k A p2 : ℝ) : ℝ :=
  (3*k/4)*A^2*p2 + E/(4*X) - 5*E*q2/(4*X^2)

theorem cubic_jacobi_potential_factorization
    (X E q2 k A p2 : ℝ) (hX : X ≠ 0) :
    cubicPotential X E q2 k A p2 =
      (3*k/4)*A^2*p2 + E*(X-5*q2)/(4*X^2) := by
  unfold cubicPotential
  field_simp
  <;> ring

theorem cubic_jacobi_potential_nonneg
    (X E q2 k A p2 : ℝ)
    (hX : 0 < X) (hE : 0 ≤ E) (hk : 0 ≤ k)
    (hp2 : 0 ≤ p2) (hcharge : 5*q2 ≤ X) :
    0 ≤ cubicPotential X E q2 k A p2 := by
  rw [cubic_jacobi_potential_factorization X E q2 k A p2
      (ne_of_gt hX)]
  have hfirst : 0 ≤ (3*k/4)*A^2*p2 := by positivity
  have hsecond : 0 ≤ E*(X-5*q2)/(4*X^2) := by
    apply div_nonneg
    · exact mul_nonneg hE (sub_nonneg.mpr hcharge)
    · positivity
  exact add_nonneg hfirst hsecond

/-- Change of response variable: Y=partial_A X=(4/3)r*h
    for r>0. A negative h forces a negative area response Y. -/
theorem negative_root_response_gives_negative_area
    (r h Y : ℝ) (hr : 0 < r)
    (hrelation : Y = (4/3)*r*h) (hh : h < 0) :
    Y < 0 := by
  rw [hrelation]
  have hp : 0 < (4/3:ℝ)*r := mul_pos (by norm_num) hr
  nlinarith [mul_neg_of_pos_of_neg hp hh]

end GammaHalf
