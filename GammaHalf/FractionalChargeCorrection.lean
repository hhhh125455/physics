import Mathlib

/-!
# Explicit fractional-power charge correction for the K = 1/2 branch

For a local self-similar odd-scalar inner model with
K=4*pi*a²=1/2, its renormalized charge flux is (up to C>0)

    H0(U,V) = C * U*V/(U+V)^(5/2).

The leading charged area correction with zero data on U=0 and V=0 is
    Xcorr = (q²*C/2)*I(U,V),
where
    I(U,V) = (8/9)*(U^(3/2)+V^(3/2)-(U+V)^(3/2))
             + (4/3)*U*V/(U+V)^(1/2).

SymPy independently differentiated this formula and found
  I_UV = U*V/(U+V)^(5/2).
That derivative is not fully formalized here; Lean checks the exact
rational cancellation among its differentiated terms, the source
bound, and positivity of the diagonal prefactor.

I has homogeneous degree 3/2, so it is subleading to a linear
X=c(U+V) blow-up. This is still a formal *local* expansion and does
not prove the global gamma exponent or existence of a coupled solution.
-/

namespace GammaHalf

/-- Algebraic cancellation of the mixed derivatives after using
    d_U d_V (z^(3/2))=(3/4)z^(-1/2) and
    d_U d_V (UV/z^(1/2))=(2z²+3UV)/(4z^(5/2)).
    The calculus rules are verified separately. -/
theorem half_mode_fractional_kernel_algebra
    (u v z root : ℝ) (hz : z ≠ 0) (hr : root ≠ 0) :
    -((2 / 3 : ℝ) / root) +
      (2 * z ^ 2 + 3 * u * v) / (3 * z ^ 2 * root) =
      u * v / (z ^ 2 * root) := by
  field_simp
  ring

/-- Exact quadratic estimate for U,V>=0. -/
theorem charge_kernel_uv_bound (u v : ℝ) :
    4 * u * v ≤ (u + v) ^ 2 := by
  nlinarith [sq_nonneg (u - v)]

/-- Bound the charged kernel by 1/(4*sqrt(z)); this is the
    key pointwise domination for the integrable z^(-1/2) source. -/
theorem half_mode_kernel_pointwise_bound
    (u v z root C : ℝ)
    (hz : z = u + v) (hzpos : 0 < z)
    (hrroot : 0 < root) (hC : 0 ≤ C) :
    C * u * v / (z ^ 2 * root) ≤ C / (4 * root) := by
  have hquart : 0 ≤ z ^ 2 - 4 * u * v := by
    rw [hz]
    nlinarith [sq_nonneg (u - v)]
  have hco : 0 ≤ C * (z ^ 2 - 4 * u * v) :=
    mul_nonneg hC hquart
  have hden : (0 : ℝ) < z ^ 2 * root := by positivity
  have hrden : (0 : ℝ) < 4 * root := by positivity
  apply (div_le_iff₀ hden).mpr
  have hrewrite : C / (4 * root) * (z ^ 2 * root) =
      C * z ^ 2 / 4 := by
    field_simp
  rw [hrewrite]
  nlinarith [hco]

/-- The coefficient of the correction on the diagonal is positive:
    I(eps,eps) = 2*(8-5*sqrt(2))/9 * eps^(3/2). -/
theorem half_mode_diagonal_coefficient_positive :
    0 < (8 : ℝ) - 5 * Real.sqrt 2 := by
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
    norm_num
  have hn : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- Degree 3/2 vs degree one: the correction/leading ratio is
    proportional to sqrt(z) for z>0. -/
theorem fractional_correction_relative_scale
    (z coeff : ℝ) (hz : z ≠ 0) :
    (coeff * z * Real.sqrt z) / z = coeff * Real.sqrt z := by
  field_simp

end GammaHalf
