import Mathlib

/-!
# Literal exponent mismatch in JHEP02(2026)259, Eq. (2.26) and first Eq. (3.1)

The printed Fermi function is n_F(omega)=1/(exp(beta*omega)+1).
The intermediate claimed factor exp(-beta*omega/2)*n_F(omega)
differs from the final factor exp(+beta*omega/2)/(1+exp(beta*omega))
unless beta*omega=0. The final expression agrees with Eq. (2.25).

This file verifies the disagreement without floating-point arithmetic.
-/

namespace SchrodingerKrylovAudit

/-- Final Eq. (3.1) equals exp(z) times the printed intermediate term. -/
theorem fermi_missing_factor (z : ℝ) :
    Real.exp (z / 2) / (1 + Real.exp z) =
      Real.exp z * (Real.exp (-z / 2) / (1 + Real.exp z)) := by
  calc
    Real.exp (z / 2) / (1 + Real.exp z) =
      Real.exp (z + (-z / 2)) / (1 + Real.exp z) := by
        congr 1
        ring
    _ = (Real.exp z * Real.exp (-z / 2)) / (1 + Real.exp z) := by
        rw [Real.exp_add]
    _ = Real.exp z * (Real.exp (-z / 2) / (1 + Real.exp z)) := by ring

/-- For any beta*omega > 0 the printed intermediate Fermi factor
is strictly smaller than the last line of Eq. (3.1). -/
theorem fermi_intermediate_strict_mismatch (z : ℝ) (hz : 0 < z) :
    Real.exp (-z / 2) / (1 + Real.exp z) <
      Real.exp (z / 2) / (1 + Real.exp z) := by
  have hex : Real.exp (-z / 2) < Real.exp (z / 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hd : 0 < 1 + Real.exp z := by positivity
  exact (div_lt_div_iff₀ hd hd).mpr
    (by nlinarith [mul_lt_mul_of_pos_right hex hd])

/-- For any beta*omega < 0 the inequality reverses. -/
theorem fermi_intermediate_reverse_mismatch (z : ℝ) (hz : z < 0) :
    Real.exp (z / 2) / (1 + Real.exp z) <
      Real.exp (-z / 2) / (1 + Real.exp z) := by
  have hex : Real.exp (z / 2) < Real.exp (-z / 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hd : 0 < 1 + Real.exp z := by positivity
  exact (div_lt_div_iff₀ hd hd).mpr
    (by nlinarith [mul_lt_mul_of_pos_right hex hd])

end SchrodingerKrylovAudit
