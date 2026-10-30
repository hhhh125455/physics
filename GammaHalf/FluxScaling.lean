import Mathlib

/-!
# Local flux scaling in the odd-scalar linear-area branch

Write z=U+V and eta=(U-V)/z.  The formal leading branch with
r²~c z and scalar phi=a*arcsin(eta) has K=4*pi*a² and
H=E/X ~ const*z^(2K-3/2)*(1-eta²)^(2K).

A common translation of the singularity tip contributes a derivative
whose radial exponent is 2K-5/2. In the 2D characteristic wedge the
Jacobian contributes one extra z, yielding an absolute integrand with
radial exponent 2K-3/2. It is integrable iff K>1/4.

The last condition matches the condition that the charged source is
subleading to the linear area term in the formal asymptotics.

The exact 2D integration and the separation-of-variables ansatz
are analysed outside Lean. The statements below machine-check all
exponent relations and the angular rational simplification. These
results are CONDITIONAL, not an existence theorem.
-/

namespace GammaHalf

theorem flux_variation_integrability_threshold (K : ℝ) :
    -(1 : ℝ) < 2 * K - 3 / 2 ↔ 1 / 4 < K := by
  constructor <;> intro h <;> linarith

theorem same_threshold_as_subleading_charge (K : ℝ) :
    (1 / 2 : ℝ) < 2 * K ↔ 1 / 4 < K := by
  constructor <;> intro h <;> linarith

theorem radial_cutoff_power_positive (K : ℝ) (hK : 1 / 4 < K) :
    0 < 2 * K - 1 / 2 := by
  linarith

/-- In the K=1/2 angular example the directional derivative is
   proportional to (5 eta²-1) z^(-3/2). This identity checks the
   rational angular polynomial after U=z(1+eta)/2, V=z(1-eta)/2. -/
theorem half_mode_angular_identity (z eta : ℝ) (hz : z ≠ 0) :
    (z ^ 2 -
       5 * (z * (1 + eta) / 2) * (z * (1 - eta) / 2)) /
       z ^ 2 = (5 * eta ^ 2 - 1) / 4 := by
  field_simp
  ring

/-- In the angular range -1<=eta<=1, the derivative numerator is
    uniformly bounded. This produces a radial integrability envelope. -/
theorem half_mode_angular_bound
    (eta : ℝ) (hl : -1 ≤ eta) (hu : eta ≤ 1) :
    |5 * eta ^ 2 - 1| ≤ 4 := by
  have hsq0 : 0 ≤ eta ^ 2 := sq_nonneg eta
  have hsq1 : eta ^ 2 ≤ 1 := by nlinarith [sq_nonneg (eta-1), sq_nonneg (eta+1)]
  apply abs_le.mpr
  constructor <;> nlinarith

end GammaHalf
