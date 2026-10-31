import Mathlib

/-!
# Double commutator reduction for the original fermionic Jacobi operator.

Let J be the Jacobi multiplication operator in x=mu-omega,
and N=diag(0,1,2,...). These theorems isolate the exact entries of
Q=[J,[J,N]]+(2/c)J after inserting the integration-by-parts sum rules.

IMPORTANT: these theorems do not silently assume Q is compact.
To conclude the exact long-time coefficient we still need:
  (a) the two displayed residual entry sequences converge to zero,
  (b) the infinite-operator commutators have the stated domain properties.
The original spectral measure is purely absolutely continuous.
-/

namespace SchrodingerKrylovAudit

/-- The diagonal coefficient of [J,[J,N]] for a Jacobi matrix. -/
def doubleCommutatorDiag (bn bnext : ℝ) : ℝ :=
  2 * (bn ^ 2 - bnext ^ 2)

/-- The upper adjacent coefficient of [J,[J,N]]. -/
def doubleCommutatorOff (dn dnext bnext : ℝ) : ℝ :=
  bnext * (dn - dnext)

/-- Corrected diagonal commutator entry given the exact Freud sum rule. -/
theorem original_double_commutator_diag
    (c bn bnext dn Rn Rnext : ℝ)
    (hc : c ≠ 0)
    (hFreud : c * (bnext ^ 2 - bn ^ 2) =
      dn + 2 * c * (Rnext - Rn)) :
    doubleCommutatorDiag bn bnext + (2 / c) * dn =
      -4 * (Rnext - Rn) := by
  unfold doubleCommutatorDiag
  apply (mul_left_cancel₀ hc)
  linear_combination (-2) * hFreud

/-- Corrected adjacent commutator entry given the exact diagonal sum rule. -/
theorem original_double_commutator_off
    (c dn dnext bnext en enext : ℝ)
    (hc : c ≠ 0)
    (hFreud : dnext = dn + 2 / c + 2 * (enext - en)) :
    doubleCommutatorOff dn dnext bnext + (2 / c) * bnext =
      -2 * bnext * (enext - en) := by
  unfold doubleCommutatorOff
  rw [hFreud]
  ring

/-- Exact difference relation between consecutive b_n² under the sum rule. -/
theorem original_freud_succ_difference
    (c beta Sprev dn bn bnext Rn Rnext : ℝ)
    (h1 : c * bn ^ 2 = Sprev + beta * Rn)
    (h2 : c * bnext ^ 2 = Sprev + dn + beta * Rnext)
    (hc : c ≠ 0) :
    bnext ^ 2 - bn ^ 2 = dn / c + (beta / c) * (Rnext - Rn) := by
  have h : c * (bnext ^ 2 - bn ^ 2) =
      dn + beta * (Rnext - Rn) := by
    linear_combination h2 - h1
  apply (mul_left_cancel₀ hc)
  calc
    c * (bnext ^ 2 - bn ^ 2) = dn + beta * (Rnext - Rn) := h
    _ = c * (dn / c + (beta / c) * (Rnext - Rn)) := by
      field_simp
      ring

/-- If the two concrete original-spectrum Freud residual sequences vanish,
then the diagonal entries of the double-commutator defect vanish. -/
theorem original_double_commutator_diag_tendsto
    (R : ℕ → ℝ)
    (hR : Filter.Tendsto (fun n : ℕ => R (n + 1) - R n)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => -4 * (R (n + 1) - R n))
      Filter.atTop (nhds 0) := by
  simpa using hR.const_mul (-4)

/-- Likewise for adjacent entries. This is a precise missing lemma,
not an unverified conclusion about the original field theory. -/
theorem original_double_commutator_off_tendsto
    (e b : ℕ → ℝ)
    (he : Filter.Tendsto
      (fun n : ℕ => b (n + 1) * (e (n + 1) - e n))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ => -2 * b (n + 1) * (e (n + 1) - e n))
      Filter.atTop (nhds 0) := by
  simpa only [mul_assoc] using he.const_mul (-2)

end SchrodingerKrylovAudit
