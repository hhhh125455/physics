import Mathlib

/-!
# Real-variable differentiation audit for the TTbar saddle partition

This is a genuine Lean check of derivatives of the square-root/exponential
model, in addition to the algebraic and formal-series checks in stages 13/14.
Its conclusion is about the assumed saddle model, not a finite-c exact trace.
-/

namespace TTbarDeformedCalculus

noncomputable def F (μ A β : ℝ) : ℝ :=
  (β - Real.sqrt (β^2 - 4*μ*A))/(2*μ)

noncomputable def Z (μ A β : ℝ) : ℝ :=
  Real.exp (F μ A β)

/-- The derivative of log Z, whenever the square-root argument is nonzero. -/
theorem logZ_hasDerivAt (μ A β : ℝ)
    (hdisc : β^2 - 4*μ*A ≠ 0) :
    HasDerivAt (F μ A)
      ((1 - (2*β)/(2*Real.sqrt (β^2-4*μ*A)))/(2*μ)) β := by
  have hp : HasDerivAt
      (fun x : ℝ => x^2 - 4*μ*A) (2*β) β := by
    simpa [two_mul] using
      (((hasDerivAt_id β).pow 2).sub_const (4*μ*A))
  have hr := hp.sqrt hdisc
  have hf := ((hasDerivAt_id β).sub hr).div_const (2*μ)
  change HasDerivAt
    (fun x : ℝ => (x - Real.sqrt (x^2 - 4*μ*A))/(2*μ))
    ((1 - (2*β)/(2*Real.sqrt (β^2-4*μ*A)))/(2*μ)) β
  simpa only [Pi.sub_apply, id_eq] using hf

/-- Derivative of the modeled partition function itself. -/
theorem partition_hasDerivAt (μ A β : ℝ)
    (hdisc : β^2 - 4*μ*A ≠ 0) :
    HasDerivAt (Z μ A)
      (Z μ A β * ((1 - (2*β)/(2*Real.sqrt (β^2-4*μ*A)))/(2*μ))) β := by
  change HasDerivAt (fun x : ℝ => Real.exp (F μ A x))
    (Real.exp (F μ A β) *
      ((1 - (2*β)/(2*Real.sqrt (β^2-4*μ*A)))/(2*μ))) β
  exact (logZ_hasDerivAt μ A β hdisc).exp

/-- Exact first TFD energy moment obtained from -Z'/Z, in Lean. -/
theorem first_moment_from_derivative (μ A β : ℝ)
    (hμ : μ ≠ 0) (hpos : 0 < β^2 - 4*μ*A) :
    -(deriv (Z μ A) β) / Z μ A β =
       ((β / Real.sqrt (β^2-4*μ*A)) - 1)/(2*μ) := by
  have hd : Real.sqrt (β^2-4*μ*A) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  have hz : Z μ A β ≠ 0 := by
    unfold Z
    exact (Real.exp_pos _).ne'
  rw [(partition_hasDerivAt μ A β (ne_of_gt hpos)).deriv]
  field_simp [hμ, hd, hz]
  ring

end TTbarDeformedCalculus
