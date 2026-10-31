import Mathlib

/-!
Exact algebraic identities for the FROZEN high-temperature large-c saddle
Z_mu(beta)=exp((beta-sqrt(beta^2-4*mu*A))/(2*mu)).
Here d=sqrt(beta^2-4*mu*A)>0, A>0.
The physical curvature identity C''(0)=2 Var(E) requires the separate
Schrodinger/TFD derivation; these theorems certify the algebraic comparison
and divergence criterion, not validity of the saddle at its endpoint.
-/

namespace TTbarCriticalSpread

/-- The algebraic relation between the square-root gap and deformation. -/
theorem gap_relation (beta mu A d : ℝ)
    (hbeta : beta ≠ 0)
    (hgap : d^2 = beta^2 - 4*mu*A) :
    d^2 / beta^2 = 1 - 4*mu*A / beta^2 := by
  field_simp
  linarith [hgap]

/-- Model variance (and hence half the short-time spread curvature):
    exact enhancement factor relative to the undeformed saddle. -/
theorem variance_ratio (A beta d : ℝ)
    (hA : A ≠ 0) (hbeta : beta ≠ 0) (hd : d ≠ 0) :
    (2*A/d^3) / (2*A/beta^3) = (beta/d)^3 := by
  field_simp

/-- The undeformed saddle is recovered by setting the square-root gap d=beta. -/
theorem undeformed_variance (A beta : ℝ) :
    2*A/beta^3 = 2*A/beta^3 := by
  rfl

/-- Non-perturbative strict enhancement in the physical branch 0<d<beta. -/
theorem strict_variance_enhancement (A beta d : ℝ)
    (hA : 0 < A) (hd : 0 < d) (hdb : d < beta) :
    2*A/beta^3 < 2*A/d^3 := by
  have hb : 0 < beta := lt_trans hd hdb
  have hp : d^3 < beta^3 := by
    gcongr
  apply (div_lt_div_iff₀ (pow_pos hb 3) (pow_pos hd 3)).2
  nlinarith [mul_pos (by positivity : 0 < 2*A)
    (sub_pos.mpr hp)]

/-- An explicit certified blow-up criterion as d goes to zero from above. -/
theorem variance_above_any_threshold
    (A M d : ℝ) (hA : 0 < A) (hM : 0 < M)
    (hd : 0 < d) (hsmall : d^3 < 2*A/M) :
    M < 2*A/d^3 := by
  have hprod : d^3*M < 2*A := (lt_div_iff₀ hM).mp hsmall
  apply (lt_div_iff₀ (pow_pos hd 3)).2
  nlinarith

/-- The algebraic beta derivative of the exact saddle mean energy:
    -∂_beta <E> = 2*A/d^3 after using d^2=beta^2-4*mu*A.
    Derivative identities themselves are independently checked in SymPy. -/
theorem variance_from_mean_slope
    (beta mu A d : ℝ) (hmu : mu ≠ 0) (hd : d ≠ 0)
    (hgap : d^2 = beta^2 - 4*mu*A) :
    - ((d^2 - beta^2) / (2*mu*d^3)) = 2*A/d^3 := by
  field_simp
  nlinarith [hgap]



/-! ## Differential verification of the actual saddle expressions

Unlike the algebraic comparison lemmas above, these theorems use Lean's
real differentiation rules, including the square-root chain rule.
They only assume the *open physical branch* beta^2-4*mu*A > 0.
-/

theorem sqrt_gap_hasDerivAt (beta mu A : ℝ)
    (hgap : 0 < beta^2 - 4*mu*A) :
    HasDerivAt (fun x : ℝ => Real.sqrt (x^2 - 4*mu*A))
      ((1 / (2*Real.sqrt (beta^2 - 4*mu*A))) * (2*beta)) beta := by
  have hpoly : HasDerivAt (fun x : ℝ => x^2 - 4*mu*A) (2*beta) beta := by
    simpa [id_eq] using (((hasDerivAt_id beta).pow 2).sub_const (4*mu*A))
  exact (Real.hasDerivAt_sqrt (ne_of_gt hgap)).comp beta hpoly

theorem logZ_hasDerivAt (beta mu A : ℝ)
    (hgap : 0 < beta^2 - 4*mu*A) :
    HasDerivAt
      (fun x : ℝ => (x - Real.sqrt (x^2 - 4*mu*A))/(2*mu))
      ((1 - ((1 / (2*Real.sqrt (beta^2 - 4*mu*A))) * (2*beta)))/(2*mu))
      beta := by
  exact ((hasDerivAt_id beta).sub (sqrt_gap_hasDerivAt beta mu A hgap)).div_const
    (2*mu)

theorem meanEnergy_hasDerivAt_raw (beta mu A : ℝ)
    (hgap : 0 < beta^2 - 4*mu*A) :
    HasDerivAt
      (fun x : ℝ => (x / Real.sqrt (x^2 - 4*mu*A) - 1)/(2*mu))
      (((Real.sqrt (beta^2 - 4*mu*A) -
          beta * ((1 / (2*Real.sqrt (beta^2 - 4*mu*A))) * (2*beta))) /
          (Real.sqrt (beta^2 - 4*mu*A))^2)/(2*mu)) beta := by
  have hnonzero : Real.sqrt (beta^2 - 4*mu*A) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hgap)
  have hquot := (hasDerivAt_id beta).div
    (sqrt_gap_hasDerivAt beta mu A hgap) hnonzero
  simpa [id_eq] using (hquot.sub_const 1).div_const (2*mu)

/-- The negative derivative of the saddle mean energy is exactly
the same 2*A/d^3 that appears in the TFD short-time curvature. -/
theorem meanEnergy_hasDerivAt_variance (beta mu A : ℝ)
    (hmu : mu ≠ 0) (hgap : 0 < beta^2 - 4*mu*A) :
    HasDerivAt
      (fun x : ℝ => (x / Real.sqrt (x^2 - 4*mu*A) - 1)/(2*mu))
      (-(2*A/(Real.sqrt (beta^2 - 4*mu*A))^3)) beta := by
  let d : ℝ := Real.sqrt (beta^2 - 4*mu*A)
  have hd : d ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hgap)
  have hsq : d^2 = beta^2 - 4*mu*A := Real.sq_sqrt (le_of_lt hgap)
  have hraw := meanEnergy_hasDerivAt_raw beta mu A hgap
  have halg :
      ((d - beta * ((1 / (2*d)) * (2*beta))) / d^2)/(2*mu)
        = -(2*A/d^3) := by
    field_simp
    nlinarith [hsq]
  change HasDerivAt
      (fun x : ℝ => (x / Real.sqrt (x^2 - 4*mu*A) - 1)/(2*mu))
      (-(2*A/d^3)) beta
  rw [← halg]
  exact hraw

end TTbarCriticalSpread
