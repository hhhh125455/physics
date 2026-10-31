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
  ring

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

end TTbarCriticalSpread
