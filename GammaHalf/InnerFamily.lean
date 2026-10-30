import Mathlib

/-!
# Charged black-hole inner-family audit

Exact scope: algebraic identities obtained after substituting
  w = U*V,  r ~ R*w^p,  exp(-2*sigma) ~ D*w^(4*p-1)
into the reduced Einstein-Maxwell-scalar ODE system.

The three 'balance' lemmas verify the leading-order *coefficients*
of the radius, sigma, and null-constraint equations.
They do not establish existence of a PDE solution, a uniform asymptotic
expansion, admissible characteristic data, or gamma = 1/2.

All proofs are complete and no additional assumptions are declared.
-/

namespace GammaHalf

/-- Matching the charge term in the conformal Einstein equation gives
    4p - 1 = 2ps for r ~ (UV)^p and exp(-2sigma) ~ (r^2)^s. -/
theorem exponent_relation (p s : ℝ)
    (h : 4 * p - 1 = 2 * p * s) :
    2 * p * (2 - s) = 1 := by
  nlinarith

/-- A finite nonzero conformal-factor branch s = 0 requires p = 1/4. -/
theorem finite_conformal_branch (p s : ℝ)
    (h : 4 * p - 1 = 2 * p * s) (hs : s = 0) :
    p = 1 / 4 := by
  subst s
  norm_num at h ⊢
  linarith

/-- Another admissible leading-order exponent relation, p = 1/3 and s = 1/2. -/
theorem alternative_exponent_relation :
    4 * (1 / 3 : ℝ) - 1 =
      2 * (1 / 3 : ℝ) * (1 / 2 : ℝ) := by
  norm_num

/-- For transverse crossing and r ~ (UV)^p, gamma = 2p algebraically,
    so p=1/3 would lead to 2/3, not 1/2. This is conditional. -/
theorem alternative_conditional_gamma :
    2 * (1 / 3 : ℝ) = 2 / 3 := by
  norm_num

/-- Charge coefficient identity D*q^2 = 8p^2R^4 gives
    D*q^2/(4R^4) = 2p^2. -/
theorem charged_coefficient (p R D q : ℝ)
    (hR : R ≠ 0) (h : D * q ^ 2 = 8 * p ^ 2 * R ^ 4) :
    D * q ^ 2 / (4 * R ^ 4) = 2 * p ^ 2 := by
  field_simp
  nlinarith [h]

/-- The radius evolution residual, after cancelling the leading charge
    term using q^2 E/(4 r^4) = 2p^2/w, consists only of E/(4r).
    The latter is subleading for p>0 as w -> 0 in the proposed family. -/
theorem radius_residual (w r p E : ℝ)
    (hw : w ≠ 0) (hr : r ≠ 0) :
    w * (p * (p - 1) * r / w ^ 2) +
      p * r / w +
      w * ((p * r / w) ^ 2 / r) -
      (2 * p ^ 2 / w) * r +
      E / (4 * r) = E / (4 * r) := by
  field_simp
  ring

/-- The sigma evolution equation vanishes at the leading-order level,
    with 4pi a^2 = 3p^2 and the charged coefficient = 2p^2/w. -/
theorem sigma_residual (w r p : ℝ)
    (hw : w ≠ 0) (hr : r ≠ 0) :
    - (-(4 * p - 1) / (2 * w)) -
        w * ((4 * p - 1) / (2 * w ^ 2)) +
        ((p * r / w) +
           w * (p * (p - 1) * r / w ^ 2)) / r -
        (3 * p ^ 2) / w +
        (2 * p ^ 2) / w = 0 := by
  field_simp
  ring

/-- The null constraint vanishes at the leading-order level exactly when
    4pi a^2 = 3p^2, after substituting the power derivatives. -/
theorem null_constraint_residual (w r p : ℝ)
    (hw : w ≠ 0) :
    p * (p - 1) * r / w ^ 2 +
      2 * (p * r / w) * (-(4 * p - 1) / (2 * w)) +
      (3 * p ^ 2) * r / w ^ 2 = 0 := by
  field_simp
  ring

/-- The product ansatz with a vanishing profile at zero forces radius
    zero along the *entire* characteristic edge U=0 (for each V).
    This is an obstruction if an external solution has positive edge radius. -/
theorem product_edge_zero (R : ℝ) (f : ℝ → ℝ)
    (hf : f 0 = 0) (v : ℝ) :
    R * f (0 * v) = 0 := by
  simp [hf]

/-- No uniform product-vanishing ansatz can be compatible with a
    strictly positive radius at a point on that same edge. -/
theorem regular_edge_obstruction (r : ℝ → ℝ → ℝ) (v : ℝ)
    (hedge : ∀ z : ℝ, 0 < z → r 0 z = 0)
    (hv : 0 < v) (hregular : 0 < r 0 v) : False := by
  have hz := hedge v hv
  rw [hz] at hregular
  exact (lt_irrefl (0 : ℝ)) hregular

end GammaHalf
