import Mathlib

/-!
# Continuous weighted integration for the original spectrum.

This file does *not* replace the original weight by the Laguerre weight.
All differentiation below is for the exact logistic-deformed weight.

Full infinite-interval integration additionally requires proving
the endpoint limits and integrability for polynomial products.
-/

namespace SchrodingerKrylovAudit

noncomputable def originalWeight (c q x : ℝ) : ℝ :=
  x * Real.exp (-c * x) / (1 + q * Real.exp (-2 * c * x))

noncomputable def originalRho (c q x : ℝ) : ℝ :=
  q * Real.exp (-2 * c * x) / (1 + q * Real.exp (-2 * c * x))

theorem originalWeight_den_pos (c q x : ℝ) (hq : 0 ≤ q) :
    0 < 1 + q * Real.exp (-2 * c * x) := by
  have h : 0 ≤ q * Real.exp (-2 * c * x) :=
    mul_nonneg hq (Real.exp_pos _).le
  linarith

/-- The literal derivative of x*w(x) for the original fermion model. -/
theorem original_xweight_hasDerivAt (c q x : ℝ) (hq : 0 ≤ q) :
    HasDerivAt (fun y : ℝ => y * originalWeight c q y)
      ((2 - c * x + 2 * c * x * originalRho c q x) * originalWeight c q x) x := by
  have hd : 1 + q * Real.exp (-2 * c * x) ≠ 0 :=
    ne_of_gt (originalWeight_den_pos c q x hq)
  have hlin1 : HasDerivAt (fun y : ℝ => -c * y) (-c) x := by
    convert (hasDerivAt_id x).const_mul (-c) using 1 <;> ring
  have hlin2 : HasDerivAt (fun y : ℝ => -2 * c * y) (-2 * c) x := by
    convert (hasDerivAt_id x).const_mul (-2 * c) using 1 <;> ring
  have hE1 : HasDerivAt (fun y : ℝ => Real.exp (-c * y))
      (Real.exp (-c * x) * (-c)) x :=
    (Real.hasDerivAt_exp (-c * x)).comp x hlin1
  have hE2 : HasDerivAt (fun y : ℝ => Real.exp (-2 * c * y))
      (Real.exp (-2 * c * x) * (-2 * c)) x :=
    (Real.hasDerivAt_exp (-2 * c * x)).comp x hlin2
  have hD : HasDerivAt (fun y : ℝ => 1 + q * Real.exp (-2 * c * y))
      (q * (Real.exp (-2 * c * x) * (-2 * c))) x :=
    (hasDerivAt_const x (1 : ℝ)).add (hE2.const_mul q)
  have hU : HasDerivAt (fun y : ℝ => y ^ 2 * Real.exp (-c * y))
      (2 * x * Real.exp (-c * x) + x ^ 2 * (Real.exp (-c * x) * (-c))) x := by
    convert ((hasDerivAt_id x).pow 2).mul hE1 using 1 <;> ring
  have hmain := hU.div hD hd
  convert hmain using 1
  · funext y
    simp only [originalWeight]
    ring
  · unfold originalWeight originalRho
    field_simp
    <;> ring

/-- The product rule needed for the diagonal Freud sum rule, including
the nonpolynomial logistic weight exactly. -/
theorem original_xwP2_hasDerivAt
    (c q x : ℝ) (hq : 0 ≤ q)
    (P P' : ℝ → ℝ) (hP : HasDerivAt P (P' x) x) :
    HasDerivAt
      (fun y => (y * originalWeight c q y) * (P y) ^ 2)
      (((2 - c * x + 2 * c * x * originalRho c q x) *
          originalWeight c q x) * (P x) ^ 2
       + (x * originalWeight c q x) * (2 * P x * P' x)) x := by
  convert ((original_xweight_hasDerivAt c q x hq).mul (hP.pow 2)) using 1 <;> ring

/-- A genuine finite-interval integration-by-parts formula, with
its derivative/integrability hypotheses exposed rather than hidden. -/
theorem original_ibp_finite
    (c q a b : ℝ) (hq : 0 ≤ q)
    (P P' : ℝ → ℝ)
    (hP : ∀ x : ℝ, HasDerivAt P (P' x) x)
    (hInt : IntervalIntegrable
      (fun x => ((2 - c * x + 2 * c * x * originalRho c q x) *
          originalWeight c q x) * (P x) ^ 2
       + (x * originalWeight c q x) * (2 * P x * P' x))
      MeasureTheory.volume a b) :
    (∫ x in a..b,
      ((2 - c * x + 2 * c * x * originalRho c q x) *
          originalWeight c q x) * (P x) ^ 2
       + (x * originalWeight c q x) * (2 * P x * P' x)) =
      (b * originalWeight c q b) * (P b) ^ 2 -
      (a * originalWeight c q a) * (P a) ^ 2 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => original_xwP2_hasDerivAt c q x hq P P' (hP x)) hInt

end SchrodingerKrylovAudit
