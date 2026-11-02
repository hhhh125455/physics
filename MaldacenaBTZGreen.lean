import Mathlib

/-!
  Maldacena, "Eternal black holes in AdS", eqs. (2.5), (2.6).
  These theorems check the algebra of the AdS3/BTZ embedding,
  the cross-boundary cosh(t1+t2) identity and m² = q(q-2).
  They do NOT formalize the Green-function PDE, the boundary
  asymptotic limit, the method of images or the iε prescription.
-/

noncomputable section

theorem ads3_scalar_mass_relation (Delta : ℝ) :
    (2 * Delta) * (2 * Delta - 2) =
      4 * Delta * (Delta - 1) := by
  ring

theorem ads3_cosh_difference (x y : ℝ) :
    Real.cosh x * Real.cosh y -
    Real.sinh x * Real.sinh y = Real.cosh (x-y) := by
  rw [Real.cosh_sub]

theorem ads3_cosh_sum (x y : ℝ) :
    Real.cosh x * Real.cosh y +
    Real.sinh x * Real.sinh y = Real.cosh (x+y) := by
  rw [Real.cosh_add]

theorem ads3_right_right_embedding
    (u₁ u₂ a₁ a₂ φ₁ φ₂ t₁ t₂ : ℝ) :
    u₁*u₂*(Real.cosh φ₁*Real.cosh φ₂ -
            Real.sinh φ₁*Real.sinh φ₂) -
    a₁*a₂*(Real.cosh t₁*Real.cosh t₂ -
            Real.sinh t₁*Real.sinh t₂) =
    u₁*u₂*Real.cosh (φ₁-φ₂) -
    a₁*a₂*Real.cosh (t₁-t₂) := by
  simp only [Real.cosh_sub]
  ring

theorem ads3_right_left_embedding
    (u₁ u₂ a₁ a₂ φ₁ φ₂ t₁ t₂ : ℝ) :
    u₁*u₂*(Real.cosh φ₁*Real.cosh φ₂ -
            Real.sinh φ₁*Real.sinh φ₂) +
    a₁*a₂*(Real.cosh t₁*Real.cosh t₂ +
            Real.sinh t₁*Real.sinh t₂) =
    u₁*u₂*Real.cosh (φ₁-φ₂) +
    a₁*a₂*Real.cosh (t₁+t₂) := by
  simp only [Real.cosh_sub, Real.cosh_add]
  ring
