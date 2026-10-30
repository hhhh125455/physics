import Mathlib

/-!
TTbar TFD manuscript, lines 146--178.
Formally checks the exact algebra beneath modular high-temperature
asymptotics, derivatives of the leading free energy, the canonical
thermodynamic identities, and the Cardy saddle point.

IMPORTANT: modular invariance, low-temperature vacuum dominance,
interchange of asymptotics with derivatives, and an asymptotic density
of states are physical/analytic input hypotheses, NOT hidden theorems.
-/

namespace TTbarTFDHighTemperature

noncomputable def AOfC (c : ℝ) : ℝ := Real.pi ^ 2 * c / 3

noncomputable def DualBeta (β : ℝ) : ℝ := 4 * Real.pi ^ 2 / β

noncomputable def leadingLogZ (A β : ℝ) : ℝ := A / β
noncomputable def leadingZ (A β : ℝ) : ℝ := Real.exp (leadingLogZ A β)
noncomputable def leadingEnergy (A β : ℝ) : ℝ := A / β ^ 2
noncomputable def leadingEntropy (A β : ℝ) : ℝ := 2 * A / β
noncomputable def leadingFreeEnergy (A β : ℝ) : ℝ := -(A / β ^ 2)

/-- Modular duality plus a specified correction to low-T vacuum dominance
    gives a corresponding EXACT high-T formula with the correction. -/
theorem modular_vacuum_with_correction
    (Z correction : ℝ → ℝ) (c β : ℝ) (hβ : 0 < β)
    (hS : ∀ x : ℝ, 0 < x → Z x = Z (DualBeta x))
    (hlow : ∀ x : ℝ, 0 < x →
      Z x = Real.exp (x * c / 12) * (1 + correction x)) :
    Z β = leadingZ (AOfC c) β * (1 + correction (DualBeta β)) := by
  have hdual : 0 < DualBeta β := by
    unfold DualBeta
    positivity
  rw [hS β hβ, hlow (DualBeta β) hdual]
  congr 1
  apply congrArg Real.exp
  unfold leadingLogZ AOfC DualBeta
  field_simp [ne_of_gt hβ]
  ring

/-- The leading high-temperature log partition function has its
    genuine mathematical derivative; this is not a derivative
    estimate for the exact Z. -/
theorem leadingLogZ_hasDerivAt (A β : ℝ) (hβ : β ≠ 0) :
    HasDerivAt (leadingLogZ A) (-A / β ^ 2) β := by
  have h := ((hasDerivAt_id β).inv hβ).const_mul A
  have h' : HasDerivAt (leadingLogZ A) (A * (-1 / β ^ 2)) β := by
    simpa only [leadingLogZ, id_eq, div_eq_mul_inv] using h
  convert h' using 1 <;> ring

/-- Derivative of the exact leading approximation Z_0=exp(A/beta). -/
theorem leadingZ_hasDerivAt (A β : ℝ) (hβ : β ≠ 0) :
    HasDerivAt (leadingZ A)
      (leadingZ A β * (-A / β ^ 2)) β := by
  have h := (leadingLogZ_hasDerivAt A β hβ).exp
  change HasDerivAt (fun x : ℝ => Real.exp (leadingLogZ A x))
    (Real.exp (leadingLogZ A β) * (-A / β ^ 2)) β
  exact h

/-- E_0 = -d(log Z_0)/d beta, under the leading approximation. -/
theorem energy_from_logZ (A β : ℝ) :
    -(-A / β ^ 2) = leadingEnergy A β := by
  unfold leadingEnergy
  ring

/-- S_0=(1-beta d_beta)log Z_0. -/
theorem entropy_from_logZ (A β : ℝ) (hβ : β ≠ 0) :
    leadingLogZ A β - β * (-A / β ^ 2) =
      leadingEntropy A β := by
  unfold leadingLogZ leadingEntropy
  field_simp [hβ]
  ring

/-- F_0=-(1/beta)log Z_0 = -A/beta^2. -/
theorem free_energy_from_logZ (A β : ℝ) (hβ : β ≠ 0) :
    -(leadingLogZ A β / β) = leadingFreeEnergy A β := by
  unfold leadingLogZ leadingFreeEnergy
  field_simp [hβ]

/-- F_0=-A T^2, where T is inverse temperature. -/
theorem free_energy_temperature (A T : ℝ) (hT : T ≠ 0) :
    leadingFreeEnergy A (1 / T) = -A * T ^ 2 := by
  unfold leadingFreeEnergy
  field_simp [hT]

/-- Canonical thermal relation S_0=beta*(E_0-F_0). -/
theorem entropy_energy_free_energy (A β : ℝ) (hβ : β ≠ 0) :
    leadingEntropy A β =
      β * (leadingEnergy A β - leadingFreeEnergy A β) := by
  unfold leadingEntropy leadingEnergy leadingFreeEnergy
  field_simp [hβ]
  ring

/-- Cardy entropy obtained by eliminating beta from canonical formulas. -/
theorem cardy_entropy_elimination (A β : ℝ)
    (hA : 0 ≤ A) (hβ : 0 < β) :
    leadingEntropy A β =
      2 * Real.sqrt (A * leadingEnergy A β) := by
  have hs : (A / β) ^ 2 = A * leadingEnergy A β := by
    unfold leadingEnergy
    field_simp [ne_of_gt hβ]
  rw [← hs, Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg (div_nonneg hA (le_of_lt hβ))]
  unfold leadingEntropy
  ring

/-- Reparametrize E=x^2. Completing the square gives the
    GLOBAL saddle, not just a guessed stationary point. -/
theorem saddle_square_completion (A β x : ℝ)
    (hA : 0 ≤ A) (hβ : β ≠ 0) :
    2 * Real.sqrt A * x - β * x ^ 2 =
      A / β - β * (x - Real.sqrt A / β) ^ 2 := by
  have hs : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
  field_simp [hβ]
  nlinarith [hs]

/-- For beta>0 the saddle is an upper bound for the exponent. -/
theorem saddle_upper_bound (A β x : ℝ)
    (hA : 0 ≤ A) (hβ : 0 < β) :
    2 * Real.sqrt A * x - β * x ^ 2 ≤ A / β := by
  rw [saddle_square_completion A β x hA (ne_of_gt hβ)]
  have hs : 0 ≤ β * (x - Real.sqrt A / β) ^ 2 :=
    mul_nonneg (le_of_lt hβ) (sq_nonneg _)
  linarith

/-- The saddle value is EXACTLY A/beta at x=sqrt(A)/beta. -/
theorem saddle_attained (A β : ℝ)
    (hA : 0 ≤ A) (hβ : 0 < β) :
    2 * Real.sqrt A * (Real.sqrt A / β) -
      β * (Real.sqrt A / β) ^ 2 = A / β := by
  rw [saddle_square_completion A β (Real.sqrt A / β)
    hA (ne_of_gt hβ)]
  ring

/-- Recover E*=A/beta^2 from x*=sqrt(A)/beta. -/
theorem saddle_energy (A β : ℝ)
    (hA : 0 ≤ A) (hβ : β ≠ 0) :
    (Real.sqrt A / β) ^ 2 = leadingEnergy A β := by
  have hs := Real.sq_sqrt hA
  unfold leadingEnergy
  field_simp [hβ]
  nlinarith [hs]

end TTbarTFDHighTemperature
