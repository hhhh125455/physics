import Mathlib

/-!
Audit of TTbar-TFD-Spread source lines 42--68.
Scope: finite-dimensional spectral trace, torus S reparametrization,
and thermal duality CONDITIONAL on modular invariance.
The identification of the path integral with a Hilbert-space trace
and modular invariance are physical inputs, not algebraic identities.
-/

namespace TTbarTFD

noncomputable def cylinderEnergy (h hbar cL cR : ℝ) : ℝ :=
  h + hbar - (cL + cR) / 24

noncomputable def cylinderMomentum (h hbar cL cR : ℝ) : ℝ :=
  h - hbar - (cL - cR) / 24

/-- A thermal exponent with an angular twist. -/
noncomputable def twistedExponent
    (β θ h hbar cL cR : ℝ) : ℂ :=
  ((-β * cylinderEnergy h hbar cL cR : ℝ) : ℂ) +
    Complex.I * (((θ * cylinderMomentum h hbar cL cR : ℝ)) : ℂ)

/-- Separating the exponent into left and right CFT weights. -/
theorem twistedExponent_chiral (β θ h hbar cL cR : ℝ) :
    twistedExponent β θ h hbar cL cR =
      (-(β : ℂ) + Complex.I * (θ : ℂ)) *
        ((h : ℂ) - (cL : ℂ) / 24) +
      (-(β : ℂ) - Complex.I * (θ : ℂ)) *
        ((hbar : ℂ) - (cR : ℂ) / 24) := by
  unfold twistedExponent cylinderEnergy cylinderMomentum
  push_cast
  ring

/-- The full finite spectral trace agrees with the left/right factorization. -/
theorem finite_twisted_trace_chiral
    (N : ℕ) (h hbar : Fin N → ℝ) (cL cR β θ : ℝ) :
    (∑ n : Fin N, Complex.exp
      (twistedExponent β θ (h n) (hbar n) cL cR)) =
    (∑ n : Fin N, Complex.exp
      ((-(β : ℂ) + Complex.I * (θ : ℂ)) *
        ((h n : ℂ) - (cL : ℂ) / 24) +
      (-(β : ℂ) - Complex.I * (θ : ℂ)) *
        ((hbar n : ℂ) - (cR : ℂ) / 24))) := by
  apply Finset.sum_congr rfl
  intro n _
  rw [twistedExponent_chiral]

/-- When central charges agree, spatial momentum is h-hbar. -/
theorem momentum_equal_charges (h hbar c : ℝ) :
    cylinderMomentum h hbar c c = h - hbar := by
  unfold cylinderMomentum
  ring

/-- At theta=0 the trace uses ONLY the thermal Hamiltonian. -/
theorem untwistedExponent (β h hbar cL cR : ℝ) :
    twistedExponent β 0 h hbar cL cR =
      ((-β * cylinderEnergy h hbar cL cR : ℝ) : ℂ) := by
  simp [twistedExponent]

/-- An elementary counterexample to replacing old spatial momentum
    by the rotated Euclidean-time Hamiltonian. -/
theorem old_momentum_not_new_hamiltonian :
    Real.exp (-(1 : ℝ)) ≠
      Real.exp (-(2 * Real.pi) * (0 : ℝ)) := by
  intro heq
  have h := Real.exp_injective heq
  norm_num at h

/- Geometry for spatial circumference 2*pi and Euclidean time beta. -/
noncomputable def rectangularTau (β : ℝ) : ℂ :=
  Complex.I * ((β : ℂ) / (2 * (Real.pi : ℂ)))

noncomputable def dualInverseTemperature (β : ℝ) : ℝ :=
  (2 * Real.pi) ^ 2 / β

/-- The S transformation of the rectangular torus. -/
theorem rectangular_S (β : ℝ) (hβ : β ≠ 0) :
    -(1 : ℂ) / rectangularTau β =
      rectangularTau (dualInverseTemperature β) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hπc : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  unfold rectangularTau dualInverseTemperature
  push_cast
  field_simp [hβc, hπc, Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

/-- S is an involution on positive inverse temperatures. -/
theorem dual_inverse_involutive (β : ℝ) (hβ : β ≠ 0) :
    dualInverseTemperature (dualInverseTemperature β) = β := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold dualInverseTemperature
  field_simp [hβ, hπ]
  ring

/-- Modular invariance is kept as an explicit hypothesis. -/
def ModularSInvariant (Z : ℂ → ℂ) : Prop :=
  ∀ τ : ℂ, Z τ = Z (-(1 : ℂ) / τ)

/-- The thermal duality is a theorem only once S invariance is assumed. -/
theorem thermal_S_duality (Z : ℂ → ℂ) (hS : ModularSInvariant Z)
    (β : ℝ) (hβ : 0 < β) :
    Z (rectangularTau β) =
      Z (rectangularTau (dualInverseTemperature β)) := by
  rw [hS (rectangularTau β)]
  rw [rectangular_S β (ne_of_gt hβ)]

end TTbarTFD
