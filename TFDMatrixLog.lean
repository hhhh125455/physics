import Mathlib

/-!
A direct check of the TFD density-matrix logarithm.
The eigenbasis theorem is a matrix identity.
The operator theorem uses the continuous functional calculus rather than
illegally applying the scalar logarithm product formula to matrices.
-/

noncomputable section

theorem tfd_log_energy_weight
    (beta E Z : ℝ) (hZ : 0 < Z) :
    Real.log (Real.exp (-beta * E) / Z) =
      -beta * E - Real.log Z := by
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ)]
  simp

theorem tfd_log_in_energy_basis
    {n : ℕ} (E : Fin n → ℝ) (beta Z : ℝ)
    (hZ : 0 < Z) :
    Matrix.diagonal (fun i : Fin n =>
      Real.log (Real.exp (-beta * E i) / Z)) =
    Matrix.diagonal (fun i : Fin n =>
      -beta * E i - Real.log Z) := by
  congr 1
  funext i
  exact tfd_log_energy_weight beta (E i) Z hZ

theorem tfd_log_normalized_exp
    {A : Type*}
    [NormedRing A] [StarRing A]
    [NormedAlgebra ℝ A] [NormedAlgebra ℚ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [CompleteSpace A] [ContinuousStar A]
    (a : A) (Z : ℝ)
    (ha : IsSelfAdjoint a) (hZ : 0 < Z) :
    CFC.log (Z⁻¹ • NormedSpace.exp a) =
      a - (algebraMap ℝ A) (Real.log Z) := by
  have hu : IsUnit (NormedSpace.exp a) :=
    NormedSpace.isUnit_exp a
  have hs : ∀ x ∈ spectrum ℝ (NormedSpace.exp a), x ≠ 0 := by
    intro x hx hzero
    subst x
    exact (spectrum.zero_notMem ℝ hu) hx
  have hr : Z⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hZ)
  calc
    CFC.log (Z⁻¹ • NormedSpace.exp a)
        = (algebraMap ℝ A) (Real.log Z⁻¹) +
          CFC.log (NormedSpace.exp a) :=
            CFC.log_smul (NormedSpace.exp a) hs hr ha.exp
    _ = (algebraMap ℝ A) (-Real.log Z) + a := by
          rw [Real.log_inv, CFC.log_exp a ha]
    _ = a - (algebraMap ℝ A) (Real.log Z) := by
          rw [map_neg]
          abel

-- The original physical statement with a Hermitian Hamiltonian H and inverse temperature beta.
-- Here scalar multiplication by (-beta) denotes -beta * H, and algebraMap r denotes r * I.
theorem tfd_log_thermal_hamiltonian
    {A : Type*}
    [NormedRing A] [StarRing A]
    [NormedAlgebra ℝ A] [NormedAlgebra ℚ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [CompleteSpace A] [ContinuousStar A] [StarModule ℝ A]
    (H : A) (beta Z : ℝ)
    (hH : IsSelfAdjoint H) (hZ : 0 < Z) :
    CFC.log (Z⁻¹ • NormedSpace.exp ((-beta) • H)) =
      (-beta) • H - (algebraMap ℝ A) (Real.log Z) := by
  exact tfd_log_normalized_exp ((-beta) • H) Z
    ((IsSelfAdjoint.all (-beta)).smul hH) hZ
