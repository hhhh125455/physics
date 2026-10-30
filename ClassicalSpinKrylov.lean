import Mathlib
import HoravaQNM

/-!
# Low-order classical spin Krylov consistency checks

Let c = 2 χ S. The normalized spectral moments of the uniform-sphere
spin model are μ₂ = c²/5 and μ₄ = 3c⁴/35.
The low-order Lanczos coefficients satisfy b₁² = c²/5
and b₂² = 8c²/35.

These theorems check the algebraic moment-to-Lanczos identities.
They do NOT derive the moments from the classical Hamiltonian.
-/

namespace ClassicalSpinKrylov

theorem second_moment_identity (c : ℝ) :
    c ^ 2 / 5 = c ^ 2 / 5 := by
  rfl

theorem fourth_moment_identity (c : ℝ) :
    3 * c ^ 4 / 35 =
      (c ^ 2 / 5) ^ 2 + (c ^ 2 / 5) * (8 * c ^ 2 / 35) := by
  ring

theorem second_lanczos_identity (c : ℝ) :
    (c ^ 2 / 5) * (8 * c ^ 2 / 35) =
      3 * c ^ 4 / 35 - (c ^ 2 / 5) ^ 2 := by
  ring

end ClassicalSpinKrylov
