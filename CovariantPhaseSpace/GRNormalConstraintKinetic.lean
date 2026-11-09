import Mathlib

/-!
# GR H3 normal-deformation consistency: exact quadratic expansion

At one point in an h-orthonormal frame, a symmetric ADM momentum
has 6 independent components p_0,p_1,p_2,p_3,p_4,p_5, where
the last three encode the off-diagonal components.

The kinetic Hamiltonian-constraint numerator is
Q(p) = p_ij p_ij - (trace p)^2/2
     = sum_diag p_i^2 + 2 sum_offdiag p_i^2 - (sum_diag p_i)^2/2.

The exact polynomial expansion shows that its directional derivative
is the expected expression used in {h,H[N]} = 2N K.
This is a pointwise algebraic computation, NOT a proof of the full
normal-diffeomorphism projectability or transformation of lapse/shift.
-/

namespace CovariantPhaseSpace

section GRNormalHamiltonian

noncomputable def admQuadratic6 (p : Fin 6 → ℝ) : ℝ :=
  p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 +
    2 * (p 3 ^ 2 + p 4 ^ 2 + p 5 ^ 2) -
    (p 0 + p 1 + p 2) ^ 2 / 2

def admQuadraticDifferential6
    (p u : Fin 6 → ℝ) : ℝ :=
  (2 * p 0 - (p 0 + p 1 + p 2)) * u 0 +
    (2 * p 1 - (p 0 + p 1 + p 2)) * u 1 +
    (2 * p 2 - (p 0 + p 1 + p 2)) * u 2 +
    4 * (p 3 * u 3 + p 4 * u 4 + p 5 * u 5)

/-- Exact second-order expansion in ε: the linear term is the
Hamiltonian differential and the remaining term is ε²Q(u). -/
theorem admHamiltonianNormalExpansion
    (p u : Fin 6 → ℝ) (eps : ℝ) :
    admQuadratic6 (fun i => p i + eps * u i) =
      admQuadratic6 p +
        eps * admQuadraticDifferential6 p u +
        eps ^ 2 * admQuadratic6 u := by
  unfold admQuadratic6 admQuadraticDifferential6
  ring

end GRNormalHamiltonian

end CovariantPhaseSpace
