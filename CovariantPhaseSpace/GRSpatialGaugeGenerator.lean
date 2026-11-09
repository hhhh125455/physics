import Mathlib

/-!
# H3 (CP) partial check: canonical cotangent lift of a symmetry generator

For a fixed vector field ξ on a closed spatial Σ, the Lie derivative
A = ℒ_ξ acts linearly on metric tensors h. Its cotangent lift on
(h, π) is (A h, -A* π), where A* is the algebraic dual.

The canonical momentum map H_ξ = π(A h) has derivative
δH_ξ = δπ(A h) + π(A δh), and with Ω = δπ ∧ δh one obtains
ι_X Ω = -δH_ξ. This proof does not assert that the Hamiltonian
constraint generates normal spacetime diffeomorphisms. Establishing
that separate CP part requires the ADM constraints and projectability.
-/

namespace CovariantPhaseSpace

section CotangentLift

variable {K V : Type*} [Field K]
variable [AddCommGroup V] [Module K V]

def canonicalCotangentPairing (u v : V × Module.Dual K V) : K :=
  u.2 v.1 - v.2 u.1

def cotangentLiftOfLinearSymmetry (A : V →ₗ[K] V)
    (qp : V × Module.Dual K V) : V × Module.Dual K V :=
  (A qp.1, -(qp.2.comp A))

def momentMapVariation (A : V →ₗ[K] V)
    (qp u : V × Module.Dual K V) : K :=
  u.2 (A qp.1) + qp.2 (A u.1)

/-- The Hamiltonian generator for a cotangent-lifted spatial symmetry
obeys the precise sign convention of the work note. -/
theorem cotangent_lift_is_hamiltonian
    (A : V →ₗ[K] V)
    (qp u : V × Module.Dual K V) :
    canonicalCotangentPairing (cotangentLiftOfLinearSymmetry A qp) u =
      -momentMapVariation A qp u := by
  simp [canonicalCotangentPairing, cotangentLiftOfLinearSymmetry,
    momentMapVariation, LinearMap.comp_apply]
  ring

end CotangentLift

end CovariantPhaseSpace
