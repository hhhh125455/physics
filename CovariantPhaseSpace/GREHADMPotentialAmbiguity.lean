import Mathlib

/-!
# Einstein--Hilbert versus ADM symplectic potentials: exact/corner audit

Freidel--Geiller--Pranzetti (JHEP 11 (2020) 026), equation (2.16),
show that the integrated Einstein--Hilbert potential differs from the
canonical GR potential by a field-space exact variation and a corner
potential.  In a closed spatial section, the latter is absent.

This file checks the finite-dimensional, tangent-space algebra:
adding a *symmetric Hessian* of a boundary functional does not affect
the antisymmetrized variation (the presymplectic 2-form), and the only
possible discrepancy is the corner contribution.

This DOES NOT derive the EH/ADM potential identity from the metric
action: that geometric result is taken from the cited publication.
-/

namespace CovariantPhaseSpace

section ExactVariationAndCorner

variable {K V : Type*} [Field K]
variable [AddCommGroup V] [Module K V]

/-- A linearized 1-form derivative represented by a bilinear map. -/
def antisymmetrizedDerivative
    (Dtheta : V →ₗ[K] Module.Dual K V)
    (u v : V) : K :=
  Dtheta u v - Dtheta v u

/-- Exact field-space 1-form additions do not change the symplectic
2-form because the Hessian is symmetric: δ²B=0. -/
theorem closed_slice_exact_variation_does_not_change_omega
    (Dtheta : V →ₗ[K] Module.Dual K V)
    (Hessian : V →ₗ[K] Module.Dual K V)
    (hSym : ∀ u v : V, Hessian u v = Hessian v u)
    (u v : V) :
    antisymmetrizedDerivative (Dtheta + Hessian) u v =
      antisymmetrizedDerivative Dtheta u v := by
  simp only [antisymmetrizedDerivative, LinearMap.add_apply]
  rw [hSym u v]
  ring

/-- With a corner derivative, the difference is precisely the
antisymmetrized corner contribution. Closed Σ means corner=0. -/
theorem exact_and_corner_potential_difference
    (Dtheta Hessian Corner : V →ₗ[K] Module.Dual K V)
    (hSym : ∀ u v : V, Hessian u v = Hessian v u)
    (u v : V) :
    antisymmetrizedDerivative (Dtheta + Hessian + Corner) u v =
      antisymmetrizedDerivative Dtheta u v +
        antisymmetrizedDerivative Corner u v := by
  simp only [antisymmetrizedDerivative, LinearMap.add_apply]
  rw [hSym u v]
  ring

end ExactVariationAndCorner

end CovariantPhaseSpace
