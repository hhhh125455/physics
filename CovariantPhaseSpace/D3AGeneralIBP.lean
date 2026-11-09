import Mathlib

/-!
# General D3A repeated integration-by-parts identity (all finite orders)

Unlike the old ring-only order-1/2/3 fixtures, this proof takes an
actual additive derivation D with the Leibniz rule.  It checks the
boundary/interior decomposition for EVERY natural-number order.

It does not prove spacetime integration, spatial jet bundle regularity,
or the constrained Legendre pullback (those require H0/H1/H2).
-/

namespace CovariantPhaseSpace

section GeneralIntegrationByParts

variable {R : Type*} [CommRing R]

/-- The n-th positive time derivative D^n q. -/
def repeatedTimeDerivative (D : R →+ R) : ℕ → R → R
  | 0, q => q
  | n + 1, q => D (repeatedTimeDerivative D n q)

/-- The n-th signed derivative (-D)^n f, written in a form
that makes the induction relation explicit. -/
def ibpInterior (D : R →+ R) : ℕ → R → R
  | 0, f => f
  | n + 1, f => ibpInterior D n ((-D) f)

/-- Boundary contribution, the finite sum
Σ_{j=0}^{n-1} (-D)^(n-1-j) f ⋅ D^j q, encoded recursively. -/
def ibpBoundary (D : R →+ R) : ℕ → R → R → R
  | 0, _, _ => 0
  | n + 1, f, q =>
      f * repeatedTimeDerivative D n q +
        ibpBoundary D n ((-D) f) q

/-- Work-note D3A, for all finite n:
  f (D^n q) = ((-D)^n f) q + D(B_n(f,q)).
The hypothesis is exactly the derivative product rule. -/
theorem integration_by_parts_all_orders
    (D : R →+ R)
    (hLeibniz : ∀ f q : R, D (f * q) = D f * q + f * D q)
    (n : ℕ) (f q : R) :
    f * repeatedTimeDerivative D n q =
      ibpInterior D n f * q + D (ibpBoundary D n f q) := by
  induction n generalizing f with
  | zero =>
      simp [repeatedTimeDerivative, ibpInterior, ibpBoundary]
  | succ n ih =>
      have hneg : (-D) f = -(D f) := by rfl
      calc
        f * repeatedTimeDerivative D (n + 1) q =
          D (f * repeatedTimeDerivative D n q) +
            (-D) f * repeatedTimeDerivative D n q := by
              change f * D (repeatedTimeDerivative D n q) =
                D (f * repeatedTimeDerivative D n q) +
                  (-D) f * repeatedTimeDerivative D n q
              rw [hLeibniz f (repeatedTimeDerivative D n q), hneg]
              ring
        _ = D (f * repeatedTimeDerivative D n q) +
              (ibpInterior D n ((-D) f) * q +
                D (ibpBoundary D n ((-D) f) q)) := by
                  rw [ih ((-D) f)]
        _ = ibpInterior D (n + 1) f * q +
              D (ibpBoundary D (n + 1) f q) := by
                change
                  D (f * repeatedTimeDerivative D n q) +
                      (ibpInterior D n ((-D) f) * q +
                        D (ibpBoundary D n ((-D) f) q)) =
                    ibpInterior D n ((-D) f) * q +
                      D (f * repeatedTimeDerivative D n q +
                        ibpBoundary D n ((-D) f) q)
                rw [map_add]
                ring

end GeneralIntegrationByParts

end CovariantPhaseSpace
