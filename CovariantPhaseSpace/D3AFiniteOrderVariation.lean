import CovariantPhaseSpace.D3AGeneralIBP

/-!
# D3A: general finite-order Lagrangian temporal variation

Starting from F_m D^m(q) for ALL m from 0 to k, this theorem
reorganizes the finite sum into a bulk Euler-Lagrange contribution
plus one time derivative of the complete boundary contribution.

This establishes the general finite-order temporal integration-by-parts
step in the work note. It does not assert that spatial integrations,
functional spaces, the Legendre constraint surface or global pullback
properties have been constructed.
-/

namespace CovariantPhaseSpace

section GeneralFiniteOrderVariation

variable {R : Type*} [CommRing R]

theorem finite_order_bulk_and_boundary
    (D : R →+ R)
    (hLeibniz : ∀ f q : R, D (f * q) = D f * q + f * D q)
    (k : ℕ) (F : ℕ → R) (q : R) :
    (∑ m ∈ Finset.range (k + 1), F m * repeatedTimeDerivative D m q) =
      (∑ m ∈ Finset.range (k + 1), ibpInterior D m (F m)) * q
        + D (∑ m ∈ Finset.range (k + 1), ibpBoundary D m (F m) q) := by
  calc
    (∑ m ∈ Finset.range (k + 1), F m * repeatedTimeDerivative D m q) =
        ∑ m ∈ Finset.range (k + 1),
          (ibpInterior D m (F m) * q +
            D (ibpBoundary D m (F m) q)) := by
              apply Finset.sum_congr rfl
              intro m hm
              exact integration_by_parts_all_orders D hLeibniz m (F m) q
    _ = (∑ m ∈ Finset.range (k + 1), ibpInterior D m (F m)) * q
          + D (∑ m ∈ Finset.range (k + 1), ibpBoundary D m (F m) q) := by
            rw [Finset.sum_add_distrib, Finset.sum_mul, map_sum]

end GeneralFiniteOrderVariation

end CovariantPhaseSpace
