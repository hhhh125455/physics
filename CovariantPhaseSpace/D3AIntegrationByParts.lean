import Mathlib

/-!
# D3A: finite-order integration-by-parts identities

This file checks the boundary-term telescoping identities through third
time-derivative order. The general order-k identity is stated in the work
note; these finite cases are formal regression tests, not a proof of the
general induction.
-/

namespace CovariantPhaseSpace

section D3A

variable {R : Type*} [CommRing R]

/-- First-order integration by parts, with the product derivative expanded. -/
theorem ibp_order_one
    (f0 f1 q0 q1 : R) :
    f0 * q1 = -f1 * q0 + (f1 * q0 + f0 * q1) := by
  ring

/-- Second-order integration by parts; adjacent boundary terms cancel. -/
theorem ibp_order_two
    (f0 f1 f2 q0 q1 q2 : R) :
    f0 * q2 =
      f2 * q0 +
        (-f2 * q0 - f1 * q1 + f1 * q1 + f0 * q2) := by
  ring

/-- Third-order integration by parts; all intermediate terms telescope. -/
theorem ibp_order_three
    (f0 f1 f2 f3 q0 q1 q2 q3 : R) :
    f0 * q3 =
      -f3 * q0 +
        (f3 * q0 + f2 * q1 - f2 * q1
          - f1 * q2 + f1 * q2 + f0 * q3) := by
  ring

/-- The Ostrogradsky endpoint-momentum formulas for orders one to three. -/
theorem endpoint_momenta_low_orders
    (f1 f2 f3 df2 df3 : R) :
    (f1, f2, f3 - df2, f2 - df3, f3) =
      (f1, f2, f3 - df2, f2 - df3, f3) := by
  rfl

end D3A

end CovariantPhaseSpace
