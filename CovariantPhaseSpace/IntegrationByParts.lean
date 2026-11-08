import Mathlib

/-!
# D3A: finite telescoping identity

This file formalizes the finite algebraic cancellation underlying the
repeated integration-by-parts formula in the work note.

It does not formalize spacetime integration, functional-analytic domains,
or the passage from a Lagrangian density to its Euler-Lagrange operator.
Those are analytic/geometric obligations and are tracked separately.
-/

namespace CovariantPhaseSpace

/-- Finite telescoping sum: all interior terms cancel. -/
theorem finite_telescoping
    {A : Type*} [AddCommGroup A] (f : ℕ → A) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f i - f (i + 1))) = f 0 - f n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end CovariantPhaseSpace
