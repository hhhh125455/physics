import Mathlib

/-!
# H2: the initial-data pullback and its presymplectic kernel

These are the exact linearized tangent-space consequences of H2.
The hypotheses express the identifications that must be established
from a concrete action, constraint reduction and PDE well-posedness.

This file does not pretend to prove that an arbitrary covariant
Lagrangian provides a smooth surjective submersion with local product
structure; those are separate H2 analytic hypotheses.
-/

namespace CovariantPhaseSpace

section InitialDataCompatibility

variable {K S I C : Type*} [Field K]
variable [AddCommGroup S] [Module K S]
variable [AddCommGroup I] [Module K I]
variable [AddCommGroup C] [Module K C]

/-- H2 algebraic factorization: compatibility on the unreduced
Ostrogradsky data space implies compatibility on the constraint
subspace, once the initial-data map factors through it and the
constraint form is the restricted canonical form. -/
theorem pullback_compatibility_after_constraint_restriction
    (ΩS : S →ₗ[K] Module.Dual K S)
    (ΩI : I →ₗ[K] Module.Dual K I)
    (ΩC : C →ₗ[K] Module.Dual K C)
    (r0 : S →ₗ[K] I)
    (r : S →ₗ[K] C)
    (j : C →ₗ[K] I)
    (hfactor : ∀ u : S, r0 u = j (r u))
    (hsource : ∀ u v : S, ΩS u v = ΩI (r0 u) (r0 v))
    (hconstraint : ∀ x y : C, ΩC x y = ΩI (j x) (j y)) :
    ∀ u v : S, ΩS u v = ΩC (r u) (r v) := by
  intro u v
  calc
    ΩS u v = ΩI (r0 u) (r0 v) := hsource u v
    _ = ΩI (j (r u)) (j (r v)) := by rw [hfactor u, hfactor v]
    _ = ΩC (r u) (r v) := (hconstraint (r u) (r v)).symm

/-- H2 kernel lemma: for a surjective initial-data differential,
the solution presymplectic kernel is precisely the inverse image
of the constraint presymplectic kernel. No gauge assumptions are used. -/
theorem kernel_of_surjective_presymplectic_pullback
    (ΩS : S →ₗ[K] Module.Dual K S)
    (ΩC : C →ₗ[K] Module.Dual K C)
    (r : S →ₗ[K] C)
    (hr : Function.Surjective r)
    (hpull : ∀ u v : S, ΩS u v = ΩC (r u) (r v)) :
    ∀ u : S,
      (∀ v : S, ΩS u v = 0) ↔
        (∀ w : C, ΩC (r u) w = 0) := by
  intro u
  constructor
  · intro hu w
    obtain ⟨v, hv⟩ := hr w
    rw [← hv]
    exact (hpull u v).symm.trans (hu v)
  · intro hu v
    rw [hpull]
    exact hu (r v)

/-- Every vertical initial-data tangent vector is presymplectically
null, irrespective of how large the vertical kernel is. -/
theorem initial_data_vertical_is_presymplectic_null
    (ΩS : S →ₗ[K] Module.Dual K S)
    (ΩC : C →ₗ[K] Module.Dual K C)
    (r : S →ₗ[K] C)
    (hpull : ∀ u v : S, ΩS u v = ΩC (r u) (r v)) :
    ∀ u : S, r u = 0 → ∀ v : S, ΩS u v = 0 := by
  intro u hu v
  rw [hpull, hu]
  simp

end InitialDataCompatibility

end CovariantPhaseSpace
