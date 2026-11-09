import Mathlib

/-!
# D4: pointwise presymplectic descent to the linearized reduced space

This formalizes only the tangent-space part of D4:
independence from choices of lifts and weak nondegeneracy.
It does not establish a smooth global quotient, closedness, or
existence of the descended smooth 2-form. Those require H5.
-/

namespace CovariantPhaseSpace

section ReducedPairing

variable {K V P : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup P] [Module K P]

/-- Independence from tangent lifts, assuming that vertical
directions are exactly presymplectic null vectors and Ω is skew. -/
theorem pairing_independent_of_lifts
    (ΩS : V →ₗ[K] Module.Dual K V)
    (π : V →ₗ[K] P)
    (hvertical : ∀ w : V, π w = 0 → ∀ z : V, ΩS w z = 0)
    (hskew : ∀ x y : V, ΩS x y = -(ΩS y x))
    (u u' v v' : V)
    (hu : π u = π u') (hv : π v = π v') :
    ΩS u v = ΩS u' v' := by
  have hdu : π (u - u') = 0 := by
    rw [map_sub, hu]
    simp
  have hdv : π (v - v') = 0 := by
    rw [map_sub, hv]
    simp
  have hleft : ΩS u v = ΩS u' v := by
    have h : ΩS (u - u') v = 0 := hvertical _ hdu _
    have hdiff : ΩS u v - ΩS u' v = 0 := by
      simpa using h
    exact sub_eq_zero.mp hdiff
  have hright : ΩS u' v = ΩS u' v' := by
    have h : ΩS (v - v') u' = 0 := hvertical _ hdv _
    have hswap : ΩS u' (v - v') = 0 := by
      calc
        ΩS u' (v - v') = -(ΩS (v - v') u') := hskew _ _
        _ = 0 := by rw [h]; simp
    have hdiff : ΩS u' v - ΩS u' v' = 0 := by
      simpa using hswap
    exact sub_eq_zero.mp hdiff
  exact hleft.trans hright

/-- If a descended two-form exists and pulls back to the
presymplectic form, the kernel equality and surjective projection
imply weak nondegeneracy on the quotient tangent space. -/
theorem descended_pairing_weakly_nondegenerate
    (ΩS : V →ₗ[K] Module.Dual K V)
    (Ωphys : P →ₗ[K] Module.Dual K P)
    (π : V →ₗ[K] P)
    (hπ : Function.Surjective π)
    (hpull : ∀ u v : V, ΩS u v = Ωphys (π u) (π v))
    (hker : ∀ u : V, (∀ v : V, ΩS u v = 0) → π u = 0) :
    ∀ x : P, (∀ y : P, Ωphys x y = 0) → x = 0 := by
  intro x hx
  obtain ⟨u, rfl⟩ := hπ x
  apply hker u
  intro v
  rw [hpull]
  exact hx (π v)

end ReducedPairing

end CovariantPhaseSpace
