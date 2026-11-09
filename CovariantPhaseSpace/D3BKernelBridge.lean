import Mathlib

/-!
# D3B: the non-circular algebraic bridge from Cauchy data to gauge degeneracy

This theorem is the linear tangent-space skeleton of work-note D3B.
Its assumptions mirror H2 (surjective initial-data map and symplectic
pullback), D2 (constraint kernel), H3 (CP), H4 (PU at the tangent level),
and D1 (gauge inclusion).  It does NOT establish these hypotheses
for a nonlinear PDE, nor identify arbitrary gauge parameters with
spacetime vector fields.
-/

namespace CovariantPhaseSpace

section KernelBridge

variable {K V C Γ Λ : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup C] [Module K C]
variable [AddCommGroup Γ] [Module K Γ]
variable [AddCommGroup Λ] [Module K Λ]

/-- D3B: a presymplectic null direction is gauge if the full constrained
initial-data kernel is generated, the Cauchy map is a surjective
symplectic pullback, constraint generators lift to gauge directions
(CP), and vertical Cauchy variations are gauge (differentiated PU).
D1 supplies the converse inclusion. -/
theorem presymplectic_kernel_eq_gauge_range
    (ΩS : V →ₗ[K] Module.Dual K V)
    (ΩC : C →ₗ[K] Module.Dual K C)
    (r : V →ₗ[K] C)
    (R : Γ →ₗ[K] V)
    (X : Λ →ₗ[K] C)
    (hr : Function.Surjective r)
    (hpull : ∀ u v : V, ΩS u v = ΩC (r u) (r v))
    (hCker : ∀ w : C,
      (∀ t : C, ΩC w t = 0) ↔ ∃ lam : Λ, X lam = w)
    (hCP : ∀ lam : Λ, ∃ gamma : Γ, r (R gamma) = X lam)
    (hPU : ∀ u : V, r u = 0 → ∃ gamma : Γ, R gamma = u)
    (hD1 : ∀ gamma : Γ, ∀ v : V, ΩS (R gamma) v = 0) :
    ∀ u : V, (∀ v : V, ΩS u v = 0) ↔
      ∃ gamma : Γ, R gamma = u := by
  intro u
  constructor
  · intro hu
    have hCu : ∀ w : C, ΩC (r u) w = 0 := by
      intro w
      obtain ⟨v, rfl⟩ := hr w
      calc
        ΩC (r u) (r v) = ΩS u v := (hpull u v).symm
        _ = 0 := hu v
    obtain ⟨lam, hlam⟩ := (hCker (r u)).mp hCu
    obtain ⟨gamma, hgamma⟩ := hCP lam
    have hz : r (u - R gamma) = 0 := by
      rw [map_sub, hgamma, hlam]
      simp
    obtain ⟨eta, heta⟩ := hPU (u - R gamma) hz
    refine ⟨gamma + eta, ?_⟩
    rw [map_add, heta]
    abel
  · rintro ⟨gamma, rfl⟩
    exact hD1 gamma

end KernelBridge

end CovariantPhaseSpace
