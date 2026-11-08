import Mathlib

/-!
# Constraint-kernel theorem for covariant phase space

This file formalizes the algebraic core of D2 in the work note.

It does NOT formalize the analytic hypotheses (closed range, admissible
annihilator completeness, PDE well-posedness, or the construction of the
constraint map). Those remain explicit assumptions and require separate
functional-analytic / physical justification.
-/

namespace CovariantPhaseSpace

section ConstraintKernel

variable {K V Λ : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup Λ] [Module K Λ]

/-- The conormal covector associated with a constraint differential. -/
def conormal
    (dχ : V →ₗ[K] Module.Dual K Λ) :
    Λ →ₗ[K] Module.Dual K V where
  toFun λ :=
    { toFun := fun v => dχ v λ
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  map_add' := by
    intro λ μ
    ext v
    simp
  map_smul' := by
    intro c λ
    ext v
    simp

/--
D2 (abstract constraint-kernel theorem).

Assumptions:
* `ω` is injective as the flat map;
* `X λ` is tangent to the constraint surface (first-class condition);
* `ω(X λ) = -dχ_λ` (Hamiltonian sign convention);
* every admissible covector annihilating the constraint tangent space is a
  conormal covector (the annihilator-completeness hypothesis).

Conclusion: the kernel of the pulled-back two-form on the constraint tangent
space is exactly the range of the constraint Hamiltonian generators.

The theorem is algebraic once the four displayed hypotheses are supplied.
-/
theorem constraint_kernel_eq_generator_range
    (ω : V →ₗ[K] Module.Dual K V)
    (dχ : V →ₗ[K] Module.Dual K Λ)
    (X : Λ →ₗ[K] V)
    (hω_injective : Function.Injective ω)
    (h_first_class : ∀ λ : Λ, dχ (X λ) = 0)
    (h_hamiltonian : ∀ λ : Λ, ω (X λ) = - conormal dχ λ)
    (h_annihilator_complete :
      ∀ v : V,
        (∀ w : V, dχ w = 0 → ω v w = 0) →
          ∃ λ : Λ, ω v = conormal dχ λ) :
    ∀ v : V,
      (dχ v = 0 ∧ ∀ w : V, dχ w = 0 → ω v w = 0) ↔
        ∃ λ : Λ, X λ = v := by
  intro v
  constructor
  · rintro ⟨hv_tangent, hv_annihilates⟩
    obtain ⟨λ, hλ⟩ := h_annihilator_complete v hv_annihilates
    have hsum : ω (v + X λ) = 0 := by
      ext w
      change ω v w + ω (X λ) w = 0
      rw [hλ, h_hamiltonian λ]
      simp
    have hzero : v + X λ = 0 :=
      hω_injective (v + X λ) 0 (by simpa using hsum)
    have hvneg : v = - X λ := by
      simpa using congrArg (fun z : V => z - X λ) hzero
    refine ⟨-λ, ?_⟩
    change X (-λ) = v
    rw [map_neg]
    exact hvneg.symm
  · rintro ⟨λ, rfl⟩
    constructor
    · exact h_first_class λ
    · intro w hw_tangent
      have h := congrArg (fun f : Module.Dual K V => f w)
        (h_hamiltonian λ)
      simpa [conormal, hw_tangent] using h

end ConstraintKernel

end CovariantPhaseSpace
