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
  toFun lam :=
    { toFun := fun v => dχ v lam
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  map_add' := by
    intro lam μ
    ext v
    simp
  map_smul' := by
    intro c lam
    ext v
    simp

/--
D2 (abstract constraint-kernel theorem).

Assumptions:
* `ω` is injective as the flat map;
* `X lam` is tangent to the constraint surface (first-class condition);
* `ω(X lam) = -dχ_lam` (Hamiltonian sign convention);
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
    (h_first_class : ∀ lam : Λ, dχ (X lam) = 0)
    (h_hamiltonian : ∀ lam : Λ, ω (X lam) = - conormal dχ lam)
    (h_annihilator_complete :
      ∀ v : V,
        (∀ w : V, dχ w = 0 → ω v w = 0) →
          ∃ lam : Λ, ω v = conormal dχ lam) :
    ∀ v : V,
      (dχ v = 0 ∧ ∀ w : V, dχ w = 0 → ω v w = 0) ↔
        ∃ lam : Λ, X lam = v := by
  intro v
  constructor
  · rintro ⟨hv_tangent, hv_annihilates⟩
    obtain ⟨lam, hlam⟩ := h_annihilator_complete v hv_annihilates
    have hsum : ω (v + X lam) = 0 := by
      rw [map_add, hlam, h_hamiltonian lam]
      simp
    have hzero : v + X lam = 0 :=
      hω_injective (by simpa using hsum)
    have hvneg : v = - X lam := by
      calc
        v = (v + X lam) - X lam := by simp
        _ = 0 - X lam := by rw [hzero]
        _ = - X lam := by simp
    refine ⟨-lam, ?_⟩
    change X (-lam) = v
    rw [map_neg]
    exact hvneg.symm
  · rintro ⟨lam, rfl⟩
    constructor
    · exact h_first_class lam
    · intro w hw_tangent
      rw [h_hamiltonian lam]
      simp [conormal, hw_tangent]

end ConstraintKernel

end CovariantPhaseSpace
