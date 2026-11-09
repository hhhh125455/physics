import CovariantPhaseSpace.ConstraintKernel

/-!
# H1 / D2: admissible conormal pairing audit

This file does not identify "admissible covectors" with all algebraic
covectors. The admissible subspace is represented by a submodule of the
algebraic dual, and membership of Ω♭(v) is an explicit hypothesis.

The functional-analytic validity of that submodule and of the conormal
surjectivity hypothesis is NOT obtained from this Lean theorem.
-/

namespace CovariantPhaseSpace

section AdmissibleConstraintKernel

variable {K V Λ : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup Λ] [Module K Λ]

/-- Algebraic D2, with the missing domain qualification stated explicitly:
the flat image belongs to the admissible covectors, and any admissible
covector annihilating the constraint tangent space is a conormal.
No implicit identification of the admissible and full dual is made. -/
theorem constraint_kernel_with_admissible_dual
    (ω : V →ₗ[K] Module.Dual K V)
    (dχ : V →ₗ[K] Module.Dual K Λ)
    (X : Λ →ₗ[K] V)
    (Adm : Submodule K (Module.Dual K V))
    (hω_injective : Function.Injective ω)
    (hω_admissible : ∀ v : V, ω v ∈ Adm)
    (h_first_class : ∀ lam : Λ, dχ (X lam) = 0)
    (h_hamiltonian : ∀ lam : Λ, ω (X lam) = -conormal dχ lam)
    (h_admissible_conormal_complete :
       ∀ α : Module.Dual K V, α ∈ Adm →
         (∀ w : V, dχ w = 0 → α w = 0) →
           ∃ lam : Λ, α = conormal dχ lam) :
    ∀ v : V,
      (dχ v = 0 ∧ ∀ w : V, dχ w = 0 → ω v w = 0) ↔
        ∃ lam : Λ, X lam = v := by
  apply constraint_kernel_eq_generator_range ω dχ X
    hω_injective h_first_class h_hamiltonian
  intro v hvanish
  exact h_admissible_conormal_complete
    (ω v) (hω_admissible v) hvanish

end AdmissibleConstraintKernel

end CovariantPhaseSpace
