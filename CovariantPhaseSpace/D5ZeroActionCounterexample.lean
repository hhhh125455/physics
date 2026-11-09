import Mathlib

/-!
# D5: algebraic mechanism of an additional degeneracy

The work note chooses L = 0 and metrics g_a = -dt² + a² h on
R × S², with scalar curvature R[g_a] = 2/a².

This file proves an abstract obstruction: if a gauge-invariant
linearized observable changes along a tangent vector, then that vector
is not a gauge variation; for the zero presymplectic form it is
nevertheless a null direction.

It also checks the scalar-curvature values at a=1, a=2.
It does NOT formalize differential geometry or prove R[g_a]=2/a²
from Christoffel symbols; that remains a geometry/reference obligation.
-/

namespace CovariantPhaseSpace

section ExtraNullDirections

variable {K V Γ : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup Γ] [Module K Γ]

/-- D5: an invariant-changing variation cannot be a gauge direction,
though it is null for the identically zero presymplectic form. -/
theorem zero_action_extra_null_direction
    (R : Γ →ₗ[K] V)
    (I : V →ₗ[K] K)
    (h_gauge_invariant : ∀ gamma : Γ, I (R gamma) = 0)
    (u : V)
    (h_changes_invariant : I u ≠ 0) :
    (∀ v : V, (0 : V →ₗ[K] Module.Dual K V) u v = 0) ∧
      ¬ ∃ gamma : Γ, R gamma = u := by
  constructor
  · intro v
    rfl
  · rintro ⟨gamma, hg⟩
    have hi : I u = 0 := by
      rw [← hg]
      exact h_gauge_invariant gamma
    exact h_changes_invariant hi

/-- Exact curvature values of the two metrics in the note, once
the independently established geometric formula R[g_a]=2/a² is used. -/
theorem product_sphere_curvature_values :
    (2 : ℝ) / (1 : ℝ)^2 = 2 ∧
    (2 : ℝ) / (2 : ℝ)^2 = 1/2 := by
  constructor <;> norm_num

theorem product_sphere_curvature_values_differ :
    (2 : ℝ) / (1 : ℝ)^2 ≠ (2 : ℝ) / (2 : ℝ)^2 := by
  norm_num

/-- The algebraic value of the claimed derivative -4/a³ is nonzero
for every positive radius; this does not formalize the derivative rule. -/
theorem curvature_parameter_variation_nonzero (a : ℝ) (ha : 0 < a) :
    -(4 : ℝ) / a ^ 3 ≠ 0 := by
  apply div_ne_zero
  · norm_num
  · exact pow_ne_zero _ (ne_of_gt ha)

end ExtraNullDirections

end CovariantPhaseSpace
