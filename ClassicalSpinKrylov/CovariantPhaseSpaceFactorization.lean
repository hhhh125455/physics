import Mathlib
import ClassicalSpinKrylov.CovariantPhaseSpaceAudit

/-!
# D2: annihilator factorization from a surjective linearized constraint map

This is the algebraic-dual version of the continuous-dual factorization used
for a regular constraint submanifold. In a Banach/Hilbert GR application,
surjectivity and the split/closed-range hypotheses must be established in the
chosen Sobolev spaces; those analytic facts are not formalized here.
-/

namespace CovariantPhaseSpaceAudit

section AnnihilatorFactorization

variable {K V W : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- A linear functional that vanishes on ker χ factors through χ when χ is
surjective. This is the algebraic-dual annihilator identity. -/
theorem linearFunctional_factors_through_surjective
    (χ : V →ₗ[K] W)
    (hχ : Function.Surjective χ)
    (α : Module.Dual K V)
    (hα : ∀ v : V, χ v = 0 → α v = 0) :
    ∃ β : Module.Dual K W, β.comp χ = α := by
  classical
  let β : W →ₗ[K] K :=
    { toFun := fun w => α (Classical.choose (hχ w))
      map_add' := by
        intro x y
        let vx := Classical.choose (hχ x)
        let vy := Classical.choose (hχ y)
        let vxy := Classical.choose (hχ (x + y))
        have hx : χ vx = x := Classical.choose_spec (hχ x)
        have hy : χ vy = y := Classical.choose_spec (hχ y)
        have hxy : χ vxy = x + y := Classical.choose_spec (hχ (x + y))
        have hker : χ (vx + vy - vxy) = 0 := by
          simp [map_add, map_sub, hx, hy, hxy]
        have hz := hα (vx + vy - vxy) hker
        have hz' : α vx + α vy - α vxy = 0 := by
          simpa [map_add, map_sub] using hz
        change α vxy = α vx + α vy
        exact (sub_eq_zero.mp hz').symm
      map_smul' := by
        intro c x
        let vx := Classical.choose (hχ x)
        let vcx := Classical.choose (hχ (c • x))
        have hx : χ vx = x := Classical.choose_spec (hχ x)
        have hcx : χ vcx = c • x := Classical.choose_spec (hχ (c • x))
        have hker : χ (c • vx - vcx) = 0 := by
          simp [map_sub, map_smul, hx, hcx]
        have hz := hα (c • vx - vcx) hker
        have hz' : c • α vx - α vcx = 0 := by
          simpa [map_sub, map_smul] using hz
        change α vcx = c • α vx
        exact (sub_eq_zero.mp hz').symm }
  refine ⟨β, ?_⟩
  ext v
  dsimp [β]
  let v' := Classical.choose (hχ (χ v))
  have hv' : χ v' = χ v := Classical.choose_spec (hχ (χ v))
  have hker : χ (v' - v) = 0 := by
    simp [map_sub, hv']
  have hz := hα (v' - v) hker
  have hz' : α v' - α v = 0 := by
    simpa [map_sub] using hz
  exact sub_eq_zero.mp hz'

/-- D2 with the annihilator-completeness condition derived from surjectivity
of the linearized constraint map. Multipliers are continuous/algebraic
functionals on the constraint-value space (algebraically in this theorem). -/
theorem constraint_kernel_eq_of_surjective
    (ω : V →ₗ[K] Module.Dual K V)
    (χ : V →ₗ[K] W)
    (X : Module.Dual K W →ₗ[K] V)
    (hωInjective : Function.Injective ω)
    (hχSurjective : Function.Surjective χ)
    (hFirstClass : ∀ μ : Module.Dual K W, χ (X μ) = 0)
    (hHamilton : ∀ μ : Module.Dual K W, ω (X μ) = -(μ.comp χ)) :
    ∀ v : V,
      (χ v = 0 ∧ ∀ w : V, χ w = 0 → ω v w = 0) ↔
        ∃ μ : Module.Dual K W, X μ = v := by
  intro v
  constructor
  · rintro ⟨hvTangent, hvAnnihilates⟩
    obtain ⟨μ, hfactor⟩ :=
      linearFunctional_factors_through_surjective χ hχSurjective
        (ω v) hvAnnihilates
    have hsum : ω (v + X μ) = 0 := by
      apply LinearMap.ext
      intro w
      simp only [map_add, LinearMap.add_apply]
      rw [hfactor.symm, hHamilton μ]
      simp
    have hzero : v + X μ = 0 := by
      apply hωInjective
      simpa using hsum
    have hvneg : v = -X μ := by
      calc
        v = (v + X μ) - X μ := by simp
        _ = 0 - X μ := by rw [hzero]
        _ = -X μ := by simp
    refine ⟨-μ, ?_⟩
    change X (-μ) = v
    rw [map_neg]
    exact hvneg.symm
  · rintro ⟨μ, rfl⟩
    constructor
    · exact hFirstClass μ
    · intro w hw
      rw [hHamilton μ]
      simp [LinearMap.comp_apply, hw]

end AnnihilatorFactorization

end CovariantPhaseSpaceAudit
