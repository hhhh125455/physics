import Mathlib

/-!
# Formal audit of the presymplectic reduction argument

This file formalizes only the algebraic parts of the argument in work-note.pdf.
It does NOT formalize the infinite-dimensional PDE hypotheses, spacetime
diffeomorphism geometry, the ADM constraint algebra, or the existence of a
smooth quotient. Those require separate analytic/geometric proofs and
literature verification.

The sign convention is i_{X_f} Ω = - d f.
-/

namespace CovariantPhaseSpaceAudit

section ConstraintKernel

variable {K V W : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- A vector is in the kernel of the presymplectic form restricted to
the linear constraint surface ker(χ). -/
def IsConstraintKernel
    (ω : V →ₗ[K] V →ₗ[K] K)
    (χ : V →ₗ[K] W) (u : V) : Prop :=
  χ u = 0 ∧ ∀ v, χ v = 0 → ω u v = 0

/-- Abstract constraint-kernel theorem.

Assumptions:
* hωInjective: the ambient bilinear form has injective flat map;
* hFirstClass: constraint Hamiltonian vectors are tangent to ker χ;
* hHamilton: the Hamiltonian-vector sign convention is
  Ω(X_λ, ·) = - λ ∘ χ;
* hAnnihilatorComplete: every covector annihilating ker χ factors through χ.
  In infinite dimensions this is an independent topological hypothesis,
  not a consequence of first-classness alone.

Conclusion: the kernel of the restricted form is exactly the image of the
constraint Hamiltonian generators. -/
theorem constraint_kernel_eq
    (ω : V →ₗ[K] V →ₗ[K] K)
    (χ : V →ₗ[K] W)
    (X : (W →ₗ[K] K) →ₗ[K] V)
    (hωInjective : Function.Injective ω)
    (hFirstClass : ∀ λ, χ (X λ) = 0)
    (hHamilton : ∀ λ, ω (X λ) = -(λ.comp χ))
    (hAnnihilatorComplete :
      ∀ α : V →ₗ[K] K,
        (∀ v, χ v = 0 → α v = 0) →
          ∃ λ : W →ₗ[K] K, α = λ.comp χ) :
    ∀ u, IsConstraintKernel ω χ u ↔ ∃ λ, u = X λ := by
  intro u
  constructor
  · rintro ⟨huConstraint, huRadical⟩
    obtain ⟨λ, hλ⟩ := hAnnihilatorComplete (ω u) (by
      intro v hv
      exact huRadical v hv)
    refine ⟨-λ, ?_⟩
    apply hωInjective
    calc
      ω u = λ.comp χ := hλ
      _ = ω (X (-λ)) := by
        rw [hHamilton]
        ext v
        simp [LinearMap.comp_apply]
  · rintro ⟨λ, rfl⟩
    refine ⟨hFirstClass λ, ?_⟩
    intro v hv
    rw [hHamilton]
    simp [LinearMap.comp_apply, hv]

end ConstraintKernel

section QuotientPairing

variable {K V Q : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup Q] [Module K Q]

/-- The left radical of a bilinear form. -/
def IsRadical
    (ω : V →ₗ[K] V →ₗ[K] K) (u : V) : Prop :=
  ∀ v, ω u v = 0

/-- If the kernel of a quotient map is exactly the radical,
then the pairing is independent of the chosen lifts of both quotient
arguments. Skew-symmetry controls a change in the second lift. -/
theorem pairing_independent_of_lifts
    (ω : V →ₗ[K] V →ₗ[K] K)
    (π : V →ₗ[K] Q)
    (hSkew : ∀ x y, ω x y = -ω y x)
    (hRadical : ∀ x, π x = 0 ↔ IsRadical ω x)
    {u u' v v' : V}
    (hu : π u = π u')
    (hv : π v = π v') :
    ω u v = ω u' v' := by
  have hdu : π (u - u') = 0 := by
    rw [map_sub, hu]
    simp
  have hdv : π (v - v') = 0 := by
    rw [map_sub, hv]
    simp
  have hRadU := (hRadical (u - u')).mp hdu
  have hRadV := (hRadical (v - v')).mp hdv
  have hzeroRight : ω u' (v - v') = 0 := by
    rw [hSkew]
    simp [hRadV]
  calc
    ω u v = ω (u' + (u - u')) (v' + (v - v')) := by
      congr 1 <;> abel
    _ = (ω u' v' + ω u' (v - v')) +
        (ω (u - u') v' + ω (u - u') (v - v')) := by
      simp only [map_add, LinearMap.add_apply]
      ring
    _ = ω u' v' := by
      simp [hzeroRight, hRadU]

/-- Nondegeneracy of the descended pairing, expressed without choosing
coordinates on the quotient: if a class pairs to zero with every quotient
class, then it is the zero class. -/
theorem quotient_pairing_nondegenerate
    (ω : V →ₗ[K] V →ₗ[K] K)
    (π : V →ₗ[K] Q)
    (hSurjective : Function.Surjective π)
    (hRadical : ∀ x, π x = 0 ↔ IsRadical ω x)
    (u : V)
    (hPairZero :
      ∀ q : Q, ∀ v : V, π v = q → ω u v = 0) :
    π u = 0 := by
  apply (hRadical u).2
  intro v
  obtain ⟨w, hw⟩ := hSurjective (π v)
  exact hPairZero (π v) w hw

end QuotientPairing

section FourDimensionalSphereCounterexample

/-- The scalar curvature 6/a² of the product metric
-dt² + a² h_{S³} distinguishes different positive scale factors. -/
theorem sphere_scalar_curvature_injective
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hR : 6 / a ^ 2 = 6 / b ^ 2) :
    a = b := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hsquare : a ^ 2 = b ^ 2 := by
    have h := hR
    field_simp [ha0, hb0] at h
    nlinarith
  nlinarith [sq_nonneg (a - b)]

end FourDimensionalSphereCounterexample

end CovariantPhaseSpaceAudit
