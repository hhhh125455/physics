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
  This Lean file uses the algebraic dual only. It does not formalize the
  continuous/admissible dual in H1; in that topological setting the exactness
  condition is independent and requires separate closed-range/extension
  analysis.

Conclusion: the kernel of the restricted form is exactly the image of the
constraint Hamiltonian generators. -/
theorem constraint_kernel_eq
    (ω : V →ₗ[K] V →ₗ[K] K)
    (χ : V →ₗ[K] W)
    (X : (W →ₗ[K] K) →ₗ[K] V)
    (hωInjective : Function.Injective ω)
    (hFirstClass : ∀ μ, χ (X μ) = 0)
    (hHamilton : ∀ μ, ω (X μ) = -(μ.comp χ))
    (hAnnihilatorComplete :
      ∀ α : V →ₗ[K] K,
        (∀ v, χ v = 0 → α v = 0) →
          ∃ μ : W →ₗ[K] K, α = μ.comp χ) :
    ∀ u, IsConstraintKernel ω χ u ↔ ∃ μ, u = X μ := by
  intro u
  constructor
  · rintro ⟨huConstraint, huRadical⟩
    obtain ⟨μ, hfactor⟩ := hAnnihilatorComplete (ω u) (by
      intro v hv
      exact huRadical v hv)
    refine ⟨-μ, ?_⟩
    apply hωInjective
    calc
      ω u = μ.comp χ := hfactor
      _ = ω (X (-μ)) := by
        rw [hHamilton]
        ext v
        simp [LinearMap.comp_apply]
  · rintro ⟨μ, rfl⟩
    refine ⟨hFirstClass μ, ?_⟩
    intro v hv
    rw [hHamilton]
    simp [LinearMap.comp_apply, hv]

end ConstraintKernel

section SolutionConstraintBridge

variable {K S C G M : Type*}
variable [Field K]
variable [AddCommGroup S] [Module K S]
variable [AddCommGroup C] [Module K C]
variable [AddCommGroup G] [Module K G]
variable [AddCommGroup M] [Module K M]

/-- Algebraic data for the induced linearized Cauchy map on gauge
quotients to be well-defined and bijective.

The first field says that spacetime gauge directions map to
constraint-generated initial-data directions. The second and third fields
are, respectively, surjectivity and injectivity of the induced map on
quotients, written without constructing quotient types explicitly. -/
structure LinearizedCauchyQuotientEquiv
    (r : S →ₗ[K] C) (R : G →ₗ[K] S) (X : M →ₗ[K] C) : Prop where
  map_gauge_to_gauge : ∀ ξ, ∃ μ, r (R ξ) = X μ
  quotient_surjective : ∀ c, ∃ s μ, r s = c + X μ
  quotient_injective : ∀ s, (∃ μ, r s = X μ) → ∃ ξ, s = R ξ

/-- Abstract form of the reverse-inclusion argument D3B.

Here S is the tangent space to the actual solution space, C is the tangent
space to the initial-data constraint surface, r is the linearized initial-data
map, R generates spacetime gauge directions, and X generates constraint
directions on C.

The assumptions encode:
* pullback compatibility of the two presymplectic forms;
* surjectivity of the initial-data map;
* the already-established constraint-kernel characterization on C;
* CP: each constraint direction is realized by a spacetime gauge direction;
* PU_tan: every vertical tangent vector of the initial-data map is a
  spacetime gauge tangent vector.

The work note's H4 is stronger: it is a nonlinear, parameterized statement
that every smooth same-initial-data solution curve is related by a smooth
family of diffeomorphisms. Differentiating H4 should imply PU_tan, but this
Lean theorem assumes PU_tan directly; it does not formalize that
infinite-dimensional differentiation step.

This proves the reverse inclusion without assuming the target kernel equality. -/
theorem reverse_kernel_inclusion
    (ωS : S →ₗ[K] S →ₗ[K] K)
    (ωC : C →ₗ[K] C →ₗ[K] K)
    (r : S →ₗ[K] C)
    (R : G →ₗ[K] S)
    (X : M →ₗ[K] C)
    (hPullback : ∀ u v, ωS u v = ωC (r u) (r v))
    (hSurjective : Function.Surjective r)
    (hConstraintKernel :
      ∀ c, (∀ d, ωC c d = 0) → ∃ μ, c = X μ)
    (hCP : ∀ μ, ∃ ξ, r (R ξ) = X μ)
    (hPU : ∀ u, r u = 0 → ∃ η, u = R η) :
    ∀ u, (∀ v, ωS u v = 0) → ∃ ξ, u = R ξ := by
  intro u hu
  have hC : ∀ c, ωC (r u) c = 0 := by
    intro c
    obtain ⟨v, hv⟩ := hSurjective c
    calc
      ωC (r u) c = ωC (r u) (r v) := by rw [← hv]
      _ = ωS u v := (hPullback u v).symm
      _ = 0 := hu v
  obtain ⟨μ, hμ⟩ := hConstraintKernel (r u) hC
  obtain ⟨ξ, hξ⟩ := hCP μ
  have hVertical : r (u - R ξ) = 0 := by
    rw [map_sub, hξ, hμ]
    simp
  obtain ⟨η, hη⟩ := hPU (u - R ξ) hVertical
  refine ⟨ξ + η, ?_⟩
  calc
    u = R ξ + (u - R ξ) := by abel
    _ = R ξ + R η := by rw [hη]
    _ = R (ξ + η) := (map_add R ξ η).symm

/-- Combining D1 with the bridge theorem gives the full kernel equality. -/
theorem full_kernel_eq_from_bridge
    (ωS : S →ₗ[K] S →ₗ[K] K)
    (ωC : C →ₗ[K] C →ₗ[K] K)
    (r : S →ₗ[K] C)
    (R : G →ₗ[K] S)
    (X : M →ₗ[K] C)
    (hD1 : ∀ ξ v, ωS (R ξ) v = 0)
    (hPullback : ∀ u v, ωS u v = ωC (r u) (r v))
    (hSurjective : Function.Surjective r)
    (hConstraintKernel :
      ∀ c, (∀ d, ωC c d = 0) → ∃ μ, c = X μ)
    (hCP : ∀ μ, ∃ ξ, r (R ξ) = X μ)
    (hPU : ∀ u, r u = 0 → ∃ η, u = R η) :
    ∀ u, (∀ v, ωS u v = 0) ↔ ∃ ξ, u = R ξ := by
  intro u
  constructor
  · exact reverse_kernel_inclusion ωS ωC r R X hPullback hSurjective
      hConstraintKernel hCP hPU u
  · rintro ⟨ξ, rfl⟩
    exact hD1 ξ

/-- A quotient-level linearized Cauchy isomorphism, together with CP,
implies the tangent-level surjectivity and PU hypotheses used in D3B.

This is the algebraic passage from a theorem such as Petersen's
Theorem 4.18 (solution space modulo gauge is isomorphic to initial data
modulo gauge-producing data) to the concrete tangent-map hypotheses. -/
theorem full_kernel_eq_from_quotient_cauchy_equiv
    (ωS : S →ₗ[K] S →ₗ[K] K)
    (ωC : C →ₗ[K] C →ₗ[K] K)
    (r : S →ₗ[K] C)
    (R : G →ₗ[K] S)
    (X : M →ₗ[K] C)
    (hD1 : ∀ ξ v, ωS (R ξ) v = 0)
    (hPullback : ∀ u v, ωS u v = ωC (r u) (r v))
    (hQuotient : LinearizedCauchyQuotientEquiv r R X)
    (hCP : ∀ μ, ∃ ξ, r (R ξ) = X μ)
    (hConstraintKernel :
      ∀ c, (∀ d, ωC c d = 0) → ∃ μ, c = X μ) :
    ∀ u, (∀ v, ωS u v = 0) ↔ ∃ ξ, u = R ξ := by
  have hSurjective : Function.Surjective r := by
    intro c
    obtain ⟨s, μ, hsm⟩ := hQuotient.quotient_surjective c
    obtain ⟨ξ, hξ⟩ := hCP μ
    refine ⟨s - R ξ, ?_⟩
    calc
      r (s - R ξ) = r s - r (R ξ) := map_sub r s (R ξ)
      _ = (c + X μ) - X μ := by rw [hsm, hξ]
      _ = c := by abel
  have hPU : ∀ u, r u = 0 → ∃ ξ, u = R ξ := by
    intro u hu
    exact hQuotient.quotient_injective u ⟨0, by simpa using hu⟩
  exact full_kernel_eq_from_bridge ωS ωC r R X hD1 hPullback
    hSurjective hConstraintKernel hCP hPU


end SolutionConstraintBridge

section HigherDerivativeMomentum

variable {K V : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]

/-- Finite-sum form of the higher-derivative Ostrogradsky momentum.
The index r runs backwards from the highest derivative order k. -/
def higherOrderMomentum
    (D : V →ₗ[K] V) (F : ℕ → V) (k j : ℕ) : V :=
  ∑ r ∈ Finset.range (k - j),
    ((-D) ^ (k - j - 1 - r)) (F (k - r))

/-- The finite-sum momentum obeys p_j = F_{j+1} - D p_{j+1}.
This is the algebraic recursion underlying the endpoint momentum formula. -/
theorem higherOrderMomentum_recursion
    (D : V →ₗ[K] V) (F : ℕ → V)
    {k j : ℕ} (hjk : j < k) :
    higherOrderMomentum D F k j =
      F (j + 1) - D (higherOrderMomentum D F k (j + 1)) := by
  let n := k - j
  have hn : 0 < n := by dsimp [n]; omega
  have hnEq : n = (n - 1) + 1 := by omega
  have hnext : k - (j + 1) = n - 1 := by dsimp [n]; omega
  have hlastIndex : k - (n - 1) = j + 1 := by dsimp [n]; omega
  have hsum :
      (∑ r ∈ Finset.range (n - 1),
        ((-D) ^ (n - 1 - r)) (F (k - r))) =
      (-D) (∑ r ∈ Finset.range (n - 1),
        ((-D) ^ (n - 2 - r)) (F (k - r))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < n - 1 := Finset.mem_range.mp hr
    have hexp : n - 1 - r = (n - 2 - r) + 1 := by omega
    rw [hexp, pow_succ']
    rfl
  have hlast :
      ((-D) ^ (n - 1 - (n - 1))) (F (k - (n - 1))) =
        F (j + 1) := by
    simp [hlastIndex]
  unfold higherOrderMomentum
  rw [show k - j = n by rfl, hnEq, Finset.sum_range_succ]
  have hnorm : n - 1 + 1 - 1 = n - 1 := by omega
  rw [hnorm]
  rw [hsum, hnext]
  have hpow : n - 2 = n - 1 - 1 := by omega
  rw [hpow]
  rw [hlast]
  simp [sub_eq_add_neg, add_comm]


/-- Forward-indexed presentation of the same finite-order momentum:
p_j = sum_{s=0}^{k-j-1} (-D)^s F_{j+1+s}. -/
def higherOrderMomentumForward
    (D : V →ₗ[K] V) (F : ℕ → V) (k j : ℕ) : V :=
  ∑ s ∈ Finset.range (k - j),
    ((-D) ^ s) (F (j + 1 + s))

/-- The direct derivative-order sum and the reverse-indexed Ostrogradsky
sum are identical; the proof is the finite-sum reflection r ↦ k-j-1-r. -/
theorem higherOrderMomentum_eq_forward
    (D : V →ₗ[K] V) (F : ℕ → V)
    {k j : ℕ} (hjk : j < k) :
    higherOrderMomentum D F k j =
      higherOrderMomentumForward D F k j := by
  let n := k - j
  have harg : ∀ r, r < n → j + 1 + (n - 1 - r) = k - r := by
    intro r hr
    dsimp [n]
    omega
  unfold higherOrderMomentum higherOrderMomentumForward
  change
    (∑ r ∈ Finset.range n,
      ((-D) ^ (n - 1 - r)) (F (k - r))) =
    ∑ r ∈ Finset.range n, ((-D) ^ r) (F (j + 1 + r)
    )
  calc
    (∑ r ∈ Finset.range n,
      ((-D) ^ (n - 1 - r)) (F (k - r))) =
      ∑ r ∈ Finset.range n,
        ((-D) ^ (n - 1 - r)) (F (j + 1 + (n - 1 - r))) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [harg r (Finset.mem_range.mp hr)]
    _ = ∑ r ∈ Finset.range n, ((-D) ^ r) (F (j + 1 + r)) := by
          rw [← Finset.sum_range_reflect]
          apply Finset.sum_congr rfl
          intro r hr
          have hrlt : r < n := Finset.mem_range.mp hr
          have hreflect : n - 1 - (n - 1 - r) = r := by omega
          rw [hreflect]

end HigherDerivativeMomentum

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
    calc
      ω u' (v - v') = -ω (v - v') u' := hSkew u' (v - v')
      _ = 0 := by rw [hRadV u']; simp
  calc
    ω u v = ω (u' + (u - u')) (v' + (v - v')) := by
      abel_nf
    _ = (ω u' v' + ω u' (v - v')) +
        (ω (u - u') v' + ω (u - u') (v - v')) := by
      simp only [map_add, LinearMap.add_apply]
      ring
    _ = ω u' v' := by
      rw [hzeroRight, hRadU v', hRadU (v - v')]
      ring

/-- Nondegeneracy of the descended pairing, expressed without choosing
coordinates on the quotient: if a class pairs to zero with every quotient
class, then it is the zero class. -/
theorem quotient_pairing_nondegenerate
    (ω : V →ₗ[K] V →ₗ[K] K)
    (π : V →ₗ[K] Q)
    (hSkew : ∀ x y, ω x y = -ω y x)
    (hRadical : ∀ x, π x = 0 ↔ IsRadical ω x)
    (u : V)
    (hPairZero : ∀ q : Q, ∃ v : V, π v = q ∧ ω u v = 0) :
    π u = 0 := by
  apply (hRadical u).2
  intro v
  obtain ⟨w, hw, hω⟩ := hPairZero (π v)
  have hsame : ω u v = ω u w := by
    exact pairing_independent_of_lifts ω π hSkew hRadical rfl hw.symm
  rw [hsame]
  exact hω

/-- A descended bilinear form is unique when the quotient map is
surjective: two forms with the same pullback along π must coincide. -/
theorem quotient_pairing_unique
    (π : V →ₗ[K] Q)
    (hSurjective : Function.Surjective π)
    (ω₁ ω₂ : Q →ₗ[K] Q →ₗ[K] K)
    (hPullback : ∀ u v, ω₁ (π u) (π v) = ω₂ (π u) (π v)) :
    ω₁ = ω₂ := by
  ext q r
  obtain ⟨u, hu⟩ := hSurjective q
  obtain ⟨v, hv⟩ := hSurjective r
  rw [← hu, ← hv]
  exact hPullback u v
end QuotientPairing

section DifferentialFormConsequences

variable {K A A1 B B1 C : Type*}
variable [Field K]
variable [AddCommGroup A] [Module K A]
variable [AddCommGroup A1] [Module K A1]
variable [AddCommGroup B] [Module K B]
variable [AddCommGroup B1] [Module K B1]
variable [AddCommGroup C] [Module K C]

/-- Algebraic consequence of Cartan's formula: a closed horizontal form
is invariant under the corresponding infinitesimal flow. The actual
differential-geometric Cartan formula is a separate geometric input. -/
theorem cartan_invariance_of_horizontal_closed_form
    (d : A →ₗ[K] B)
    (i : A →ₗ[K] C)
    (dNext : C →ₗ[K] A)
    (iNext : B →ₗ[K] A)
    (lie : A →ₗ[K] A)
    (hCartan : ∀ α, lie α = dNext (i α) + iNext (d α))
    (α : A)
    (hHorizontal : i α = 0)
    (hClosed : d α = 0) :
    lie α = 0 := by
  rw [hCartan, hHorizontal, hClosed]
  simp

/-- Closedness descends through an injective pullback map when pullback
commutes with the exterior differential. In geometric applications,
injectivity is supplied by local sections of a surjective submersion. -/
theorem closedness_descends
    (pullback : A →ₗ[K] B)
    (pullbackNext : A1 →ₗ[K] B1)
    (dBase : A →ₗ[K] A1)
    (dTotal : B →ₗ[K] B1)
    (hCommute : ∀ α, pullbackNext (dBase α) = dTotal (pullback α))
    (hPullbackInjective : Function.Injective pullbackNext)
    (formBase : A)
    (formTotal : B)
    (hPullback : pullback formBase = formTotal)
    (hClosed : dTotal formTotal = 0) :
    dBase formBase = 0 := by
  apply hPullbackInjective
  simpa using (calc
    pullbackNext (dBase formBase) = dTotal (pullback formBase) :=
      hCommute formBase
    _ = dTotal formTotal := by rw [hPullback]
    _ = 0 := hClosed)

end DifferentialFormConsequences

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

section TwoDimensionalSphereCounterexample

/-- The original work note's scalar curvature 2/a² on R × S² is
injective in the positive scale factor. -/
theorem two_sphere_scalar_curvature_injective
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hR : 2 / a ^ 2 = 2 / b ^ 2) :
    a = b := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hsquare : a ^ 2 = b ^ 2 := by
    have h := hR
    field_simp [ha0, hb0] at h
    nlinarith
  nlinarith [sq_nonneg (a - b)]

end TwoDimensionalSphereCounterexample

section GaugeInvariantObservable

variable {K V G : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup G] [Module K G]

/-- An invariant linearized observable separates a tangent direction
from all gauge directions whenever its variation is nonzero. -/
theorem invariant_observable_excludes_gauge
    (I : V →ₗ[K] K)
    (R : G →ₗ[K] V)
    (hGauge : ∀ ξ, I (R ξ) = 0)
    (u : V)
    (hObservable : I u ≠ 0) :
    ¬ ∃ ξ, u = R ξ := by
  rintro ⟨ξ, hξ⟩
  apply hObservable
  calc
    I u = I (R ξ) := by rw [hξ]
    _ = 0 := hGauge ξ

end GaugeInvariantObservable

end CovariantPhaseSpaceAudit
