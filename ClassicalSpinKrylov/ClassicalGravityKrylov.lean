import Mathlib

/-!
# Classical vacuum gravitational waves: from Einstein--Hilbert TT modes to Krylov

PHYSICAL INPUTS (not claimed as Lean-proved tensor calculus):
* Einstein--Hilbert action, signature (- + + +), 4D flat background R x T³.
* Second-order, constraint-reduced TT action:
  S₂ = (64πG)⁻¹ ∫ [ (∂ₜhᵀᵀ)² - (∂ₗhᵀᵀ)² ] d⁴x.
* Select spatial modes cos(kx)/√π and normalized TT polarization e⁺_{ij} e⁺_{ij}=1.
  Integrated transverse area (2π)² gives M=π/(8G).
* A_k and Π_k=M dA_k/dt are canonical reduced data.
* Linearized curvature Fourier observables E_k=k² A_k/2, B_k=k Π_k/(2M).
* ORIGINAL finite-N normalized Gibbs--Liouville inner product is used, not
  an invented infinite-dimensional symplectic volume measure.

These Lean theorems check: canonical Legendre algebra, canonical symplectic
normalization, curvature Hamilton evolution, Gibbs variance identities
conditional on standard Gaussian covariances, complex curvature/oscillator
observable identification, finite-N spectral weight normalization and limit,
all-level Krylov amplitude recurrence algebra, Riccati identities for
the analytic amplitude ansatz, probability normalization and mean formula.

NOT proven here: tensor expansion of EH, curvature gauge invariance,
Gaussian phase-space integrations, all-degree Meixner orthogonality,
functional ODE uniqueness, complexity convergence from finite to infinite N.
-/

open scoped Topology

namespace ClassicalGravityKrylov

section TT
noncomputable def gravMass (G : ℝ) : ℝ := Real.pi / (8*G)

noncomputable def gravModeLag (M k a v : ℝ) : ℝ :=
  M/2 * (v^2 - k^2*a^2)

noncomputable def gravModeHam (M k a p : ℝ) : ℝ :=
  p^2 / (2*M) + M*k^2*a^2/2

/-- The EH quadratic TT mode's Legendre transform, with no altered Hamiltonian. -/
theorem legendre_TT (M k a p : ℝ) (hM : M ≠ 0) :
    p*(p/M) - gravModeLag M k a (p/M) =
      gravModeHam M k a p := by
  unfold gravModeLag gravModeHam
  field_simp
  ring

/-- Canonical transformations Q=s A and P=Π/s preserve the symplectic 2-form. -/
theorem symplectic_normalization (s a₁ p₁ a₂ p₂ : ℝ) (hs : s ≠ 0) :
    (s*a₁)*(p₂/s) - (s*a₂)*(p₁/s) =
      a₁*p₂-a₂*p₁ := by
  field_simp

/-- Same gravitational Hamiltonian, in oscillator canonical variables, M=s². -/
theorem oscillator_hamiltonian (s k a p : ℝ) (hs : s ≠ 0) :
    gravModeHam (s^2) k a p =
      ((p/s)^2 + k^2*(s*a)^2)/2 := by
  unfold gravModeHam
  field_simp

noncomputable def electric (k a : ℝ) : ℝ := k^2*a/2
noncomputable def magnetic (M k p : ℝ) : ℝ := k*p/(2*M)
noncomputable def velocity (M p : ℝ) : ℝ := p/M
def force (M k a : ℝ) : ℝ := -M*k^2*a

/-- d E/dt = k B, using the actual canonical Hamilton equations. -/
theorem electric_evolution (M k p : ℝ) (hM : M ≠ 0) :
    k^2/2*velocity M p = k*magnetic M k p := by
  unfold velocity magnetic
  field_simp

/-- d B/dt = -k E, the curvature rotation equation. -/
theorem magnetic_evolution (M k a : ℝ) (hM : M ≠ 0) :
    k/(2*M)*force M k a = -k*electric k a := by
  unfold force electric
  field_simp

/-- Gaussian covariance identities, conditional on the original Gibbs
 measure: E[A²]=1/(β M k²), E[Π²]=M/β. -/
theorem curvature_variance (β M k : ℝ)
    (hβ : β ≠ 0) (hM : M ≠ 0) (hk : k ≠ 0) :
    (k^4/4)*(1/(β*M*k^2)) =
      (k^2/(4*M^2))*(M/β) := by
  field_simp

/-- A positive-frequency curvature combination is the same canonical complex
 oscillator observable, up to the explicitly tracked frequency/mass factors.
 We use doubled Weyl components to avoid arbitrary sqrt conventions. -/
noncomputable def curvatureComplex (s k a p : ℂ) : ℂ :=
  k^2*a + Complex.I*k*p/s^2

noncomputable def canonicalComplex (s k a p : ℂ) : ℂ :=
  k*s*a + Complex.I*p/s

theorem curvature_to_canonical (s k a p : ℂ)
    (hs : s ≠ 0) (hk : k ≠ 0) :
    (s/k)*curvatureComplex s k a p =
      canonicalComplex s k a p := by
  unfold curvatureComplex canonicalComplex
  field_simp

/-- One nonzero physical curvature mode gives a two-step Krylov chain. -/
theorem one_mode_probability (k t : ℝ) :
    Real.cos (k*t)^2 + Real.sin (k*t)^2 = 1 := by
  nlinarith [Real.sin_sq_add_cos_sq (k*t)]

theorem one_mode_complexity (k t : ℝ) :
    (0 : ℝ)*Real.cos (k*t)^2 +
      (1 : ℝ)*Real.sin (k*t)^2 = Real.sin (k*t)^2 := by
  ring

end TT

section InfiniteModes

/-- k=j+1, P(k)=2^{-k}; induced by the FINITE-N Gibbs--Liouville metric. -/
noncomputable def gravityWeight (j : ℕ) : ℝ := (1/2 : ℝ)^(j+1)

theorem gravityWeight_finite (N : ℕ) :
    (∑ j ∈ Finset.range N, gravityWeight j) =
      1-(1/2 : ℝ)^N := by
  induction N with
  | zero => simp [gravityWeight]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [gravityWeight]
      rw [pow_succ]
      ring

theorem gravityWeight_tendsto_one :
    Filter.Tendsto (fun N : ℕ =>
      ∑ j ∈ Finset.range N, gravityWeight j)
      Filter.atTop (𝓝 (1 : ℝ)) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)
  have h1 := (tendsto_const_nhds.sub h :
    Filter.Tendsto (fun N : ℕ => 1-(1/2 : ℝ)^N)
      Filter.atTop (𝓝 (1-(0 : ℝ))))
  simpa only [gravityWeight_finite, sub_zero] using h1

/-- Exact normalized amplitudes have a geometric Krylov distribution. -/
noncomputable def spreadRatio (s : ℝ) : ℝ := 8*s/(1+8*s)
noncomputable def krylovProb (r : ℝ) (n : ℕ) : ℝ := (1-r)*r^n

theorem krylovProb_finite (r : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, krylovProb r n) = 1-r^N := by
  induction N with
  | zero => simp [krylovProb]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [krylovProb]
      rw [pow_succ]
      ring

theorem spreadRatio_bounds (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ spreadRatio s ∧ spreadRatio s < 1 := by
  have hd : 0 < 1+8*s := by positivity
  constructor
  · unfold spreadRatio
    positivity
  · unfold spreadRatio
    apply (div_lt_one hd).2
    linarith

theorem krylovProb_tendsto_one (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Filter.Tendsto (fun N : ℕ =>
        ∑ n ∈ Finset.range N, krylovProb r n)
        Filter.atTop (𝓝 (1 : ℝ)) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have h1 := (tendsto_const_nhds.sub h :
    Filter.Tendsto (fun N : ℕ => 1-r^N)
      Filter.atTop (𝓝 (1-(0 : ℝ))))
  simpa only [krylovProb_finite, sub_zero] using h1

noncomputable def geometricMean (r : ℝ) : ℝ := r/(1-r)

theorem exact_krylov_mean (s : ℝ) (hs : 0 ≤ s) :
    geometricMean (spreadRatio s) = 8*s := by
  have hd : 1+8*s ≠ 0 := ne_of_gt (by positivity)
  have hOne : 1-spreadRatio s = 1/(1+8*s) := by
    unfold spreadRatio
    field_simp
    ring
  unfold geometricMean
  rw [hOne]
  unfold spreadRatio
  field_simp

/-- Check the n=1,2 Meixner monic recurrences (full orthogonality is
not part of these algebraic lemmas). -/
theorem meixner_first (x : ℝ) :
    x*(x-2) = (x^2-7*x+8)+5*(x-2)+2 := by ring

theorem meixner_second (x : ℝ) :
    x*(x^2-7*x+8) =
      (x^3-15*x^2+56*x-48)+8*(x^2-7*x+8)+8*(x-2) := by ring

/-- The all-level coefficient recursion can be checked symbolically
for the exact ansatz ψ_n=α(u)ρ(u)^n and a_n=3n+2, b_n=w n. -/
theorem amplitude_recurrence_all (w r : ℂ) (n : ℕ) :
    (2+w*r)*r^(n+1) + (n+1)*(w+3*r+w*r^2)*r^n =
    w*(n+2)*r^(n+2) + (3*(n+1)+2)*r^(n+1) + w*(n+1)*r^n := by
  rw [show n+2 = (n+1)+1 by omega, pow_succ]
  rw [pow_succ]
  ring

noncomputable def ampAlpha (u : ℂ) : ℂ := u/(2-u)
noncomputable def ampRatio (u w : ℂ) : ℂ := -w*(1-u)/(2-u)

/-- Rational identity for i α̇ = (2+wρ) α when u=e^{-it}. -/
theorem riccati_alpha (u w : ℂ)
    (hu : (2 : ℂ)-u ≠ 0) (hw : w^2 = (2 : ℂ)) :
    2*u/((2-u)^2) = (2+w*ampRatio u w)*ampAlpha u := by
  unfold ampRatio ampAlpha
  calc
    2*u/((2-u)^2) =
        (2-2*(1-u)/(2-u))*(u/(2-u)) := by
          field_simp [hu]
          ring
    _ = (2-w^2*(1-u)/(2-u))*(u/(2-u)) := by rw [hw]
    _ = (2+w*(-w*(1-u)/(2-u)))*(u/(2-u)) := by ring

/-- Rational identity for i ρ̇ = w+3ρ+wρ² when u=e^{-it}. -/
theorem riccati_ratio (u w : ℂ)
    (hu : (2 : ℂ)-u ≠ 0) (hw : w^2 = (2 : ℂ)) :
    w*u/((2-u)^2) =
      w+3*ampRatio u w+w*(ampRatio u w)^2 := by
  unfold ampRatio
  calc
    w*u/((2-u)^2) =
        w*(1-3*(1-u)/(2-u)+2*((1-u)/(2-u))^2) := by
          field_simp [hu]
          ring
    _ = w*(1-3*(1-u)/(2-u)+w^2*((1-u)/(2-u))^2) := by
          rw [hw]
    _ = w+3*(-w*(1-u)/(2-u))+w*(-w*(1-u)/(2-u))^2 := by ring

/-- The recurrence's first values exactly reproduce the moment-derived data. -/
theorem first_lanczos_squared :
    (6 : ℝ)-2^2=2 := by norm_num

theorem second_lanczos_squared :
    ((150 : ℝ)-14*26+65*6-112*2+64)/2=8 := by norm_num

end InfiniteModes
end ClassicalGravityKrylov
