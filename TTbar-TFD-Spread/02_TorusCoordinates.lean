import Mathlib

/-!
TTbar-TFD Spread, Section 02 (source lines 26--41).
We verify the algebra of the torus identifications.  This does NOT
prove the path integral / Hilbert space trace correspondence.
-/

namespace TTbarTFD

noncomputable def torusCoord (φ t L : ℝ) : ℂ :=
  ((φ : ℂ) + Complex.I * (t : ℂ)) / (L : ℂ)

noncomputable def torusTau (θ β L : ℝ) : ℂ :=
  ((θ : ℂ) + Complex.I * (β : ℂ)) / (L : ℂ)

/-- The Euclidean-time and angular twist shifts the complex coordinate by tau. -/
theorem shift_thermal (φ t θ β L : ℝ) :
    torusCoord (φ + θ) (t + β) L =
      torusCoord φ t L + torusTau θ β L := by
  unfold torusCoord torusTau
  push_cast
  ring

/-- A spatial shift by circumference L is a unit shift of z. -/
theorem shift_spatial (φ t L : ℝ) (hL : L ≠ 0) :
    torusCoord (φ + L) t L = torusCoord φ t L + 1 := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  unfold torusCoord
  push_cast
  field_simp [hLc]
  ring

/-- T changes the lattice generator tau by one spatial cycle. -/
theorem shift_T (τ : ℂ) : τ + 1 = 1 + τ := by
  ring


/- Additional checks: shape parameter and nondegeneracy of the lattice.
   The original paper uses L = 2π; here all statements are for any L > 0. -/

/-- Multiplication by the real spatial period recovers the thermal cycle. -/
theorem tau_times_length (θ β L : ℝ) (hL : L ≠ 0) :
    torusTau θ β L * (L : ℂ) =
      (θ : ℂ) + Complex.I * (β : ℂ) := by
  have hc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  unfold torusTau
  field_simp [hc]

/-- The real part of tau is angular twist divided by circumference. -/
theorem tau_real (θ β L : ℝ) (hL : L ≠ 0) :
    (torusTau θ β L).re = θ / L := by
  have h := congrArg Complex.re (tau_times_length θ β L hL)
  have hprod : (torusTau θ β L).re * L = θ := by
    simpa [Complex.mul_re, Complex.add_re] using h
  apply (eq_div_iff hL).2
  simpa [mul_comm] using hprod

/-- The imaginary part of tau is thermal period divided by circumference. -/
theorem tau_imag (θ β L : ℝ) (hL : L ≠ 0) :
    (torusTau θ β L).im = β / L := by
  have h := congrArg Complex.im (tau_times_length θ β L hL)
  have hprod : (torusTau θ β L).im * L = β := by
    simpa [Complex.mul_im, Complex.add_im] using h
  apply (eq_div_iff hL).2
  simpa [mul_comm] using hprod

/-- A positive Euclidean-time period gives a modulus in the upper half-plane. -/
theorem tau_upper_half_plane (θ β L : ℝ) (hL : 0 < L)
    (hβ : 0 < β) :
    0 < (torusTau θ β L).im := by
  rw [tau_imag θ β L (ne_of_gt hL)]
  positivity

/-- The two torus lattice cycles have no nontrivial integer relation
    when Im τ ≠ 0. -/
theorem lattice_independent (τ : ℂ) (hτ : τ.im ≠ 0)
    (m n : ℤ) (h : (m : ℂ) + (n : ℂ) * τ = 0) :
    m = 0 ∧ n = 0 := by
  have him := congrArg Complex.im h
  have hnprod : (n : ℝ) * τ.im = 0 := by
    simpa [Complex.mul_im, Complex.add_im] using him
  have hnreal : (n : ℝ) = 0 :=
    (mul_eq_zero.mp hnprod).resolve_right hτ
  have hn : n = 0 := by exact_mod_cast hnreal
  subst n
  have hm : m = 0 := by
    simpa using h
  exact ⟨hm, rfl⟩

/-- Thermal and spatial identifications are independent for β,L > 0. -/
theorem torus_lattice_independent (θ β L : ℝ)
    (hL : 0 < L) (hβ : 0 < β) (m n : ℤ)
    (h : (m : ℂ) + (n : ℂ) * torusTau θ β L = 0) :
    m = 0 ∧ n = 0 := by
  exact lattice_independent (torusTau θ β L)
    (ne_of_gt (tau_upper_half_plane θ β L hL hβ)) m n h

/-- Replacing a lattice generator τ by τ+1 is a unimodular basis change. -/
theorem lattice_T_change (τ : ℂ) (m n : ℤ) :
    (m : ℂ) + (n : ℂ) * (τ + 1) =
      ((m+n : ℤ) : ℂ) + (n : ℂ) * τ := by
  push_cast
  ring

/-- Every old lattice vector can be represented after T change. -/
theorem lattice_T_inverse (τ : ℂ) (m n : ℤ) :
    (m : ℂ) + (n : ℂ) * τ =
      ((m-n : ℤ) : ℂ) + (n : ℂ) * (τ + 1) := by
  push_cast
  ring

end TTbarTFD
