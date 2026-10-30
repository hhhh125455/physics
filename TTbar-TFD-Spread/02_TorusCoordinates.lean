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

end TTbarTFD
