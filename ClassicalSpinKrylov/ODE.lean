import ClassicalSpinKrylov.Dynamics

/-!
The exact rotation trajectory satisfies the Hamilton ODE in all three
coordinates.  These are genuine HasDerivAt statements, not numerical
sampling or conservation-only checks.
-/

namespace ClassicalSpinKrylov

private theorem phase_hasDerivAt (ω t : ℝ) :
    HasDerivAt (fun u : ℝ => ω * u) ω t := by
  simpa using (hasDerivAt_id t).const_mul ω

private theorem rotating_sin_hasDerivAt (ω t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin (ω * u))
      (ω * Real.cos (ω * t)) t := by
  convert (Real.hasDerivAt_sin (ω * t)).comp t (phase_hasDerivAt ω t) using 1 <;>
    (first | rfl | ring)

private theorem rotating_cos_hasDerivAt (ω t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.cos (ω * u))
      (-ω * Real.sin (ω * t)) t := by
  convert (Real.hasDerivAt_cos (ω * t)).comp t (phase_hasDerivAt ω t) using 1 <;>
    (first | rfl | ring)

/-- The x coordinate of a planar rotation has the correct time derivative. -/
theorem rotation_x_hasDerivAt (x y ω t : ℝ) :
    HasDerivAt
      (fun u : ℝ => x * Real.cos (ω * u) - y * Real.sin (ω * u))
      (-ω * (x * Real.sin (ω * t) + y * Real.cos (ω * t))) t := by
  convert ((rotating_cos_hasDerivAt ω t).const_mul x).sub
    ((rotating_sin_hasDerivAt ω t).const_mul y) using 1 <;>
    (first | rfl | ring)

/-- The y coordinate of a planar rotation has the correct time derivative. -/
theorem rotation_y_hasDerivAt (x y ω t : ℝ) :
    HasDerivAt
      (fun u : ℝ => x * Real.sin (ω * u) + y * Real.cos (ω * u))
      (ω * (x * Real.cos (ω * t) - y * Real.sin (ω * t))) t := by
  convert ((rotating_sin_hasDerivAt ω t).const_mul x).add
    ((rotating_cos_hasDerivAt ω t).const_mul y) using 1 <;>
    (first | rfl | ring)

/-- The explicit spin evolution really solves the first Hamilton ODE. -/
theorem evolve_solves_x (χ t : ℝ) (s : Spin) :
    HasDerivAt (fun u : ℝ => (evolve χ u s).x)
      (vectorField χ (evolve χ t s)).x t := by
  convert rotation_x_hasDerivAt s.x s.y (2 * χ * s.z) t using 1 <;>
    (simp [evolve, vectorField_x] <;> ring)

/-- The explicit spin evolution really solves the second Hamilton ODE. -/
theorem evolve_solves_y (χ t : ℝ) (s : Spin) :
    HasDerivAt (fun u : ℝ => (evolve χ u s).y)
      (vectorField χ (evolve χ t s)).y t := by
  convert rotation_y_hasDerivAt s.x s.y (2 * χ * s.z) t using 1 <;>
    (simp [evolve, vectorField_y] <;> ring)

/-- The z component is constant and satisfies the third Hamilton ODE. -/
theorem evolve_solves_z (χ t : ℝ) (s : Spin) :
    HasDerivAt (fun u : ℝ => (evolve χ u s).z)
      (vectorField χ (evolve χ t s)).z t := by
  have h : HasDerivAt (fun _ : ℝ => s.z) 0 t := by
    exact hasDerivAt_const t s.z
  simpa only [evolve, vectorField_z] using h

end ClassicalSpinKrylov
