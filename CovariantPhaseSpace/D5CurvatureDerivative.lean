import Mathlib

/-!
# D5: rigorous derivative of the scalar-curvature radius expression

This proves the mathematical derivative of 2/a² for a nonzero radius.
The geometric identification of 2/a² with the scalar curvature of
(R × S², -dt² + a² h) is a separate differential-geometric calculation.
-/

namespace CovariantPhaseSpace

theorem product_sphere_curvature_radius_hasDerivAt
    (a : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun x : ℝ => (2 : ℝ) / x ^ 2)
      (-(4 : ℝ) / a ^ 3) a := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * a) a := by
    convert (hasDerivAt_id a).pow 2 using 1 <;> ring
  have hc : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 a :=
    hasDerivAt_const a (2 : ℝ)
  have hdiv :
      HasDerivAt (fun x : ℝ => (2 : ℝ) / x ^ 2)
        ((0 * a ^ 2 - 2 * (2 * a)) / (a ^ 2) ^ 2) a := by
    convert hc.div hpow (pow_ne_zero 2 ha) using 1 <;> ring
  have hid : (0 * a ^ 2 - 2 * (2 * a)) / (a ^ 2) ^ 2 =
      -(4 : ℝ) / a ^ 3 := by
    field_simp [ha]
    ring
  rw [hid] at hdiv
  exact hdiv

end CovariantPhaseSpace
