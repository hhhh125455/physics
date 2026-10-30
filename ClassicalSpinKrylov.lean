import Mathlib
import ClassicalSpinKrylov.Dynamics
import ClassicalSpinKrylov.ODE

/-!
# Classical spin Krylov: moment integrals and low-order Lanczos relations

The reduced spectral weight is ρ(z) = 3/4 * (1-z²) on [-1,1].
The even moment theorem is proved from its definite integral, not assumed.
The Hamiltonian-to-measure correspondence and all-order Lanczos formula
are beyond the scope of this file.
-/

open MeasureTheory intervalIntegral

namespace ClassicalSpinKrylov

private theorem odd_power_neg_one (n : ℕ) :
    (-1 : ℝ) ^ (2 * n + 1) = -1 := by
  rw [pow_add]
  have h : (-1 : ℝ) ^ (2 * n) = 1 := by
    rw [pow_mul]
    norm_num
  rw [h]
  norm_num

/-- Exact integral of every even monomial over [-1,1]. -/
theorem even_power_integral (n : ℕ) :
    (∫ z : ℝ in -1..1, z ^ (2 * n)) = 2 / (2 * (n : ℝ) + 1) := by
  rw [integral_pow]
  rw [odd_power_neg_one n]
  simp only [one_pow, sub_neg_eq_add]
  have hc : (↑(2 * n) : ℝ) + 1 = 2 * (n : ℝ) + 1 := by
    push_cast
    ring
  rw [hc]
  norm_num

/-- Weighted moment integral for the sphere's azimuth-reduced density. -/
theorem spin_weight_integral (n : ℕ) :
    (∫ z : ℝ in -1..1, (1 - z ^ 2) * z ^ (2 * n)) =
      4 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by
  have hpoint (z : ℝ) :
      (1 - z ^ 2) * z ^ (2 * n) = z ^ (2 * n) - z ^ (2 * (n + 1)) := by
    have hs : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [hs, pow_add]
    ring
  calc
    (∫ z : ℝ in -1..1, (1 - z ^ 2) * z ^ (2 * n)) =
        (∫ z : ℝ in -1..1, z ^ (2 * n) - z ^ (2 * (n + 1))) := by
          apply intervalIntegral.integral_congr
          intro z hz
          exact hpoint z
    _ = (∫ z : ℝ in -1..1, z ^ (2 * n)) -
        (∫ z : ℝ in -1..1, z ^ (2 * (n + 1))) := by
          rw [intervalIntegral.integral_sub]
          all_goals apply Continuous.intervalIntegrable <;> fun_prop
    _ = 2 / (2 * (n : ℝ) + 1) -
        2 / (2 * ((n + 1 : ℕ) : ℝ) + 1) := by
          rw [even_power_integral n, even_power_integral (n + 1)]
    _ = 4 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by
          push_cast
          have h1 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
          have h3 : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
          field_simp
          ring

/-- Moments of the reduced classical-spin density ρ(z)=3/4(1-z²). -/
noncomputable def evenMoment (c : ℝ) (n : ℕ) : ℝ :=
  (3 / 4 : ℝ) * c ^ (2 * n) *
    (∫ z : ℝ in -1..1, (1 - z ^ 2) * z ^ (2 * n))

/-- Formula for all even moments, with spectral weight specified explicitly. -/
theorem evenMoment_formula (c : ℝ) (n : ℕ) :
    evenMoment c n = 3 * c ^ (2 * n) /
      ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by
  unfold evenMoment
  rw [spin_weight_integral]
  ring

theorem moment_normalized (c : ℝ) : evenMoment c 0 = 1 := by
  rw [evenMoment_formula]
  norm_num

theorem moment_two (c : ℝ) : evenMoment c 1 = c ^ 2 / 5 := by
  rw [evenMoment_formula]
  norm_num <;> ring

theorem moment_four (c : ℝ) : evenMoment c 2 = 3 * c ^ 4 / 35 := by
  rw [evenMoment_formula]
  norm_num

theorem fourth_moment_identity (c : ℝ) :
    3 * c ^ 4 / 35 =
      (c ^ 2 / 5) ^ 2 + (c ^ 2 / 5) * (8 * c ^ 2 / 35) := by
  ring

theorem second_lanczos_identity (c : ℝ) :
    (c ^ 2 / 5) * (8 * c ^ 2 / 35) =
      3 * c ^ 4 / 35 - (c ^ 2 / 5) ^ 2 := by
  ring

end ClassicalSpinKrylov
