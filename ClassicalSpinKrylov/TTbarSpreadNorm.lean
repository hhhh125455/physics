import Mathlib

/-!
# TTbar TFD spread normalization and finite-chain asymptotics
FROZEN physics target:
i dψₙ/dt = bₙ₊₁ ψₙ₊₁ + aₙ ψₙ + bₙ ψₙ₋₁, real Jacobi coefficients.
C_N(t) = ∑ₙ n |ψₙ(t)|² with ∑ₙ |ψₙ(t)|² = 1.
These are purely finite-dimensional algebraic results; no claim that the
1001-level Jacobi approximation proves the infinite CFT asymptotics.
-/
namespace TTbarSpreadNorm

theorem diagonal_probability_drift (a xr xi : ℝ) :
    2 * (xr * (a * xi) + xi * (-a * xr)) = 0 := by
  ring

theorem bond_probability_drift (b xr xi yr yi : ℝ) :
    2 * (xr * (b * yi) + xi * (-b * yr) +
         yr * (b * xi) + yi * (-b * xr)) = 0 := by
  ring

theorem total_bond_probability_drift (N : ℕ)
    (b xr xi yr yi : Fin N → ℝ) :
    (∑ i : Fin N,
      2 * (xr i * (b i * yi i) + xi i * (-b i * yr i) +
           yr i * (b i * xi i) + yi i * (-b i * xr i))) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact bond_probability_drift (b i) (xr i) (xi i) (yr i) (yi i)

theorem initial_one_site_probability :
    ((1 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 1 := by
  norm_num

/-- Probability masses at each level are nonnegative. -/
theorem nonnegative_complexity (N : ℕ) (p : Fin N → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    0 ≤ ∑ i : Fin N, (i.val : ℝ) * p i := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (Nat.cast_nonneg _) (hp i)

/-- The finite normalized chain always has bounded spread: C_N ≤ N. -/
theorem finite_spread_bound (N : ℕ) (p : Fin N → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hnorm : (∑ i : Fin N, p i) = 1) :
    (∑ i : Fin N, (i.val : ℝ) * p i) ≤ (N : ℝ) := by
  calc
    (∑ i : Fin N, (i.val : ℝ) * p i)
        ≤ ∑ i : Fin N, (N : ℝ) * p i := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_right _ (hp i)
          exact_mod_cast Nat.le_of_lt i.isLt
    _ = (N : ℝ) := by
          rw [← Finset.mul_sum, hnorm, mul_one]

/-- Finite-chain normalized complexity is between zero and the cutoff. -/
theorem finite_spread_interval (N : ℕ) (p : Fin N → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hnorm : (∑ i : Fin N, p i) = 1) :
    0 ≤ (∑ i : Fin N, (i.val : ℝ) * p i) ∧
    (∑ i : Fin N, (i.val : ℝ) * p i) ≤ (N : ℝ) := by
  exact ⟨nonnegative_complexity N p hp, finite_spread_bound N p hp hnorm⟩

/-- A finite normalized chain has C_N(t)/t² bounded above by N/t²
    for any positive time. This is *not* a claim about the infinite chain. -/
theorem finite_quadratic_ratio_bound (N : ℕ) (p : Fin N → ℝ) (t : ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hnorm : (∑ i : Fin N, p i) = 1)
    (ht : 0 < t) :
    0 ≤ (∑ i : Fin N, (i.val : ℝ) * p i) / t^2 ∧
    (∑ i : Fin N, (i.val : ℝ) * p i) / t^2 ≤ (N : ℝ) / t^2 := by
  constructor
  · exact div_nonneg (nonnegative_complexity N p hp) (sq_nonneg t)
  · exact (div_le_div_of_nonneg_right (finite_spread_bound N p hp hnorm)
      (sq_pos_of_pos ht))

end TTbarSpreadNorm
