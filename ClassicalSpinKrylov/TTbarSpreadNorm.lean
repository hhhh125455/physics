import Mathlib

/-!
# TTbar TFD spread: algebraic normalization checks
Frozen physical target: i ∂ₜ ψₙ = bₙ₊₁ ψₙ₊₁ + aₙ ψₙ + bₙ ψₙ₋₁,
with real aₙ,bₙ and finite real-symmetric Jacobi truncation.
The lemmas below verify cancellation of every diagonal and edge
contribution to d/dt ∑ₙ |ψₙ|². They do NOT establish a continuum
spectral approximation, or the numerical spread-complexity curve.
-/

namespace TTbarSpreadNorm

/-- A real diagonal Hamiltonian cannot change local probability. -/
theorem diagonal_probability_drift (a xr xi : ℝ) :
    2 * (xr * (a * xi) + xi * (-a * xr)) = 0 := by
  ring

/-- Contributions of each undirected real symmetric bond cancel exactly. -/
theorem bond_probability_drift
    (b xr xi yr yi : ℝ) :
    2 * (xr * (b * yi) + xi * (-b * yr) +
         yr * (b * xi) + yi * (-b * xr)) = 0 := by
  ring

/-- For any finite bond list, the total pairwise drift vanishes. -/
theorem total_bond_probability_drift (N : ℕ)
    (b xr xi yr yi : Fin N → ℝ) :
    (∑ i : Fin N,
      2 * (xr i * (b i * yi i) + xi i * (-b i * yr i) +
           yr i * (b i * xi i) + yi i * (-b i * xr i))) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact bond_probability_drift (b i) (xr i) (xi i) (yr i) (yi i)

/-- Pointwise initial probability is exactly one at the initial site. -/
theorem initial_one_site_probability :
    ((1 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 1 := by
  norm_num

end TTbarSpreadNorm
