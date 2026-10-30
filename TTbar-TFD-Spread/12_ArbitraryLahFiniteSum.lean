import Mathlib

/-!
# TTbar TFD: arbitrary-index checks for the Lah finite-sum formula

This file formalizes the weight-positivity and universal non-cancellation
consequences of the proposed finite Laguerre--Gram/Cauchy--Binet expansion.

IMPORTANT: it does NOT prove that this combinatorial sum equals the original
Hankel determinant. That identity needs separate formalization of the
Laguerre/Gram factorization and Cauchy--Binet formula.
-/

namespace TTbarArbitraryLah

open scoped BigOperators

/-- The explicit weight W_(J,l)(u) in the proposed finite-sum formula. -/
noncomputable def weight (J l : ℕ) (u : ℚ) : ℚ :=
  if l = 0 then u ^ J / (Nat.factorial J : ℚ)
  else (u ^ l / (Nat.factorial l : ℚ)) *
    ∑ r ∈ Finset.range (J - l + 1),
      ((Nat.choose (J - r - 1) (l - 1) : ℚ) * u ^ r) /
        (Nat.factorial r : ℚ)

/-- Uniform in J and l: all combinatorial weights are nonnegative for u >= 0. -/
theorem weight_nonneg (J l : ℕ) (u : ℚ) (hu : 0 ≤ u) :
    0 ≤ weight J l u := by
  unfold weight
  split_ifs with hl
  · exact div_nonneg (pow_nonneg hu _) (Nat.cast_nonneg _)
  · apply mul_nonneg
      (div_nonneg (pow_nonneg hu _) (Nat.cast_nonneg _))
    apply Finset.sum_nonneg
    intro r hr
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu _))
      (Nat.cast_nonneg _)

/-- Every l=0 weight is strictly positive at positive u. -/
theorem weight_zero_pos (J : ℕ) (u : ℚ) (hu : 0 < u) :
    0 < weight J 0 u := by
  have hf : (0 : ℚ) < (Nat.factorial J : ℚ) := by
    exact_mod_cast Nat.factorial_pos J
  simpa [weight] using (div_pos (pow_pos hu J) hf)

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The candidate square-minor expansion over subsets of cardinality N. -/
noncomputable def minorSum (N : ℕ) (coeff : Finset ι → ℚ)
    (w : ι → ℚ) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset ι).powersetCard N,
    (coeff S) ^ 2 * (∏ i ∈ S, w i)

/-- The square-minor formula has no cancellation when weights are nonnegative. -/
theorem minorSum_nonneg (N : ℕ) (coeff : Finset ι → ℚ)
    (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ minorSum N coeff w := by
  unfold minorSum
  apply Finset.sum_nonneg
  intro S hS
  apply mul_nonneg (sq_nonneg _)
  exact Finset.prod_nonneg (fun i hi => hw i)

/-- Positive weights plus at least one nonzero selected minor imply strict positivity. -/
theorem minorSum_pos (N : ℕ) (coeff : Finset ι → ℚ)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i)
    (hex : ∃ S ∈ (Finset.univ : Finset ι).powersetCard N,
      coeff S ≠ 0) :
    0 < minorSum N coeff w := by
  unfold minorSum
  apply Finset.sum_pos'
  · intro S hS
    exact mul_nonneg (sq_nonneg _) (Finset.prod_nonneg (fun i hi => (hw i).le))
  · rcases hex with ⟨S, hS, hc⟩
    refine ⟨S, hS, ?_⟩
    have hs : 0 < coeff S ^ 2 := sq_pos_of_ne_zero hc
    have hwS : 0 < ∏ i ∈ S, w i :=
      Finset.prod_pos (fun i hi => hw i)
    exact mul_pos hs hwS

end TTbarArbitraryLah
