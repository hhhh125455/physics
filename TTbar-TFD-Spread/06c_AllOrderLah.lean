import Mathlib

/-!
Formal power-series proof of the arbitrary-order Lah coefficient formula.
The model moment generating function is the substitution of the
exponential power series by u*X/(1-X).

Unlike checking moments 1, 2, 3, the coefficient identity here is
quantified over all natural indices m and j.
-/

namespace TTbarTFDAllOrder

open PowerSeries

noncomputable def geometric : PowerSeries ℝ := mk (fun _ : ℕ => 1)

noncomputable def rationalArgument (u : ℝ) : PowerSeries ℝ :=
  C u * X * geometric

theorem geometric_pow_coeff (n j : ℕ) (hj : 0 < j) :
    (coeff n) (geometric ^ j) =
      (Nat.choose (j - 1 + n) (j - 1) : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have h := PowerSeries.mk_one_pow_eq_mk_choose_add ℝ k
  simpa only [geometric, Nat.succ_eq_add_one, Nat.add_sub_cancel_left] using
    congrArg (fun p : PowerSeries ℝ => (coeff n) p) h

theorem rational_argument_constant_zero (u : ℝ) :
    constantCoeff (rationalArgument u) = 0 := by
  simp [rationalArgument, geometric]

theorem rational_argument_substitutable (u : ℝ) :
    HasSubst (rationalArgument u) :=
  HasSubst.of_constantCoeff_zero'
    (rational_argument_constant_zero u)

theorem rational_argument_power_coeff
    (u : ℝ) (m j : ℕ) (hj : 0 < j) :
    (coeff m) ((rationalArgument u)^j) =
      if j ≤ m then u^j * (Nat.choose (m-1) (j-1) : ℝ) else 0 := by
  have heq : (rationalArgument u)^j =
      X^j * (geometric^j) * C (u^j) := by
    unfold rationalArgument
    simp only [mul_pow, map_pow]
    ring
  rw [heq, coeff_mul_C]
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [geometric_pow_coeff (m-j) j hj]
    have hi : j-1 + (m-j) = m-1 := by omega
    rw [hi]
    ring
  · ring

end TTbarTFDAllOrder
