import Mathlib

/-!
# Original fermionic Wightman spectrum, JHEP02(2026)259 Eq. (3.1)

This module verifies exact pointwise spectral transformations and
nonnegative remainder bounds for every moment order. The
special-function integration is not yet formalized in Lean.
-/

namespace SchrodingerKrylovAudit

theorem original_fermion_factor_rewrite (beta mu x : ℝ) :
    Real.exp (beta * (mu - x) / 2) /
      (1 + Real.exp (beta * (mu - x))) =
    (Real.exp (beta * mu / 2) * Real.exp (-beta * x / 2)) /
      (1 + Real.exp (beta * mu) * Real.exp (-beta * x)) := by
  have hnum : beta * (mu - x) / 2 = beta * mu / 2 + (-beta * x / 2) := by ring
  have hden : beta * (mu - x) = beta * mu + (-beta * x) := by ring
  rw [hnum, hden, Real.exp_add, Real.exp_add]

theorem logistic_defect_bounds (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ 1 - 1 / (1 + u) ∧ 1 - 1 / (1 + u) ≤ u := by
  have hd : 0 < 1 + u := by linarith
  have heq : 1 - 1 / (1 + u) = u / (1 + u) := by
    field_simp
    <;> ring
  rw [heq]
  constructor
  · exact div_nonneg hu hd.le
  · exact (div_le_iff₀ hd).mpr (by nlinarith [sq_nonneg u])

theorem positive_weight_correction (A u : ℝ) (hA : 0 ≤ A) (hu : 0 ≤ u) :
    0 ≤ A - A / (1 + u) ∧ A - A / (1 + u) ≤ A * u := by
  have heq : A - A / (1 + u) = A * (1 - 1 / (1 + u)) := by ring
  rw [heq]
  rcases logistic_defect_bounds u hu with ⟨h0, h1⟩
  exact ⟨mul_nonneg hA h0, mul_le_mul_of_nonneg_left h1 hA⟩

theorem original_positive_weight (beta q x : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    0 ≤ x * Real.exp (-beta * x / 2) /
      (1 + q * Real.exp (-beta * x)) := by
  have hn : 0 ≤ x * Real.exp (-beta * x / 2) :=
    mul_nonneg hx (Real.exp_pos _).le
  have hd : 0 ≤ 1 + q * Real.exp (-beta * x) := by
    have hh : 0 ≤ q * Real.exp (-beta * x) :=
      mul_nonneg hq (Real.exp_pos _).le
    linarith
  exact div_nonneg hn hd

theorem original_all_order_tail_error
    (beta q x : ℝ) (k : ℕ) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    0 ≤ (x ^ (k + 1) * Real.exp (-beta * x / 2)) -
       (x ^ (k + 1) * Real.exp (-beta * x / 2)) /
         (1 + q * Real.exp (-beta * x)) ∧
    (x ^ (k + 1) * Real.exp (-beta * x / 2)) -
       (x ^ (k + 1) * Real.exp (-beta * x / 2)) /
         (1 + q * Real.exp (-beta * x)) ≤
       (x ^ (k + 1) * Real.exp (-beta * x / 2)) *
         (q * Real.exp (-beta * x)) := by
  have hA : 0 ≤ x ^ (k + 1) * Real.exp (-beta * x / 2) :=
    mul_nonneg (pow_nonneg hx _) (Real.exp_pos _).le
  have hu : 0 ≤ q * Real.exp (-beta * x) :=
    mul_nonneg hq (Real.exp_pos _).le
  exact positive_weight_correction _ _ hA hu

theorem original_weight_ratio_sandwich
    (beta q x : ℝ) (hb : 0 ≤ beta) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    1 / (1 + q) ≤ 1 / (1 + q * Real.exp (-beta * x)) ∧
    1 / (1 + q * Real.exp (-beta * x)) ≤ 1 := by
  have he0 : 0 < Real.exp (-beta * x) := Real.exp_pos _
  have he1 : Real.exp (-beta * x) ≤ 1 := by
    have hbx : -beta * x ≤ (0 : ℝ) := by
      have h : 0 ≤ beta * x := mul_nonneg hb hx
      linarith
    simpa using (Real.exp_le_exp.mpr hbx)
  have hp : 0 ≤ q * Real.exp (-beta * x) := mul_nonneg hq he0.le
  have hp2 : 0 ≤ q * (1 - Real.exp (-beta * x)) :=
    mul_nonneg hq (sub_nonneg.mpr he1)
  have hd1 : 0 < 1 + q := by linarith
  have hd2 : 0 < 1 + q * Real.exp (-beta * x) := by linarith
  constructor
  · apply (div_le_div_iff₀ hd1 hd2).mpr
    nlinarith
  · apply (div_le_iff₀ hd2).mpr
    linarith

theorem original_exponential_rate_ratio (beta : ℝ) (hb : beta ≠ 0) :
    (beta / 2) / (beta / 2 + beta) = 1 / 3 := by
  field_simp
  <;> ring

end SchrodingerKrylovAudit
