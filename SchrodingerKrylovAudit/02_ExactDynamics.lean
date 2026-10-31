import Mathlib

/-!
# Second pass: exact solvable spectral models of JHEP02(2026)259

This formalizes (a) a general complex-valued algebraic identity underlying
(4.7), (b) actual infinite geometric normalizations and means underlying
(4.8)/(4.14), and (c) parameter-dependent probabilities for the one-sided
spectrum. It does NOT assume the field theory or the Lanczos asymptotics.
-/

namespace SchrodingerKrylovAudit

/-- The real geometric ratio associated with the one-sided spectrum (4.1). -/
noncomputable def oneSidedRatio (k t : ℝ) : ℝ := t ^ 2 / (k ^ 2 + t ^ 2)

theorem oneSidedRatio_nonneg (k t : ℝ) (hk : 0 < k) :
    0 ≤ oneSidedRatio k t := by
  unfold oneSidedRatio
  have hd : 0 < k ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hk) (sq_nonneg t)
  exact div_nonneg (sq_nonneg t) hd.le

theorem oneSidedRatio_lt_one (k t : ℝ) (hk : 0 < k) :
    oneSidedRatio k t < 1 := by
  unfold oneSidedRatio
  have hsq : 0 < k ^ 2 := sq_pos_of_pos hk
  have hd : 0 < k ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg hsq (sq_nonneg t)
  apply (div_lt_one hd).mpr
  linarith

/-- Exact normalization of an infinite geometric Krylov probability. -/
theorem geometric_probability_normalization (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, (1 - q) * q ^ n) = 1 := by
  have hden : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  field_simp

/-- Infinite geometric mean, using Mathlib's convergent factorial-power sum. -/
theorem geometric_first_moment (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, (n : ℝ) * q ^ n) = q / (1 - q) ^ 2 := by
  have hn : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  let f : ℕ → ℝ := fun n => (↑((n + 1).choose 1) : ℝ) * q ^ n
  have hf : Summable f := by
    dsimp [f]
    exact summable_choose_mul_geometric_of_norm_lt_one 1 hn
  have hg : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hq0 hq1
  have hsum : (∑' n : ℕ, f n) = 1 / (1 - q) ^ 2 := by
    dsimp [f]
    exact tsum_choose_mul_geometric_of_norm_lt_one 1 hn
  have hden : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  calc
    (∑' n : ℕ, (n : ℝ) * q ^ n) =
        (∑' n : ℕ, f n - q ^ n) := by
          apply tsum_congr
          intro n
          dsimp [f]
          simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
          ring
    _ = (∑' n : ℕ, f n) - (∑' n : ℕ, q ^ n) := hf.tsum_sub hg
    _ = 1 / (1 - q) ^ 2 - 1 / (1 - q) := by
          rw [hsum, tsum_geometric_of_lt_one hq0 hq1]
          ring
    _ = q / (1 - q) ^ 2 := by field_simp [hden]; ring


/-- Exact expected Krylov site, rather than a finite-n numerical spot check. -/
theorem geometric_probability_mean (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, (n : ℝ) * ((1 - q) * q ^ n)) = q / (1 - q) := by
  have hden : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  calc
    (∑' n : ℕ, (n : ℝ) * ((1 - q) * q ^ n)) =
        (1 - q) * ∑' n : ℕ, (n : ℝ) * q ^ n := by
          have hterm : (fun n : ℕ => (n : ℝ) * ((1 - q) * q ^ n)) =
              (fun n : ℕ => (1 - q) * ((n : ℝ) * q ^ n)) := by
                funext n; ring
          rw [hterm, tsum_mul_left]
    _ = (1 - q) * (q / (1 - q) ^ 2) := by
          rw [geometric_first_moment q hq0 hq1]
    _ = q / (1 - q) := by field_simp

/-- One-sided exact complexity (4.8), modulo its spectral-amplitude identity. -/
theorem oneSidedQuadraticComplexity (k t : ℝ) (hk : 0 < k) :
    (∑' n : ℕ, (n : ℝ) *
        ((1 - oneSidedRatio k t) * (oneSidedRatio k t) ^ n)) =
      t ^ 2 / k ^ 2 := by
  rw [geometric_probability_mean (oneSidedRatio k t)
      (oneSidedRatio_nonneg k t hk) (oneSidedRatio_lt_one k t hk)]
  unfold oneSidedRatio
  have hsq : k ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hk)
  have hd : k ^ 2 + t ^ 2 ≠ 0 := ne_of_gt
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hk) (sq_nonneg t))
  field_simp
  <;> ring

/-- Equation (4.7): polynomial numerator identity for the full n+1 recurrence.
After division by the nonvanishing denominator, this matches the derivative
of the proposed amplitude with the Lanczos right-hand side. -/
theorem eq_4_7_numerator_recurrence (n : ℕ) (k t : ℂ) :
    k * ((n : ℂ) + 1) * t ^ n * (k + Complex.I * t)
      - k * ((n : ℂ) + 2) * Complex.I * t ^ (n + 1) =
    -Complex.I * (2 * (n : ℂ) + 3) * t ^ (n + 1) * (k + Complex.I * t)
      + ((n : ℂ) + 1) * t ^ n * (k + Complex.I * t) ^ 2
      - ((n : ℂ) + 2) * t ^ (n + 2) := by
  have h1 : t ^ (n + 1) = t ^ n * t := by rw [pow_succ]
  have h2 : t ^ (n + 2) = t ^ n * t ^ 2 := by rw [pow_add]
  apply sub_eq_zero.mp
  calc
    (k * ((n : ℂ) + 1) * t ^ n * (k + Complex.I * t)
      - k * ((n : ℂ) + 2) * Complex.I * t ^ (n + 1)) -
    (-Complex.I * (2 * (n : ℂ) + 3) * t ^ (n + 1) * (k + Complex.I * t)
      + ((n : ℂ) + 1) * t ^ n * (k + Complex.I * t) ^ 2
      - ((n : ℂ) + 2) * t ^ (n + 2)) =
      ((n : ℂ) + 2) * t ^ (n + 2) * (Complex.I ^ 2 + 1) := by
        rw [h1, h2]
        ring
    _ = 0 := by simp [Complex.I_sq]

/-- The n=0 version of the (4.7) derivative numerator identity. -/
theorem eq_4_7_n0_numerator (k t : ℂ) :
    -(k * Complex.I) = -Complex.I * (k + Complex.I * t) - t := by
  have h : -(k * Complex.I) - (-Complex.I * (k + Complex.I * t) - t) =
      t * (Complex.I ^ 2 + 1) := by ring
  apply sub_eq_zero.mp
  rw [h]
  simp [Complex.I_sq]

/-- The factorial moments of (4.2) obey this exact recurrence. -/
noncomputable def expMoment (k : ℝ) (n : ℕ) : ℝ := (-1) ^ n * (n.factorial : ℝ) / k ^ n

theorem eq_4_2_initial_moment (k : ℝ) : expMoment k 0 = 1 := by
  simp [expMoment]

theorem eq_4_2_moment_recurrence (k : ℝ) (hk : k ≠ 0) (n : ℕ) :
    expMoment k (n + 1) = - ((n : ℝ) + 1) / k * expMoment k n := by
  unfold expMoment
  rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
  field_simp

end SchrodingerKrylovAudit
