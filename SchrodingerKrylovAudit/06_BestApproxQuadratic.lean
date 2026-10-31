import Mathlib

/-!
# Krylov complexity comparison through best polynomial approximation

For the original positive-chemical-potential fermionic spectrum,
w_q(x) = w_0(x) / (1 + q * exp(-beta*x)) on x >= 0,
so m*w_0 <= w_q <= w_0 with m = 1/(1+q).

The following theorems *formally prove* abstract best-approximation
comparison and finite partial-sum comparison for normalized errors.
The Hilbert-space tail identity, polynomial completeness, and
the exact reference Gamma complexity are proved analytically in
the accompanying research note, not formalized in this Lean file.
-/

namespace SchrodingerKrylovAudit

/-- Best-approximation errors inherit pointwise comparison of squared norms.
The two GLB hypotheses state precisely that E0 and E1 are infima. -/
theorem best_approx_error_comparison
    {A : Type*} (err0 err1 : A → ℝ) (E0 E1 m : ℝ)
    (hm : 0 ≤ m)
    (hpoint : ∀ p : A, m * err0 p ≤ err1 p ∧ err1 p ≤ err0 p)
    (h0lo : ∀ p : A, E0 ≤ err0 p)
    (h1lo : ∀ p : A, E1 ≤ err1 p)
    (h0glb : ∀ r : ℝ, (∀ p : A, r ≤ err0 p) → r ≤ E0)
    (h1glb : ∀ r : ℝ, (∀ p : A, r ≤ err1 p) → r ≤ E1) :
    m * E0 ≤ E1 ∧ E1 ≤ E0 := by
  constructor
  · apply h1glb
    intro p
    calc
      m * E0 ≤ m * err0 p := mul_le_mul_of_nonneg_left (h0lo p) hm
      _ ≤ err1 p := (hpoint p).1
  · apply h0glb
    intro p
    exact (h1lo p).trans (hpoint p).2

/-- Normalize approximation errors by total spectral mass.
The reciprocal factors m and 1/m are exact. -/
theorem normalized_error_comparison
    (m Z0 Z1 E0 E1 : ℝ)
    (hm : 0 < m) (hZ0 : 0 < Z0)
    (hZlo : m * Z0 ≤ Z1) (hZhi : Z1 ≤ Z0)
    (hE0 : 0 ≤ E0)
    (hElo : m * E0 ≤ E1) (hEhi : E1 ≤ E0) :
    m * (E0 / Z0) ≤ E1 / Z1 ∧
    E1 / Z1 ≤ (1 / m) * (E0 / Z0) := by
  have hZ1 : 0 < Z1 := lt_of_lt_of_le (mul_pos hm hZ0) hZlo
  have hcross1 : (m * E0) * Z1 ≤ E1 * Z0 := by
    calc
      (m * E0) * Z1 ≤ (m * E0) * Z0 :=
        mul_le_mul_of_nonneg_left hZhi (mul_nonneg hm.le hE0)
      _ ≤ E1 * Z0 := mul_le_mul_of_nonneg_right hElo hZ0.le
  have hcross2 : E1 * (m * Z0) ≤ E0 * Z1 := by
    calc
      E1 * (m * Z0) ≤ E0 * (m * Z0) :=
        mul_le_mul_of_nonneg_right hEhi (mul_pos hm hZ0).le
      _ ≤ E0 * Z1 := mul_le_mul_of_nonneg_left hZlo hE0
  constructor
  · calc
      m * (E0 / Z0) = (m * E0) / Z0 := by ring
      _ ≤ E1 / Z1 := (div_le_div_iff₀ hZ0 hZ1).mpr hcross1
  · calc
      E1 / Z1 ≤ E0 / (m * Z0) :=
        (div_le_div_iff₀ hZ1 (mul_pos hm hZ0)).mpr hcross2
      _ = (1 / m) * (E0 / Z0) := by
        field_simp
        <;> ring

/-- Every finite partial sum of Krylov approximation errors has
an exact upper and lower quadratic comparison factor. -/
theorem normalized_errors_partial_sum
    (m Z0 Z1 : ℝ) (E0 E1 : ℕ → ℝ) (N : ℕ)
    (hm : 0 < m) (hZ0 : 0 < Z0)
    (hZlo : m * Z0 ≤ Z1) (hZhi : Z1 ≤ Z0)
    (hE0 : ∀ n : ℕ, 0 ≤ E0 n)
    (hElo : ∀ n : ℕ, m * E0 n ≤ E1 n)
    (hEhi : ∀ n : ℕ, E1 n ≤ E0 n) :
    m * (∑ n ∈ Finset.range N, E0 (n + 1) / Z0) ≤
      ∑ n ∈ Finset.range N, E1 (n + 1) / Z1
    ∧
      (∑ n ∈ Finset.range N, E1 (n + 1) / Z1) ≤
      (1 / m) * (∑ n ∈ Finset.range N, E0 (n + 1) / Z0) := by
  have hterm (n : ℕ) :
      m * (E0 (n + 1) / Z0) ≤ E1 (n + 1) / Z1 ∧
      E1 (n + 1) / Z1 ≤ (1 / m) * (E0 (n + 1) / Z0) :=
    normalized_error_comparison
      m Z0 Z1 (E0 (n + 1)) (E1 (n + 1))
      hm hZ0 hZlo hZhi (hE0 _) (hElo _) (hEhi _)
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n _ => (hterm n).1)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n _ => (hterm n).2)

/-- Direct all-index mass-independent bound for logistic weight. -/
theorem logistic_weight_uniform_ratio (q x beta : ℝ)
    (hq : 0 ≤ q) (hbeta : 0 ≤ beta) (hx : 0 ≤ x) :
    1 / (1 + q) ≤ 1 / (1 + q * Real.exp (-beta * x)) ∧
    1 / (1 + q * Real.exp (-beta * x)) ≤ 1 := by
  have he : Real.exp (-beta * x) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hbeta hx]
  have hpos : 0 < Real.exp (-beta * x) := Real.exp_pos _
  have hz : 0 ≤ q * Real.exp (-beta * x) := mul_nonneg hq hpos.le
  have ha : 0 < 1 + q := by linarith
  have hb : 0 < 1 + q * Real.exp (-beta * x) := by linarith
  constructor
  · apply (div_le_div_iff₀ ha hb).mpr
    have hx0 : 0 ≤ q * (1 - Real.exp (-beta * x)) :=
      mul_nonneg hq (sub_nonneg.mpr he)
    nlinarith
  · apply (div_le_iff₀ hb).mpr
    linarith


/-- An infinite version of the positive-series comparison. Unlike
a finite truncation, this also proves summability of the perturbed
complexity when the reference complexity is finite. -/
theorem bounded_infinite_series_comparison
    (u v : ℕ → ℝ) (m : ℝ) (hm : 0 < m)
    (hu0 : ∀ n : ℕ, 0 ≤ u n)
    (hlo : ∀ n : ℕ, m * u n ≤ v n)
    (hhi : ∀ n : ℕ, v n ≤ (1 / m) * u n)
    (hsum0 : Summable u) :
    Summable v ∧
    m * (∑' n : ℕ, u n) ≤ (∑' n : ℕ, v n) ∧
    (∑' n : ℕ, v n) ≤ (1 / m) * (∑' n : ℕ, u n) := by
  have hv0 (n : ℕ) : 0 ≤ v n :=
    (mul_nonneg hm.le (hu0 n)).trans (hlo n)
  have hsup : Summable (fun n : ℕ => (1 / m) * u n) :=
    hsum0.mul_left (1 / m)
  have hsum1 : Summable v :=
    summable_of_nonneg_of_le hv0 hhi hsup
  have hsub : Summable (fun n : ℕ => m * u n) :=
    hsum0.mul_left m
  have hleft : (∑' n : ℕ, m * u n) ≤ (∑' n : ℕ, v n) :=
    tsum_le_tsum hlo hsub hsum1
  have hright : (∑' n : ℕ, v n) ≤
      (∑' n : ℕ, (1 / m) * u n) :=
    tsum_le_tsum hhi hsum1 hsup
  refine ⟨hsum1, ?_, ?_⟩
  · simpa only [tsum_mul_left] using hleft
  · simpa only [tsum_mul_left] using hright

/-- All-time comparison of normalized infinite approximation-error sums:
the reference sum is finite, so the deformed one is finite and bounded
between m and 1/m times the reference. -/
theorem normalized_errors_infinite_sum
    (m Z0 Z1 : ℝ) (E0 E1 : ℕ → ℝ)
    (hm : 0 < m) (hZ0 : 0 < Z0)
    (hZlo : m * Z0 ≤ Z1) (hZhi : Z1 ≤ Z0)
    (hE0 : ∀ n : ℕ, 0 ≤ E0 n)
    (hElo : ∀ n : ℕ, m * E0 n ≤ E1 n)
    (hEhi : ∀ n : ℕ, E1 n ≤ E0 n)
    (hsum0 : Summable (fun n : ℕ => E0 (n + 1) / Z0)) :
    Summable (fun n : ℕ => E1 (n + 1) / Z1) ∧
    m * (∑' n : ℕ, E0 (n + 1) / Z0) ≤
      (∑' n : ℕ, E1 (n + 1) / Z1) ∧
    (∑' n : ℕ, E1 (n + 1) / Z1) ≤
      (1 / m) * (∑' n : ℕ, E0 (n + 1) / Z0) := by
  have hpair (n : ℕ) :=
    normalized_error_comparison
      m Z0 Z1 (E0 (n + 1)) (E1 (n + 1))
      hm hZ0 hZlo hZhi (hE0 _) (hElo _) (hEhi _)
  exact bounded_infinite_series_comparison
    (fun n : ℕ => E0 (n + 1) / Z0)
    (fun n : ℕ => E1 (n + 1) / Z1) m hm
    (fun n => div_nonneg (hE0 _) hZ0.le)
    (fun n => (hpair n).1)
    (fun n => (hpair n).2)
    hsum0

end SchrodingerKrylovAudit
