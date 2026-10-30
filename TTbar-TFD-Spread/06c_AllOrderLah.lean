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
  have hg : geometric = mk (1 : ℕ → ℝ) := by
    ext t
    simp [geometric]
  rw [hg]
  simpa [Nat.succ_eq_add_one, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc] using
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

/- The full generating function is the exponential formal series composed
   with uX/(1-X); coefficients are computed at EVERY order m, not merely
   m=1,2,3. -/
noncomputable def formalModelGenerating (u : ℝ) : PowerSeries ℝ :=
  subst (rationalArgument u) (PowerSeries.exp ℝ)

theorem formal_model_coeff_all (u : ℝ) (m : ℕ) :
    (coeff m) (formalModelGenerating u) =
      ∑ j ∈ Finset.range (m+1),
        if j = 0 then (if m = 0 then (1 : ℝ) else 0)
        else (u^j / (Nat.factorial j : ℝ)) *
             (Nat.choose (m-1) (j-1) : ℝ) := by
  classical
  unfold formalModelGenerating
  rw [PowerSeries.coeff_subst' (rational_argument_substitutable u)
       (PowerSeries.exp ℝ) m]
  have hs : Function.support
      (fun j : ℕ => (coeff j) (PowerSeries.exp ℝ) •
        (coeff m) ((rationalArgument u)^j)) ⊆
      ↑(Finset.range (m+1)) := by
    intro j hj
    by_contra hmem
    have hgt : m < j := by
      simp only [Finset.mem_coe, Finset.mem_range] at hmem
      omega
    have hzero : (coeff m) ((rationalArgument u)^j) = 0 := by
      rw [rational_argument_power_coeff u m j (by omega)]
      simp [not_le.mpr hgt]
    have hz : ((coeff j) (PowerSeries.exp ℝ) •
      (coeff m) ((rationalArgument u)^j)) = 0 := by
      simp [hzero]
    exact (Function.mem_support.mp hj) hz
  rw [finsum_eq_finsetSum_of_support_subset _ hs]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ m := by
    have h := Finset.mem_range.mp hj
    omega
  by_cases hj0 : j = 0
  · subst j
    simp [PowerSeries.coeff_exp]
  · have hjpos : 0 < j := by omega
    rw [rational_argument_power_coeff u m j hjpos]
    rw [if_pos hjle]
    simp only [PowerSeries.coeff_exp, if_neg hj0]
    simp only [smul_eq_mul, map_div, map_inv, map_one, map_natCast, div_eq_mul_inv]
    ring


/-- Exact coefficient at degree zero in the formal generating series. -/
theorem formal_model_coeff_zero (u : ℝ) :
    (coeff 0) (formalModelGenerating u) = 1 := by
  simp [formal_model_coeff_all]

/-- For every positive degree, the zero-index term vanishes and the
    ALL-ORDER coefficient is the claimed finite Lah-number sum. -/
theorem formal_model_coeff_positive (u : ℝ) (m : ℕ) (hm : 0 < m) :
    (coeff m) (formalModelGenerating u) =
      ∑ j ∈ Finset.Icc 1 m,
        (u ^ j / (Nat.factorial j : ℝ)) *
          (Nat.choose (m - 1) (j - 1) : ℝ) := by
  rw [formal_model_coeff_all]
  have hset : Finset.range (m + 1) =
      insert 0 (Finset.Icc 1 m) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  have hm0 : m ≠ 0 := by omega
  simp only [if_pos rfl, if_neg hm0, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : j ≠ 0 := by
    have h := (Finset.mem_Icc.mp hj).1
    omega
  simp only [if_neg hj0]

/-- Inverse-temperature rescaling reproduces EXACTLY the manuscript's
    arbitrary-order finite Lah formula for the *model* moment.
    m is arbitrary, not checked only up to three. -/
theorem formal_model_moment_all
    (A β : ℝ) (hβ : β ≠ 0) (m : ℕ) (hm : 0 < m) :
    ((Nat.factorial m : ℝ) / β ^ m) *
      (coeff m) (formalModelGenerating (A / β)) =
        ∑ j ∈ Finset.Icc 1 m,
          ((Nat.factorial m : ℝ) / (Nat.factorial j : ℝ)) *
          (Nat.choose (m - 1) (j - 1) : ℝ) *
          A ^ j / β ^ (m + j) := by
  rw [formal_model_coeff_positive (A / β) m hm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  rw [div_pow, pow_add]
  field_simp [hβ, hf] <;> ring


end TTbarTFDAllOrder
