import Mathlib

/-!
Audit completion for TTbar-TFD-Spread lines 180--222:
infinite thermal spectral sums, all order termwise derivative interchange,
positive-temperature convergence hypotheses, complex return amplitudes,
and a proof that an approximate partition-function value does not
automatically control derivatives.

Assumptions are explicit: nonnegative excitation energy E_n and
summability of every Boltzmann-weighted energy moment at a reference
inverse temperature a. This is a SUFFICIENT analytic hypothesis,
not a theorem about arbitrary CFTs.
-/

namespace TTbarTFDInfinite

noncomputable def thermalTerm (E : ℕ → ℝ) (k : ℕ) (n : ℕ)
    (β : ℝ) : ℝ :=
  (-E n)^k * Real.exp (-E n * β)

noncomputable def thermalSum (E : ℕ → ℝ) (k : ℕ)
    (β : ℝ) : ℝ :=
  ∑' n : ℕ, thermalTerm E k n β

/-- Derivative of each term of the kth moment-generating series. -/
theorem thermal_term_derivative (E : ℕ → ℝ) (k n : ℕ)
    (β : ℝ) :
    HasDerivAt (thermalTerm E k n)
      (thermalTerm E (k+1) n β) β := by
  have hl : HasDerivAt (fun x : ℝ => -E n * x) (-E n) β := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id β).const_mul (-E n)
  have he := hl.exp
  have hm := he.const_mul ((-E n)^k)
  convert hm using 1
  · rfl
  · simp only [thermalTerm, pow_succ]
    ring

/-- Uniform bound for beta>a given nonnegative excitation energies. -/
theorem thermal_term_bound (E : ℕ → ℝ)
    (hE : ∀ n, 0 ≤ E n) (a β : ℝ) (ha : a ≤ β)
    (k n : ℕ) :
    ‖thermalTerm E k n β‖ ≤
      (E n)^k * Real.exp (-E n * a) := by
  have hdec : -E n * β ≤ -E n * a := by
    nlinarith [hE n]
  have hexp := Real.exp_le_exp.mpr hdec
  have hpow : 0 ≤ (E n)^k := pow_nonneg (hE n) _
  unfold thermalTerm
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_of_nonneg (hE n), Real.abs_exp]
  exact mul_le_mul_of_nonneg_left hexp hpow

/-- A standard convergence input: at one reference temperature,
    every energy moment has a finite Boltzmann-weighted sum. -/
def ThermalMomentSummable (E : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ k : ℕ, Summable (fun n : ℕ =>
    (E n)^k * Real.exp (-E n * a))

theorem thermal_term_summable (E : ℕ → ℝ)
    (hE : ∀ n, 0 ≤ E n) (a β : ℝ)
    (hMom : ThermalMomentSummable E a) (ha : a ≤ β)
    (k : ℕ) :
    Summable (fun n : ℕ => thermalTerm E k n β) := by
  apply Summable.of_norm_bounded (hMom k)
  intro n
  exact thermal_term_bound E hE a β ha k n

/-- ALL-ORDER differentiation under the infinite sum on beta>a.
    This proves the exact thermal trace derivative hierarchy
    given the stated spectral moment summability. -/
theorem thermal_tsum_derivative_all_orders
    (E : ℕ → ℝ) (a β : ℝ)
    (hE : ∀ n, 0 ≤ E n)
    (hMom : ThermalMomentSummable E a)
    (ha : a < β) (k : ℕ) :
    HasDerivAt (thermalSum E k)
      (thermalSum E (k+1) β) β := by
  have hs : IsPreconnected (Set.Ioi a) := isPreconnected_Ioi
  have hbase : Summable (fun n : ℕ =>
      thermalTerm E k n (a+1)) :=
    thermal_term_summable E hE a (a+1) hMom (by linarith) k
  exact hasDerivAt_tsum_of_isPreconnected
    (hMom (k+1)) isOpen_Ioi hs
    (fun n y hy => thermal_term_derivative E k n y)
    (fun n y hy => thermal_term_bound E hE a y (le_of_lt hy) (k+1) n)
    (by show a < a+1; linarith) hbase ha

/-- The first infinite-spectrum trace is a genuine differentiable function. -/
theorem infinite_partition_has_deriv
    (E : ℕ → ℝ) (a β : ℝ) (hE : ∀ n, 0 ≤ E n)
    (hMom : ThermalMomentSummable E a) (ha : a < β) :
    HasDerivAt (thermalSum E 0)
      (thermalSum E 1 β) β :=
  thermal_tsum_derivative_all_orders E a β hE hMom ha 0

/-- Exact moment-generating identity for countable spectra.
    This is an equality of convergent sums, not an asymptotic. -/
theorem infinite_mgf_exact
    (E : ℕ → ℝ) (β s : ℝ) :
    (∑' n : ℕ,
      Real.exp (-E n * β) * Real.exp (s * E n)) =
      thermalSum E 0 (β-s) := by
  unfold thermalSum thermalTerm
  simp only [pow_zero, one_mul]
  apply tsum_congr
  intro n
  rw [← Real.exp_add]
  congr 1
  ring

/-- The complex spectral return amplitude identity holds term by term. -/
theorem infinite_return_amplitude_exact
    (E : ℕ → ℝ) (β t : ℝ) :
    (∑' n : ℕ,
      Complex.exp (((-β*E n : ℝ) : ℂ)) *
        Complex.exp (-Complex.I * (((t*E n : ℝ)) : ℂ))) =
    (∑' n : ℕ,
      Complex.exp (-((β : ℂ) + Complex.I*(t : ℂ))*(E n : ℂ))) := by
  apply tsum_congr
  intro n
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

noncomputable def modelReal (A β : ℝ) : ℝ := Real.exp (A / β)
noncomputable def modelComplex (A : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((A : ℂ) / z)

/-- The high-temperature model has the advertised exact complex-time ratio.
    This is about Z_0, not about the exact original CFT. -/
theorem model_complex_ratio
    (A β t : ℝ) (hβ : β ≠ 0) :
    modelComplex A ((β : ℂ) + Complex.I*(t : ℂ)) /
      modelComplex A (β : ℂ) =
      Complex.exp ((A : ℂ) /
        ((β : ℂ) + Complex.I*(t : ℂ)) - (A : ℂ)/(β : ℂ)) := by
  simp only [modelComplex]
  rw [Complex.exp_sub]

/-- At fixed beta, equality of function VALUES does not force equality
    of DERIVATIVES. The correction is identically zero at beta0. -/
noncomputable def perturb (A β0 ε : ℝ) (β : ℝ) : ℝ :=
  modelReal A β + ε * (β - β0)

theorem perturb_same_value (A β0 ε : ℝ) :
    perturb A β0 ε β0 = modelReal A β0 := by
  simp [perturb]

theorem perturb_derivative_shift (A β0 ε d : ℝ)
    (hmodel : HasDerivAt (modelReal A) d β0) :
    HasDerivAt (perturb A β0 ε) (d + ε) β0 := by
  have he : HasDerivAt (fun β : ℝ => ε * (β-β0)) ε β0 := by
    have h := (hasDerivAt_id β0).sub_const β0
    convert h.const_mul ε using 1 <;> first | rfl | ring
  convert hmodel.add he using 1 <;> first | rfl | ring

/-- The manuscript's condition s<beta alone does NOT imply |s|<beta. -/
theorem one_sided_condition_insufficient :
    (-2 : ℝ) < 1 ∧ ¬ |(-2 : ℝ)| < 1 := by
  norm_num

end TTbarTFDInfinite
