import Mathlib

/-!
Strengthening the TFD thermal trace argument:
1. Summability of Z at ONE reference beta0 implies summability
   of every fixed Boltzmann energy moment at every beta > beta0.
2. The complex-time return-amplitude series is absolutely summable
   whenever the real thermal trace is, and its norm is controlled
   by the real thermal trace.

These are mathematical implications with explicit hypotheses,
not a proof of CFT modular invariance or the Cardy spectrum.
-/

namespace TTbarTFDOneTrace

/-- An energy polynomial is exponentially dominated at any strictly
    larger inverse temperature, using the rigorous inequality
    x^k/k! <= exp(x) for x >= 0. -/
theorem energy_polynomial_exponential_bound
    (E a β : ℝ) (k : ℕ)
    (hE : 0 ≤ E) (hβ : a < β) :
    E ^ k * Real.exp (-E * β) ≤
      ((Nat.factorial k : ℝ) / (β-a)^k) *
        Real.exp (-E * a) := by
  let δ : ℝ := β-a
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδk : 0 < δ^k := pow_pos hδ _
  have hfac : 0 < (Nat.factorial k : ℝ) := by positivity
  have hx : 0 ≤ δ*E := mul_nonneg (le_of_lt hδ) hE
  have hh := Real.pow_div_factorial_le_exp (δ*E) hx k
  have hp : (δ*E)^k ≤ (Nat.factorial k : ℝ) * Real.exp (δ*E) :=
    (div_le_iff₀ hfac).mp hh
  have heq : Real.exp (δ*E) * Real.exp (-E*β) =
      Real.exp (-E*a) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [δ]
    ring
  have hb :
      (E^k * Real.exp (-E*β)) * δ^k ≤
        (Nat.factorial k : ℝ) * Real.exp (-E*a) := by
    calc
      (E^k * Real.exp (-E*β)) * δ^k =
          (δ*E)^k * Real.exp (-E*β) := by ring
      _ ≤ ((Nat.factorial k : ℝ) * Real.exp (δ*E)) *
          Real.exp (-E*β) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
      _ = (Nat.factorial k : ℝ) * Real.exp (-E*a) := by
        rw [mul_assoc, heq]
  have hbound := (le_div_iff₀ hδk).mpr hb
  dsimp [δ] at hbound ⊢
  calc
    E^k * Real.exp (-E*β) ≤
        (Nat.factorial k : ℝ) * Real.exp (-E*a) /
          (β-a)^k := hbound
    _ = ((Nat.factorial k : ℝ) / (β-a)^k) *
          Real.exp (-E*a) := by ring

/-- ONE convergent thermal trace at a implies convergence of ALL
    finite-order energy moments at every strictly larger beta. -/
theorem all_moments_from_one_partition
    (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n)
    (a β : ℝ) (hβ : a < β)
    (hbase : Summable (fun n : ℕ => Real.exp (-E n*a))) :
    ∀ k : ℕ,
      Summable (fun n : ℕ => (E n)^k * Real.exp (-E n*β)) := by
  intro k
  let C : ℝ := (Nat.factorial k : ℝ) / (β-a)^k
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound : ∀ n : ℕ,
      (E n)^k * Real.exp (-E n*β) ≤
        C * Real.exp (-E n*a) := by
    intro n
    exact energy_polynomial_exponential_bound
      (E n) a β k (hE n) hβ
  have hs : Summable (fun n : ℕ => C * Real.exp (-E n*a)) :=
    hbase.mul_left C
  exact hs.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg (hE n) k)
      (Real.exp_nonneg _)) hbound

/-- The absolute value of the complex thermal kernel is exactly
    its (positive) real Boltzmann factor. -/
theorem complex_boltzmann_norm (E β t : ℝ) :
    ‖Complex.exp (-((β : ℂ) + Complex.I*(t : ℂ)) * (E : ℂ))‖ =
      Real.exp (-E*β) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.add_re]
  ring

/-- Convergence of a single trace at a carries over to beta > a. -/
theorem thermal_trace_summable_later
    (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n)
    (a β : ℝ) (hβ : a ≤ β)
    (hbase : Summable (fun n : ℕ => Real.exp (-E n*a))) :
    Summable (fun n : ℕ => Real.exp (-E n*β)) := by
  apply hbase.of_nonneg_of_le
  · intro n
    exact (Real.exp_nonneg _)
  · intro n
    apply Real.exp_monotone
    nlinarith [hE n]

/-- For any REAL t, the complex return-amplitude trace converges
    absolutely. The real beta, not the complex time, sets convergence. -/
theorem complex_return_summable
    (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n)
    (a β t : ℝ) (hβ : a ≤ β)
    (hbase : Summable (fun n : ℕ => Real.exp (-E n*a))) :
    Summable (fun n : ℕ =>
      Complex.exp (-((β : ℂ) + Complex.I*(t : ℂ))*(E n : ℂ))) := by
  have hreal := thermal_trace_summable_later E hE a β hβ hbase
  have hnorm :
      Summable (fun n : ℕ =>
        ‖Complex.exp (-((β : ℂ) + Complex.I*(t : ℂ))*(E n : ℂ))‖) := by
    simpa only [complex_boltzmann_norm] using hreal
  exact hnorm.of_norm

end TTbarTFDOneTrace
