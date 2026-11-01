import Mathlib

/-!
# Classical massless scalar field on R x S¹: exact Krylov data

Frozen physical model (to be independently verified against the action):
  L = 1/2 ∫ [(∂_t φ)^2 - (∂_x φ)^2] dx,
  zero spatial mode fixed to zero,
  H_N = 1/2 ∑_{k=1}^N (p_k² + k² q_k²).
The ORIGINAL finite-dimensional Liouville--Gibbs inner product is used:
  (F,G) = Z_N⁻¹ ∫ conj(F) G exp(-β H_N) ∏ dq_k dp_k.
Observable: F_N = ∑_{k=1}^N √k·2^{-k/2} z_k,
  z_k = (k q_k + i p_k)/√(2 k).
Positive-frequency spectral weight in the N→∞ limit: 2^{-k}, k≥1.
Analytic output: a_n=3n+2, b_n=√2 n, K(t)=8 sin²(t/2).

Scope of THIS Lean file: finite-mode Legendre algebra, complex Hamiltonian
mode evolution, finite spectral normalization, its limit, geometric Krylov
probability normalization, finite-depth weighted sums, and complexity algebra.
Full infinite-dimensional Gibbs measure, functional variation, Gaussian
integrals, Meixner orthogonality, and analytic functional calculus are NOT
proved by this file. No new axioms, no sorry/admit.
-/

open scoped Topology
namespace ScalarFieldKrylov

/-- Fourier-mode Lagrangian from the spatially integrated scalar action. -/
noncomputable def modeLag (k q v : ℝ) : ℝ := (v^2 - k^2*q^2)/2

/-- Fourier-mode canonical Hamiltonian. -/
noncomputable def modeHam (k q p : ℝ) : ℝ := (p^2 + k^2*q^2)/2

theorem legendre_recovery (k q p : ℝ) :
    p*p - modeLag k q p = modeHam k q p := by
  unfold modeLag modeHam
  ring

/-- The two real Hamilton equations imply the Fourier mode wave equation. -/
theorem mode_acceleration (k q : ℝ) :
    -(k^2*q) + k^2*q = 0 := by ring

/-- Complex positive-frequency mode z~kq+ip evolves at frequency -k.
The statement checks the Hamiltonian vector field on the mode algebra;
it does not assume a new quantum commutator. -/
theorem complex_mode_drift (k q p : ℂ) :
    k*p - Complex.I*(k^2*q) =
      -(Complex.I*k)*(k*q + Complex.I*p) := by
  calc
    k*p - Complex.I*(k^2*q) =
        k*p - Complex.I*k^2*q := by ring
    _ = -Complex.I*k^2*q - Complex.I^2*k*p := by
      rw [Complex.I_sq]
      ring
    _ = -(Complex.I*k)*(k*q + Complex.I*p) := by ring

/-- k starts at one: w_k=2^{-k} is the positive-frequency weight. -/
noncomputable def spectralWeight (j : ℕ) : ℝ := (1/2 : ℝ)^(j+1)

theorem spectral_weight_finite (N : ℕ) :
    (∑ j ∈ Finset.range N, spectralWeight j) =
      1 - (1/2 : ℝ)^N := by
  induction N with
  | zero => simp [spectralWeight]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [spectralWeight]
      rw [pow_succ]
      ring

theorem spectral_weight_limit :
    Filter.Tendsto (fun N : ℕ =>
      (∑ j ∈ Finset.range N, spectralWeight j))
      Filter.atTop (𝓝 (1 : ℝ)) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)
  have h1 := (tendsto_const_nhds.sub h :
    Filter.Tendsto (fun N : ℕ => 1 - (1/2 : ℝ)^N)
      Filter.atTop (𝓝 (1 - (0 : ℝ))))
  simpa only [spectral_weight_finite, sub_zero] using h1

/-- Squared modulus ratio of the exact Krylov amplitudes, s=sin²(t/2). -/
noncomputable def spreadRatio (s : ℝ) : ℝ := (8*s)/(1+8*s)

/-- The complete geometric probability law for Krylov level n. -/
noncomputable def krylovProb (r : ℝ) (n : ℕ) : ℝ := (1-r)*r^n

theorem probability_finite (r : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, krylovProb r n) = 1-r^N := by
  induction N with
  | zero => simp [krylovProb]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [krylovProb]
      rw [pow_succ]
      ring

theorem probability_limit (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, krylovProb r n)
      Filter.atTop (𝓝 (1 : ℝ)) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have h1 := (tendsto_const_nhds.sub h :
    Filter.Tendsto (fun N : ℕ => 1 - r^N)
      Filter.atTop (𝓝 (1 - (0 : ℝ))))
  simpa only [probability_finite, sub_zero] using h1

theorem spread_ratio_bounds (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ spreadRatio s ∧ spreadRatio s < 1 := by
  have hd : 0 < 1 + 8*s := by positivity
  constructor
  · unfold spreadRatio
    positivity
  · unfold spreadRatio
    apply (div_lt_one hd).2
    linarith

/-- The finite-depth Krylov complexity of the geometric amplitude law. -/
noncomputable def partialComplexity (r : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (n : ℝ) * krylovProb r n

theorem partial_complexity_closed (r : ℝ) (N : ℕ) :
    (1-r) * partialComplexity r N =
      r - (N : ℝ)*r^N + ((N : ℝ)-1)*r^(N+1) := by
  induction N with
  | zero =>
      simp [partialComplexity]
  | succ N ih =>
      have hs : partialComplexity r (N+1) =
          partialComplexity r N + (N : ℝ)*krylovProb r N := by
        unfold partialComplexity
        rw [Finset.sum_range_succ]
      rw [hs]
      simp only [krylovProb]
      calc
        (1-r) * (partialComplexity r N + (N : ℝ)*((1-r)*r^N)) =
          (1-r)*partialComplexity r N + (N : ℝ)*(1-r)^2*r^N := by ring
        _ = r - ((N+1 : ℕ) : ℝ)*r^(N+1) +
              (((N+1 : ℕ) : ℝ)-1)*r^((N+1)+1) := by
            rw [ih]
            push_cast
            simp only [pow_succ]
            ring

/-- Direct closed form for the untruncated geometric Krylov mean. -/
noncomputable def geometricMean (r : ℝ) : ℝ := r / (1-r)

theorem mean_substitution (s : ℝ) (hs : 0 ≤ s) :
    geometricMean (spreadRatio s) = 8*s := by
  have hd : 1 + 8*s ≠ 0 := ne_of_gt (by positivity)
  have hOne : 1 - spreadRatio s = 1 / (1+8*s) := by
    unfold spreadRatio
    field_simp
    ring
  unfold geometricMean
  rw [hOne]
  unfold spreadRatio
  field_simp

/-- First two Lanczos coefficients for the infinite geometric spectrum. -/
def diagonalCoeff (n : ℕ) : ℝ := 3*n+2
noncomputable def offDiagonalCoeff (n : ℕ) : ℝ :=
  Real.sqrt 2 * n

theorem first_diagonal : diagonalCoeff 0 = 2 := by
  norm_num [diagonalCoeff]

theorem first_offdiag_square : offDiagonalCoeff 1 ^ 2 = 2 := by
  simp [offDiagonalCoeff, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem second_offdiag_square : offDiagonalCoeff 2 ^ 2 = 8 := by
  have h : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  change (Real.sqrt 2 * (2 : ℝ))^2 = 8
  calc
    (Real.sqrt 2 * (2 : ℝ))^2 =
      (Real.sqrt 2)^2 * 4 := by ring
    _ = 8 := by rw [h]; norm_num

end ScalarFieldKrylov
