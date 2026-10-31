import Mathlib

/-!
# TTbar Lanczos: exact finite positive spectral-measure algebra

For any number M of quadrature nodes, real nodes x_i and positive weights w_i,
prove the exact weighted spectral inner product properties, the two projection
identities, and the 3-term Lanczos residual orthogonality formulas.

This file proves universal algebraic properties used by the 1000-step
numerical algorithm. It does NOT claim that floating-point quadrature has
zero error, nor that 1000 continuum Lanczos coefficients are interval-certified.
-/

namespace TTbarLanczosMeasure

open scoped BigOperators

noncomputable def wdot {M : ℕ} (w p q : Fin M → ℝ) : ℝ :=
  ∑ i : Fin M, w i * p i * q i

noncomputable def diag {M : ℕ} (x q : Fin M → ℝ) : Fin M → ℝ :=
  fun i => x i * q i

noncomputable def resid {M : ℕ} (x : Fin M → ℝ)
    (a b : ℝ) (p q : Fin M → ℝ) : Fin M → ℝ :=
  fun i => (x i - a)*q i - b*p i

/-- Weighted scalar product is symmetric at arbitrary matrix size. -/
theorem wdot_symm {M : ℕ} (w p q : Fin M → ℝ) :
    wdot w p q = wdot w q p := by
  unfold wdot
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Multiplication by a real diagonal energy operator is symmetric. -/
theorem diag_symm {M : ℕ} (w x p q : Fin M → ℝ) :
    wdot w (diag x p) q = wdot w p (diag x q) := by
  unfold wdot diag
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The weighted squared norm is nonnegative at every finite dimension. -/
theorem wdot_self_nonneg {M : ℕ} (w q : Fin M → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    0 ≤ wdot w q q := by
  unfold wdot
  apply Finset.sum_nonneg
  intro i hi
  have h : 0 ≤ w i * (q i)^2 := mul_nonneg (hw i) (sq_nonneg _)
  simpa only [pow_two, mul_assoc] using h

/-- The Lanczos residual identity against the current orthonormal vector. -/
theorem resid_dot_current {M : ℕ} (w x p q : Fin M → ℝ) (a b : ℝ) :
    wdot w (resid x a b p q) q =
      wdot w (diag x q) q - a*wdot w q q - b*wdot w p q := by
  simp only [wdot, resid, diag]
  calc
    (∑ i : Fin M, w i * ((x i - a)*q i - b*p i)*q i)
        = ∑ i : Fin M,
          (w i*(x i*q i)*q i - a*(w i*q i*q i) -
            b*(w i*p i*q i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = (∑ i : Fin M, w i*(x i*q i)*q i) -
          a*(∑ i : Fin M, w i*q i*q i) -
          b*(∑ i : Fin M, w i*p i*q i) := by
            simp only [Finset.sum_sub_distrib, Finset.mul_sum]

/-- The residual is orthogonal to q when q is normalized and a is
    the Jacobi diagonal coefficient. -/
theorem resid_orth_current {M : ℕ} (w x p q : Fin M → ℝ)
    (a b : ℝ)
    (hqq : wdot w q q = 1)
    (hpq : wdot w p q = 0)
    (ha : a = wdot w (diag x q) q) :
    wdot w (resid x a b p q) q = 0 := by
  rw [resid_dot_current, hqq, hpq, ha]
  ring

/-- The exact projection identity against the preceding vector. -/
theorem resid_dot_previous {M : ℕ} (w x p q : Fin M → ℝ) (a b : ℝ) :
    wdot w (resid x a b p q) p =
      wdot w (diag x q) p - a*wdot w q p - b*wdot w p p := by
  simp only [wdot, resid, diag]
  calc
    (∑ i : Fin M, w i * ((x i - a)*q i - b*p i)*p i)
        = ∑ i : Fin M,
          (w i*(x i*q i)*p i - a*(w i*q i*p i) -
            b*(w i*p i*p i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = (∑ i : Fin M, w i*(x i*q i)*p i) -
          a*(∑ i : Fin M, w i*q i*p i) -
          b*(∑ i : Fin M, w i*p i*p i) := by
            simp only [Finset.sum_sub_distrib, Finset.mul_sum]

/-- Orthogonality against p follows from the preceding off-diagonal b. -/
theorem resid_orth_previous {M : ℕ} (w x p q : Fin M → ℝ)
    (a b : ℝ)
    (hpp : wdot w p p = 1)
    (hqp : wdot w q p = 0)
    (hb : b = wdot w (diag x q) p) :
    wdot w (resid x a b p q) p = 0 := by
  rw [resid_dot_previous, hpp, hqp, hb]
  ring

/-- If the residual norm is positive, normalizing by its square root
    gives a unit vector; this is the mathematical b_(n+1) update. -/
theorem next_vector_normalized {M : ℕ} (w r : Fin M → ℝ)
    (hnorm : 0 < wdot w r r) :
    let b := Real.sqrt (wdot w r r)
    wdot w (fun i => r i / b) (fun i => r i / b) = 1 := by
  dsimp
  have hb : Real.sqrt (wdot w r r) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnorm)
  have hs := Real.sq_sqrt hnorm.le
  unfold wdot at *
  calc
    (∑ i : Fin M,
      w i * (r i / Real.sqrt (∑ j : Fin M, w j*r j*r j)) *
        (r i / Real.sqrt (∑ j : Fin M, w j*r j*r j))) =
      (∑ i : Fin M, w i*r i*r i) /
        (Real.sqrt (∑ i : Fin M, w i*r i*r i))^2 := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i hi
          field_simp [hb]
    _ = 1 := by rw [hs]; exact div_self (ne_of_gt hnorm)

/-- Positivity of the Hagedorn gap is a genuine domain requirement. -/
theorem hagedorn_gap_pos (beta betaH : ℝ) (h : betaH < beta) :
    0 < beta-betaH := by linarith

end TTbarLanczosMeasure
