import Mathlib

/-!
Finite-dimensional Lanczos-to-moment identity.

The `tridiag` matrix below uses the original off-diagonal Lanczos
coefficients bⱼ, with diagonal aⱼ = 0.  We prove that its 2n-th
spectral moment is the squared norm of the n-step Krylov vector.

This is a finite-matrix theorem, not a theorem about the large-n limit
of the infinite spectral measure.  No sorry, admit, or custom axioms.
-/

namespace JacobiMoment

noncomputable section

def tridiag {N : ℕ} (b : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (if i.val + 1 = j.val then b j else 0) +
      (if j.val + 1 = i.val then b i else 0)

theorem tridiag_symmetric {N : ℕ} (b : Fin N → ℝ) :
    ∀ i j, tridiag b i j = tridiag b j i := by
  intro i j
  change ((if i.val + 1 = j.val then b j else 0) +
      (if j.val + 1 = i.val then b i else 0)) =
    ((if j.val + 1 = i.val then b i else 0) +
      (if i.val + 1 = j.val then b j else 0))
  exact add_comm _ _

theorem symmetric_power {N : Type*} [Fintype N] [DecidableEq N]
    (J : Matrix N N ℝ) (hJ : ∀ i j, J i j = J j i) (n : ℕ) :
    ∀ i j, (J ^ n) i j = (J ^ n) j i := by
  have ht : J.transpose = J := by
    ext i j
    exact hJ j i
  have htp : (J ^ n).transpose = J ^ n := by
    rw [Matrix.transpose_pow, ht]
  intro i j
  have h := congrArg (fun (M : Matrix N N ℝ) => M j i) htp
  exact h

theorem symmetric_even_moment {N : Type*} [Fintype N] [DecidableEq N]
    (J : Matrix N N ℝ) (hJ : ∀ i j, J i j = J j i)
    (n : ℕ) (i : N) :
    (J ^ (2 * n)) i i = ∑ j, ((J ^ n) i j) ^ 2 := by
  have hp : J ^ (2 * n) = J ^ n * J ^ n := by
    rw [two_mul, pow_add]
  rw [hp, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [← symmetric_power J hJ n i j]
  ring

theorem lanczos_even_moment (N n : ℕ) (b : Fin (N + 1) → ℝ) :
    ((tridiag b) ^ (2 * n)) (0 : Fin (N + 1)) 0 =
      ∑ j, (((tridiag b) ^ n) (0 : Fin (N + 1)) j) ^ 2 := by
  exact symmetric_even_moment (tridiag b) (tridiag_symmetric b) n 0

end
end JacobiMoment
