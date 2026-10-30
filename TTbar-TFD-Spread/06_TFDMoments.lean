import Mathlib

/-!
Audit of TTbar TFD manuscript lines 180--222.

Distinguish EXACT finite-spectrum statements from the MODEL
obtained by replacing the true CFT partition function with
Z0(beta) = exp(A/beta).

Exact:
* derivatives of arbitrary order of the finite spectral trace
* normalization and moment generating-function trace identity
* return amplitude spectral exponent factorization

Model:
* closed-form generating function G0(s)
* derivatives of G0
* first several explicit moments, as checks of manuscript's formula.

No claim that the entire original CFT spectrum has Z0 exactly.
-/

namespace TTbarTFDMoments

/-- The k-th UNNORMALIZED derivative of a finite-spectrum trace. -/
noncomputable def traceDerivative (N k : ℕ)
    (E : Fin N → ℝ) (β : ℝ) : ℝ :=
  ∑ j : Fin N, (-E j) ^ k * Real.exp ((-E j) * β)

/-- At k=0 this is the canonical partition sum. -/
noncomputable def finitePartition (N : ℕ)
    (E : Fin N → ℝ) (β : ℝ) : ℝ :=
  ∑ j : Fin N, Real.exp ((-E j) * β)

theorem trace_derivative_zero (N : ℕ) (E : Fin N → ℝ) (β : ℝ) :
    traceDerivative N 0 E β = finitePartition N E β := by
  simp [traceDerivative, finitePartition]

/-- This holds for ARBITRARY k: the derivative of D_k is D_(k+1).
    Thus the entire k-th derivative hierarchy is verified, not just
    the first few moments. -/
theorem trace_derivative_succ (N k : ℕ) (E : Fin N → ℝ) (β : ℝ) :
    HasDerivAt (traceDerivative N k E)
      (traceDerivative N (k + 1) E β) β := by
  have hs : HasDerivAt
      (fun x : ℝ => ∑ j : Fin N,
        (-E j) ^ k * Real.exp ((-E j) * x))
      (∑ j : Fin N,
        (-E j) ^ (k + 1) * Real.exp ((-E j) * β)) β := by
    apply HasDerivAt.fun_sum
    intro j hj
    have hl : HasDerivAt (fun x : ℝ => (-E j) * x) (-E j) β :=
      (hasDerivAt_id β).const_mul (-E j)
    have he := hl.exp
    have hm := he.const_mul ((-E j) ^ k)
    convert hm using 1 <;> first | rfl | ring
  exact hs

/-- Any nonempty finite spectrum has strictly positive thermal trace. -/
theorem finite_partition_pos (N : ℕ) (E : Fin (N+1) → ℝ) (β : ℝ) :
    0 < finitePartition (N+1) E β := by
  unfold finitePartition
  positivity

/-- The normalized state weights sum to one. -/
theorem tfd_weights_normalized (N : ℕ)
    (E : Fin (N+1) → ℝ) (β : ℝ) :
    (∑ j : Fin (N+1),
      Real.exp ((-E j)*β) / finitePartition (N+1) E β) = 1 := by
  rw [← Finset.sum_div]
  unfold finitePartition
  exact div_self (ne_of_gt (by positivity))

/-- Finite-spectrum TFD energy moments are precisely normalized
    weighted spectral sums; the (-1)^k sign cancels the kth derivative. -/
theorem moments_from_derivatives (N k : ℕ)
    (E : Fin (N+1) → ℝ) (β : ℝ) :
    (-1 : ℝ) ^ k * traceDerivative (N+1) k E β /
      finitePartition (N+1) E β =
    (∑ j : Fin (N+1),
      (E j) ^ k * Real.exp ((-E j)*β)) /
      finitePartition (N+1) E β := by
  congr 1
  unfold traceDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_assoc]
  have h : (-1 : ℝ)^k * (-E j)^k = (E j)^k := by
    rw [← mul_pow]
    ring
  rw [h]

/-- Exact finite-spectrum moment-generating function identity
    G(s)=Z(beta-s)/Z(beta), for arbitrary energy levels. -/
theorem finite_mgf_identity (N : ℕ) (E : Fin (N+1) → ℝ)
    (β s : ℝ) :
    (∑ j : Fin (N+1),
      Real.exp ((-E j)*β) * Real.exp (s*E j)) /
      finitePartition (N+1) E β =
    finitePartition (N+1) E (β-s) /
      finitePartition (N+1) E β := by
  congr 1
  unfold finitePartition
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Real.exp_add]
  congr 1
  ring

/-- Trace identity with characteristic amplitude exp(-i E t). -/
theorem finite_return_amplitude (N : ℕ) (E : Fin (N+1) → ℝ)
    (β t : ℝ) :
    (∑ j : Fin (N+1),
      Complex.exp ((((-β * E j) : ℝ) : ℂ)) *
        Complex.exp (-Complex.I * ((t * E j : ℝ) : ℂ))) =
    (∑ j : Fin (N+1),
      Complex.exp (-((β : ℂ) + Complex.I*(t : ℂ)) * (E j : ℂ))) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

noncomputable def modelPartition (A β : ℝ) : ℝ :=
  Real.exp (A / β)

noncomputable def modelGenerating (A β s : ℝ) : ℝ :=
  modelPartition A (β-s) / modelPartition A β

/-- Exact generating-function expression for the LEADING-ORDER model. -/
theorem model_generating_exp (A β s : ℝ) :
    modelGenerating A β s =
      Real.exp (A / (β-s) - A / β) := by
  unfold modelGenerating modelPartition
  rw [Real.exp_sub]

theorem model_generating_rational (A β s : ℝ)
    (hβ : β ≠ 0) (hs : β-s ≠ 0) :
    modelGenerating A β s =
      Real.exp (A*s / (β*(β-s))) := by
  rw [model_generating_exp]
  congr 1
  field_simp [hβ, hs]
  ring

theorem model_generating_normalized (A β : ℝ) :
    modelGenerating A β 0 = 1 := by
  simp [modelGenerating, modelPartition]

/-- At every finite beta, the model has an honest first derivative. -/
theorem model_generating_derivative (A β s : ℝ)
    (h : β-s ≠ 0) :
    HasDerivAt (modelGenerating A β)
      (modelGenerating A β s * A / (β-s)^2) s := by
  have hl : HasDerivAt (fun x : ℝ => β-x) (-1) s := by
    convert (hasDerivAt_id s).neg.const_add β using 1 <;> ring
  have hi := hl.inv h
  have hm := hi.const_mul A
  have hex := hm.exp
  have hd : HasDerivAt (fun x : ℝ =>
      Real.exp (A / (β-x) - A / β))
      (Real.exp (A / (β-s) - A / β) * (A / (β-s)^2)) s := by
    have hconst : HasDerivAt (fun x : ℝ => A / (β-x) - A / β)
      (A / (β-s)^2) s := by
      convert hm.sub_const (A / β) using 1 <;> first | rfl | ring
    simpa only [Function.comp_def] using hconst.exp
  convert hd using 1 <;> first | rfl | rw [model_generating_exp] | ring

/-- The model moment polynomial for each fixed k, written as a finite sum.
    The manuscript's expression requires k>=1 and separate m_0=1. -/
noncomputable def modelMoment (k : ℕ) (A β : ℝ) : ℝ :=
  if k = 0 then 1 else
    ∑ j ∈ Finset.Icc 1 k,
      ((Nat.factorial k : ℝ) / (Nat.factorial j : ℝ)) *
       (Nat.choose (k-1) (j-1) : ℝ) * A^j / β^(k+j)

theorem model_moment_zero (A β : ℝ) : modelMoment 0 A β = 1 := by
  simp [modelMoment]

theorem model_moment_one (A β : ℝ) :
    modelMoment 1 A β = A / β^2 := by
  simp [modelMoment]

theorem model_moment_two (A β : ℝ) :
    modelMoment 2 A β = A^2 / β^4 + 2*A / β^3 := by
  simp [modelMoment, Finset.sum_Icc_succ_top]
  ring

theorem model_moment_three (A β : ℝ) :
    modelMoment 3 A β =
       A^3/β^6 + 6*A^2/β^5 + 6*A/β^4 := by
  simp [modelMoment, Finset.sum_Icc_succ_top]
  ring

end TTbarTFDMoments
