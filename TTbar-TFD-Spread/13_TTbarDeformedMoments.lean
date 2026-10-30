import Mathlib

/-!
# Double-trace TTbar TFD moment-generating model

The formula for log Z is the leading large-c, high-temperature saddle;
none of the theorems claims it equals the finite-c CFT partition function.

We verify:
* an exact normalized generating-function identity at arbitrary shift s;
* the algebraic quadratic equation obeyed by log Z;
* an exact arbitrary-s quadratic equation for log G(s);
* the cumulant recursion at orders 1--4 in the model, with explicit forms;
* the first Jacobi/Lanczos variance identity.

The all-order analytic Taylor coefficient extraction is not yet a Lean
theorem in this file; it is explained separately in the research note.
-/

namespace TTbarDeformedMoments

noncomputable def logZ (μ A β : ℝ) : ℝ :=
  (β - Real.sqrt (β^2 - 4*μ*A)) / (2*μ)

noncomputable def Z (μ A β : ℝ) : ℝ :=
  Real.exp (logZ μ A β)

noncomputable def G (μ A β s : ℝ) : ℝ :=
  Z μ A (β-s) / Z μ A β

theorem partition_positive (μ A β : ℝ) : 0 < Z μ A β := by
  simp [Z]

theorem generating_normalized (μ A β : ℝ) :
    G μ A β 0 = 1 := by
  simp [G, Z]

theorem generating_exp (μ A β s : ℝ) :
    G μ A β s =
      Real.exp (logZ μ A (β-s) - logZ μ A β) := by
  simp only [G, Z, Real.exp_sub]

theorem generating_explicit (μ A β s : ℝ) :
    G μ A β s =
      Real.exp ((-s + Real.sqrt (β^2 - 4*μ*A) -
        Real.sqrt ((β-s)^2 - 4*μ*A)) / (2*μ)) := by
  rw [generating_exp]
  congr 1
  unfold logZ
  ring

/-- The quadratic equation for the high-temperature free energy. -/
theorem logZ_quadratic (μ A β : ℝ)
    (hμ : μ ≠ 0) (hdisc : 0 ≤ β^2 - 4*μ*A) :
    β*logZ μ A β - μ*(logZ μ A β)^2 = A := by
  have hs : (Real.sqrt (β^2 - 4*μ*A))^2 = β^2 - 4*μ*A :=
    Real.sq_sqrt hdisc
  have halg (d : ℝ) :
      β*((β-d)/(2*μ)) - μ*((β-d)/(2*μ))^2 =
        (β^2-d^2)/(4*μ) := by
    field_simp [hμ]
    <;> ring
  unfold logZ
  rw [halg, hs]
  field_simp [hμ]
  <;> ring

/-- The quantity β - 2μ logZ is the discriminant square root. -/
theorem root_relation (μ A β : ℝ) (hμ : μ ≠ 0) :
    Real.sqrt (β^2 - 4*μ*A) = β-2*μ*logZ μ A β := by
  unfold logZ
  field_simp [hμ]
  <;> ring

/-- Quadratic-branch subtraction, valid for arbitrary shift s.
    Here f=logZ(β), g=logZ(β-s), d=β-2μ f. -/
theorem shifted_quadratic_identity
    (μ A β s f g d : ℝ)
    (hf : β*f - μ*f^2 = A)
    (hg : (β-s)*g - μ*g^2 = A)
    (hd : d = β-2*μ*f) :
    d*(g-f) = s*g + μ*(g-f)^2 := by
  have he :
      d*(g-f) - s*g - μ*(g-f)^2 =
        ((β-s)*g - μ*g^2) - (β*f - μ*f^2) := by
    rw [hd]
    ring
  rw [hg, hf] at he
  linarith

/-- Core nonperturbative functional identity for K(s)=log G(s). -/
theorem log_generator_implicit (μ A β s : ℝ)
    (hμ : μ ≠ 0)
    (hβ : 0 ≤ β^2 - 4*μ*A)
    (hshift : 0 ≤ (β-s)^2 - 4*μ*A) :
    let F := logZ μ A β
    let K := logZ μ A (β-s) - F
    let d := Real.sqrt (β^2 - 4*μ*A)
    d*K = s*(F+K) + μ*K^2 := by
  dsimp
  have hf := logZ_quadratic μ A β hμ hβ
  have hg := logZ_quadratic μ A (β-s) hμ hshift
  have hd := root_relation μ A β hμ
  have h := shifted_quadratic_identity μ A β s
    (logZ μ A β) (logZ μ A (β-s))
    (Real.sqrt (β^2 - 4*μ*A)) hf hg hd
  convert h using 1 <;> ring

noncomputable def cumulantOne (μ β d : ℝ) : ℝ :=
  (β/d-1)/(2*μ)

noncomputable def cumulantTwo (A d : ℝ) : ℝ :=
  2*A/d^3

noncomputable def cumulantThree (A β d : ℝ) : ℝ :=
  6*A*β/d^5

noncomputable def cumulantFour (μ A β d : ℝ) : ℝ :=
  24*A*(β^2+μ*A)/d^7

theorem cumulant_first_quadratic (μ β d : ℝ)
    (hμ : μ ≠ 0) (hd : d ≠ 0) :
    d*cumulantOne μ β d = (β-d)/(2*μ) := by
  unfold cumulantOne
  field_simp [hμ, hd]
  <;> ring

/-- The n=2 cumulant recurrence, under the discriminant equation. -/
theorem cumulant_second_quadratic (μ A β d : ℝ)
    (hμ : μ ≠ 0) (hd : d ≠ 0)
    (hroot : d^2 = β^2 - 4*μ*A) :
    d*cumulantTwo A d =
      2*cumulantOne μ β d +
        2*μ*(cumulantOne μ β d)^2 := by
  unfold cumulantTwo cumulantOne
  field_simp [hμ, hd]
  nlinarith [hroot]

theorem cumulant_third_quadratic (μ A β d : ℝ)
    (hμ : μ ≠ 0) (hd : d ≠ 0) :
    d*cumulantThree A β d =
      3*cumulantTwo A d +
        6*μ*cumulantOne μ β d*cumulantTwo A d := by
  unfold cumulantOne cumulantTwo cumulantThree
  field_simp [hμ, hd]
  <;> ring

theorem cumulant_fourth_quadratic (μ A β d : ℝ)
    (hμ : μ ≠ 0) (hd : d ≠ 0) :
    d*cumulantFour μ A β d =
      4*cumulantThree A β d +
        8*μ*cumulantOne μ β d*cumulantThree A β d +
        6*μ*(cumulantTwo A d)^2 := by
  unfold cumulantOne cumulantTwo cumulantThree cumulantFour
  field_simp [hμ, hd]
  <;> ring

/-- Universal Bell-polynomial conversion from first cumulants to moments. -/
theorem moment_second_variance (k₁ k₂ : ℝ) :
    (k₁^2 + k₂) - k₁^2 = k₂ := by
  ring

theorem initial_lanczos_variance (k₁ k₂ : ℝ) :
    (let m₁ : ℝ := k₁
     let m₂ : ℝ := k₁^2 + k₂
     m₂ - m₁^2) = k₂ := by
  dsimp
  ring

theorem cumulant_two_pos (A d : ℝ) (hA : 0 < A) (hd : 0 < d) :
    0 < cumulantTwo A d := by
  unfold cumulantTwo
  positivity

end TTbarDeformedMoments
