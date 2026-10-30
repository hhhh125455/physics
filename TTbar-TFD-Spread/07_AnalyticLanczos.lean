import Mathlib

/-!
TTbar-TFD-Spread section 2: analytic Jacobi/Lanczos coefficients of
the *effective model* Z0(beta)=exp(A/beta).

The dimensionless energy is y=beta*E and u=A/beta.
The moment formula is the previously verified ALL-ORDER Lah expansion.

We check the first Jacobi steps as genuine Gram (orthogonal polynomial)
identities, not merely guessed coefficient fit.

The general-n determinant formulas are supplied as analytic definitions,
with mathematical conditions and a separate rigorous argument in the report.
-/

namespace TTbarTFDLanczos

/-- Dimensionless energy moment; exactly the Lah polynomial obtained
    from G(t)=exp(u*t/(1-t)). -/
noncomputable def M (u : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1
  else ∑ j ∈ Finset.Icc 1 k,
    ((Nat.factorial k : ℝ) / (Nat.factorial j : ℝ)) *
      (Nat.choose (k-1) (j-1) : ℝ) * u^j

theorem M0 (u : ℝ) : M u 0 = 1 := by
  simp [M]

theorem M1 (u : ℝ) : M u 1 = u := by
  simp [M]

theorem M2 (u : ℝ) : M u 2 = u^2 + 2*u := by
  simp [M, Finset.sum_Icc_succ_top]
  ring

theorem M3 (u : ℝ) : M u 3 = u^3 + 6*u^2 + 6*u := by
  simp [M, Finset.sum_Icc_succ_top]
  ring

theorem M4 (u : ℝ) :
    M u 4 = u^4 + 12*u^3 + 36*u^2 + 24*u := by
  simp [M, Finset.sum_Icc_succ_top]
  ring

theorem M5 (u : ℝ) :
    M u 5 = u^5 + 20*u^4 + 120*u^3 +
      240*u^2 + 120*u := by
  simp [M, Finset.sum_Icc_succ_top]
  ring

theorem M6 (u : ℝ) :
    M u 6 = u^6 + 30*u^5 + 300*u^4 +
      1200*u^3 + 1800*u^2 + 720*u := by
  simp [M, Finset.sum_Icc_succ_top]
  ring

/-- Gram / expectation functional applied to a polynomial represented
    by its polynomial coefficients; existence of a positive measure
    is an independent analytic fact. -/
noncomputable def expectation (u : ℝ) (p : Polynomial ℝ) : ℝ :=
  p.sum (fun k c => c * M u k)

/-- The first monic orthogonal polynomial P1(y)=y-u. -/
def P1 (u : ℝ) : Polynomial ℝ :=
  Polynomial.X - Polynomial.C u

/-- The second monic polynomial from the Gram-Schmidt recurrence. -/
def P2 (u : ℝ) : Polynomial ℝ :=
  Polynomial.X^2 - Polynomial.C (2*u+3)*Polynomial.X +
    Polynomial.C (u^2+u)

theorem mean_P1_zero (u : ℝ) : expectation u (P1 u) = 0 := by
  simp [expectation, P1, M0, M1]
  ring

theorem norm_P1_sq (u : ℝ) :
    M u 2 - 2*u*M u 1 + u^2*M u 0 = 2*u := by
  rw [M0, M1, M2]
  ring

theorem weighted_norm_P1 (u : ℝ) :
    M u 3 - 2*u*M u 2 + u^2*M u 1 =
      (u+3)*(2*u) := by
  rw [M1, M2, M3]
  ring

theorem P2_orthogonal_to_one (u : ℝ) :
    M u 2 - (2*u+3)*M u 1 +
       (u^2+u)*M u 0 = 0 := by
  rw [M0, M1, M2]
  ring

theorem P2_orthogonal_to_y (u : ℝ) :
    M u 3 - (2*u+3)*M u 2 +
       (u^2+u)*M u 1 = 0 := by
  rw [M1, M2, M3]
  ring

theorem norm_P2_sq (u : ℝ) :
    M u 4 - 2*(2*u+3)*M u 3 +
      ((2*u+3)^2+2*(u^2+u))*M u 2 -
      2*(2*u+3)*(u^2+u)*M u 1 +
      (u^2+u)^2*M u 0 = 2*u*(4*u+3) := by
  rw [M0, M1, M2, M3, M4]
  ring

theorem weighted_norm_P2 (u : ℝ) :
    M u 5 - 2*(2*u+3)*M u 4 +
      ((2*u+3)^2+2*(u^2+u))*M u 3 -
      2*(2*u+3)*(u^2+u)*M u 2 +
      (u^2+u)^2*M u 1 =
      2*u*(4*u^2+27*u+15) := by
  rw [M1, M2, M3, M4, M5]
  ring

/-- First coefficients of the MONIC Jacobi recursion in y units. -/
noncomputable def alpha0 (u : ℝ) : ℝ := u
noncomputable def alpha1 (u : ℝ) : ℝ := u+3
noncomputable def alpha2 (u : ℝ) : ℝ :=
  (4*u^2+27*u+15)/(4*u+3)
noncomputable def gamma1 (u : ℝ) : ℝ := 2*u
noncomputable def gamma2 (u : ℝ) : ℝ := 4*u+3

theorem alpha0_from_moments (u : ℝ) :
    M u 1 / M u 0 = alpha0 u := by
  rw [M0, M1]
  simp [alpha0]

theorem gamma1_from_variance (u : ℝ) :
    M u 2 - (M u 1)^2 = gamma1 u := by
  rw [M1, M2]
  ring

theorem alpha1_from_gram (u : ℝ) (hu : 0 < u) :
    (M u 3 - 2*u*M u 2 + u^2*M u 1) /
      (M u 2 - 2*u*M u 1 + u^2*M u 0) =
        alpha1 u := by
  rw [weighted_norm_P1, norm_P1_sq]
  unfold alpha1
  have hu0 : u ≠ 0 := ne_of_gt hu
  field_simp
  ring

theorem gamma2_from_gram (u : ℝ) (hu : 0 < u) :
    (2*u*(4*u+3)) / (2*u) = gamma2 u := by
  unfold gamma2
  have hu0 : u ≠ 0 := ne_of_gt hu
  field_simp
  ring

theorem alpha2_from_gram (u : ℝ) (hu : 0 < u) :
    (2*u*(4*u^2+27*u+15)) /
      (2*u*(4*u+3)) = alpha2 u := by
  unfold alpha2
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hden : 4*u+3 ≠ 0 := by positivity
  field_simp
  ring

/-- The y->E=y/beta scaling of the Jacobi recurrence. -/
noncomputable def lanczos_a (β α : ℝ) : ℝ := α / β
noncomputable def lanczos_b_sq (β γ : ℝ) : ℝ := γ / β^2

theorem physical_a0 (A β : ℝ) (hβ : β ≠ 0) :
    lanczos_a β (alpha0 (A/β)) = A/β^2 := by
  unfold lanczos_a alpha0
  field_simp [hβ]
  ring

theorem physical_b1_sq (A β : ℝ) (hβ : β ≠ 0) :
    lanczos_b_sq β (gamma1 (A/β)) = 2*A/β^3 := by
  unfold lanczos_b_sq gamma1
  field_simp [hβ]
  ring

/-- General closed but determinant-defined analytic coefficients. -/
noncomputable def Hankel (u : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => M u (i.val+j.val)

noncomputable def HankelDet (u : ℝ) (n : ℕ) : ℝ :=
  Matrix.det (Hankel u n)

/-- Hhat_n replaces last column (j=n-1) by the n-th shifted moment. -/
noncomputable def ShiftHankel (u : ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j.val + 1 = n then M u (i.val+n)
     else M u (i.val+j.val)

noncomputable def ShiftDet (u : ℝ) (n : ℕ) : ℝ :=
  Matrix.det (ShiftHankel u n)

/-- A determinantal formula at arbitrary n for Jacobi gamma_n=b_n^2. -/
noncomputable def determinantGamma (u : ℝ) (n : ℕ) : ℝ :=
  HankelDet u (n+1)*HankelDet u (n-1)/(HankelDet u n)^2

/-- A determinantal formula at arbitrary n for Jacobi alpha_n=a_n. -/
noncomputable def determinantAlpha (u : ℝ) (n : ℕ) : ℝ :=
  ShiftDet u (n+1)/HankelDet u (n+1) -
    ShiftDet u n/HankelDet u n

end TTbarTFDLanczos
