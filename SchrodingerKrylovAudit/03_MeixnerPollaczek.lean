import Mathlib

/-!
# Exact solvability of the asymmetric two-sided spectrum (4.9)

Matching to Meixner–Pollaczek polynomials with lambda=1/2,
phi=pi*a/(a+b), and x=(a+b)*omega/(2*pi), produces exact
Lanczos data, without a finite-n fit.

The polynomial recurrence is explicitly a hypothesis: this file
checks its transformation to the physical omega-coordinate, not
its independent orthogonality from the Wightman measure.
-/

namespace SchrodingerKrylovAudit

noncomputable def mpDiagonal (s sn cs : ℝ) (n : ℕ) : ℝ :=
  -(2 * Real.pi / s) * ((n : ℝ) + 1 / 2) * (cs / sn)

noncomputable def mpOffDiagonal (s sn : ℝ) (n : ℕ) : ℝ :=
  Real.pi * (n : ℝ) / (s * sn)

/-- Arbitrary-n transformation of the MP recurrence to physical frequency. -/
theorem mp_recurrence_rescaled
    (s sn cs x pprev pcur pnext : ℝ) (n : ℕ)
    (hs : s ≠ 0) (hsn : sn ≠ 0)
    (hrec : ((n : ℝ) + 1) * pnext -
      2 * (x * sn + ((n : ℝ) + 1 / 2) * cs) * pcur +
      (n : ℝ) * pprev = 0) :
    (2 * Real.pi * x / s) * pcur =
      mpOffDiagonal s sn n * pprev +
      mpDiagonal s sn cs n * pcur +
      mpOffDiagonal s sn (n + 1) * pnext := by
  unfold mpDiagonal mpOffDiagonal
  push_cast
  field_simp [hs, hsn]
  linear_combination (-Real.pi) * hrec

noncomputable def mpAlpha (s sn : ℝ) : ℝ := Real.pi / (s * sn)
noncomputable def mpGamma (s sn cs : ℝ) : ℝ := -2 * Real.pi * cs / (s * sn)

theorem mp_gamma_alpha_relation (s sn cs : ℝ) :
    (mpGamma s sn cs) ^ 2 = 4 * (mpAlpha s sn) ^ 2 * cs ^ 2 := by
  unfold mpGamma mpAlpha
  ring

/-- Exact SL2 discriminant of the MP model. -/
theorem mp_SL2_gap (s sn cs : ℝ) (hs : s ≠ 0) (hsn : sn ≠ 0)
    (htrig : sn ^ 2 + cs ^ 2 = 1) :
    4 * (mpAlpha s sn) ^ 2 - (mpGamma s sn cs) ^ 2 =
      4 * (Real.pi / s) ^ 2 := by
  rw [mp_gamma_alpha_relation]
  have heq : 1 - cs ^ 2 = sn ^ 2 := by linarith
  calc
    4 * (mpAlpha s sn) ^ 2 - 4 * (mpAlpha s sn) ^ 2 * cs ^ 2 =
      4 * (mpAlpha s sn) ^ 2 * (1 - cs ^ 2) := by ring
    _ = 4 * (mpAlpha s sn) ^ 2 * sn ^ 2 := by rw [heq]
    _ = 4 * (Real.pi / s) ^ 2 := by
        unfold mpAlpha
        field_simp [hs, hsn]

/-- The SL2 complexity formula reduces to a single hyperbolic sine. -/
theorem mp_complexity_factor (s sn cs t : ℝ) (hs : s ≠ 0)
    (hsn : sn ≠ 0) (htrig : sn ^ 2 + cs ^ 2 = 1) :
    (1 / (1 - cs ^ 2)) *
      Real.sinh (mpAlpha s sn * t * sn) ^ 2 =
      (1 / sn ^ 2) * Real.sinh (Real.pi * t / s) ^ 2 := by
  have heq : 1 - cs ^ 2 = sn ^ 2 := by linarith
  rw [heq]
  have harg : mpAlpha s sn * t * sn = Real.pi * t / s := by
    unfold mpAlpha
    field_simp [hs, hsn]
  rw [harg]

theorem mp_off_exact_line (s sn : ℝ) (n : ℕ) :
    mpOffDiagonal s sn n = (n : ℝ) * mpAlpha s sn := by
  unfold mpOffDiagonal mpAlpha
  ring

theorem mp_diag_exact_line (s sn cs : ℝ) (n : ℕ) :
    mpDiagonal s sn cs n = mpGamma s sn cs * ((n : ℝ) + 1 / 2) := by
  unfold mpDiagonal mpGamma
  ring

end SchrodingerKrylovAudit
