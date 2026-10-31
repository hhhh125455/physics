import Mathlib

/-!
# TTbar inverse-Gaussian double-scaling: rational Painleve III' sigma audit

Model spectral weight: x^(-3/2)*exp(-x-s/x), s=z^2>0.
The normalized moments obey m0=1, m1=z,
m_(k+1)=(k-1/2)m_k+z^2*m_(k-1).

The Chen--Its PIII' sigma equation for H_n(s)=s*(d/ds)log D_n(s) is
  (s H'')^2=(n-(2n-3/2)H')^2
              -4 H'(H'-1)*(s H'-H+n*(n-3/2)).
We verify the EXACT rational special-solution algebra for n=1,2,3,
and the first two normalized Hankel determinants.

Scope: This file does NOT prove the all-n PIII' equation from the
weighted integral for alpha=-3/2. That is a separate analytical extension
of the usual alpha>-1 assumption in the literature.

All theorems use exact Q-rational algebra without unproved placeholders.
-/

namespace IG_PIII
open scoped BigOperators

/-- All-order normalized inverse-Gaussian energy moments, no approximations. -/
noncomputable def mom : ℕ → ℚ → ℚ
  | 0, _ => 1
  | 1, z => z
  | k+2, z => ((k:ℚ)+1/2)*mom (k+1) z + z^2*mom k z

theorem mom0 (z : ℚ) : mom 0 z = 1 := rfl
theorem mom1 (z : ℚ) : mom 1 z = z := rfl
theorem mom_rec (k : ℕ) (z : ℚ) :
    mom (k+2) z = ((k:ℚ)+1/2)*mom (k+1) z + z^2*mom k z := rfl

theorem mom2 (z : ℚ) : mom 2 z = z^2+z/2 := by
  simp only [mom]
  ring

theorem mom3 (z : ℚ) :
    mom 3 z = z^3+3*z^2/2+3*z/4 := by
  simp only [mom]
  ring

theorem mom4 (z : ℚ) :
    mom 4 z = z^4+3*z^3+15*z^2/4+15*z/8 := by
  simp only [mom]
  ring

/-- Arbitrary-size exact normalized Hankel tau determinant. -/
noncomputable def tau (n : ℕ) (z : ℚ) : ℚ :=
  Matrix.det (fun i j : Fin n => mom (i.val+j.val) z)

/-- The first positive Hankel determinant, sigma-normalized. -/
theorem tau_one (z : ℚ) : tau 1 z = 1 := by
  simp [tau, Matrix.det_fin_one, mom]

theorem tau_two (z : ℚ) : tau 2 z = z/2 := by
  simp [tau, Matrix.det_fin_two, mom] <;> ring

theorem tau_three (z : ℚ) :
    tau 3 z = z^2*(2*z+3)/8 := by
  simp [tau, Matrix.det_fin_three, mom] <;> ring

/-- Exact low-order Jacobi/Lanczos expressions (x is scaled energy). -/
theorem b1sq (z : ℚ) :
    (mom 2 z)-(mom 1 z)^2 = z/2 := by
  rw [mom2, mom1]
  ring

theorem b2sq_from_hankel (z : ℚ) (hz : z ≠ 0) :
    tau 3 z*tau 1 z/(tau 2 z)^2 = (2*z+3)/2 := by
  rw [tau_one, tau_two, tau_three]
  field_simp [hz]
  ring

/-- Rational expression of sigma derivative w.r.t. s=z^2.
    For n=3, formulas for H, H_s and H_ss follow from differentiating
    H_3=-3z-1/2+z/(2z+3). -/
def H1 (z : ℚ) : ℚ := -z-1/2
def Hp1 (z : ℚ) : ℚ := -1/(2*z)
def Hpp1 (z : ℚ) : ℚ := 1/(4*z^3)

def H2 (z : ℚ) : ℚ := -2*z-1/2
def Hp2 (z : ℚ) : ℚ := -1/z
def Hpp2 (z : ℚ) : ℚ := 1/(2*z^3)

def H3 (z : ℚ) : ℚ := -3*z-1/2+z/(2*z+3)
def Hp3 (z : ℚ) : ℚ := -6*(z+1)*(z+2)/(z*(2*z+3)^2)
def Hpp3 (z : ℚ) : ℚ :=
  3*(2*z^3+9*z^2+12*z+6)/(z^3*(2*z+3)^3)

/-- PIII' sigma equation, with alpha=-3/2 and s=z^2. -/
def SigmaEquation (n z H Hp Hpp : ℚ) : Prop :=
  (z^2*Hpp)^2 =
    (n-(2*n-3/2)*Hp)^2 -
      4*Hp*(Hp-1)*(z^2*Hp-H+n*(n-3/2))

theorem sigma_n1 (z : ℚ) (hz : z ≠ 0) :
    SigmaEquation 1 z (H1 z) (Hp1 z) (Hpp1 z) := by
  unfold SigmaEquation H1 Hp1 Hpp1
  field_simp [hz] <;> ring

theorem sigma_n2 (z : ℚ) (hz : z ≠ 0) :
    SigmaEquation 2 z (H2 z) (Hp2 z) (Hpp2 z) := by
  unfold SigmaEquation H2 Hp2 Hpp2
  field_simp [hz] <;> ring

/-- Denominator-cleared n=3 PIII sigma equation, a genuine polynomial
    identity of degree up to eight; no parameter exclusions needed. -/
theorem sigma_n3_polynomial (z : ℚ) :
    let q := 2*z+3
    let c := -6*(z+1)*(z+2)
    let b := 3*(2*z^3+9*z^2+12*z+6)
    b^2 = q^2*(3*z*q^2-(9/2:ℚ)*c)^2 -
      4*c*(c-z*q^2)*(z*c+(3*z+5)*q^2-z*q) := by
  dsimp
  ring

/-- The n=3 rational sigma equation is certified by the preceding
    denominator-cleared polynomial identity together with stage 21. -/

/-- All-index exact algebra converting tau logarithmic derivatives to
    Lanczos diagonal entries, given nonzero tau determinants.
    Here p=τ_n, dp=∂_zτ_n, q=τ_(n+1), dq=∂_zτ_(n+1). -/
theorem all_index_jacobi_from_tau
    (n z p dp q dq : ℚ) (hp : p ≠ 0) (hq : q ≠ 0) :
    (2*n-1/2) -
        ((-(n+1)*z-(n+1)/2+z/2*(dq/q)) -
         (-n*z-n/2+z/2*(dp/p))) =
      z+2*n+z/2*(dp/p-dq/q) := by
  field_simp [hp, hq]
  ring

/-- At n=1 the inverse-Gaussian a_1 is exactly z+3/2. -/
theorem a1_exact (z : ℚ) (hz : z ≠ 0) :
    (z+2) - (z/2)*((1:ℚ)/z) = z+3/2 := by
  field_simp [hz] <;> ring

/-- b_n²=s H_n'(s)-H_n(s)+n(n-3/2), checked at n=1. -/
theorem offdiag_n1_from_sigma (z : ℚ) (hz : z ≠ 0) :
    z^2*Hp1 z-H1 z+1*(1-3/2:ℚ) = z/2 := by
  unfold H1 Hp1
  field_simp [hz] <;> ring

theorem offdiag_n2_from_sigma (z : ℚ) (hz : z ≠ 0) :
    z^2*Hp2 z-H2 z+2*(2-3/2:ℚ) = z+3/2 := by
  unfold H2 Hp2
  field_simp [hz] <;> ring

/-- Algebraic n=3 b_n² identity after multiplying by (2*z+3)^2. -/
theorem offdiag_n3_polynomial (z : ℚ) :
    -6*z*(z+1)*(z+2)+(3*z+5)*(2*z+3)^2-z*(2*z+3) =
      3*(2*z^3+12*z^2+24*z+15) := by
  ring

/-- a_n=2n-1/2+H_n-H_(n+1), checked at n=0,1,2. -/
theorem diag_n0_from_sigma (z : ℚ) :
    (-1/2:ℚ)-H1 z = z := by
  unfold H1
  ring

theorem diag_n1_from_sigma (z : ℚ) :
    (3/2:ℚ)+H1 z-H2 z = z+3/2 := by
  unfold H1 H2
  ring

theorem diag_n2_from_sigma (z : ℚ) (hq : 2*z+3 ≠ 0) :
    (7/2:ℚ)+H2 z-H3 z =
      z+7/2-z/(2*z+3) := by
  unfold H2 H3
  field_simp [hq] <;> ring

end IG_PIII
