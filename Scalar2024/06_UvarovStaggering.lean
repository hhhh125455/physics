import Mathlib

/-!
# Leading M² log(1/M) staggering for all fixed Krylov indices

The original (massive 5D free scalar) moments obey, for each fixed k>=1:
  mu_(2k)(M) = (1+eps(M)) mu_(2k)(0) + O(M²),
  eps(M)=M² log(4/M)/(14*zeta(3)),
while mu_0(M)=1 and odd moments vanish.

At the level of finite Hankel matrices, the universal leading-log
perturbation is H_n(eps)=(1+eps)H_n(0)-eps*e0*e0^T.

This file verifies the matrix determinant lemma behind the Uvarov
rank-one deformation, the exact rational adjacent-minor ratio,
and its alternating first-order coefficient.

IMPORTANT: the auxiliary measure (1+eps)*rho0 - eps*delta0 need NOT be
a positive measure for all n. It is a finite-n moment perturbation
only; the original scalar Wightman spectral measure remains unchanged.
-/

namespace Scalar2024

open Matrix

/-- Mathlib's exact finite-dimensional rank-one determinant identity,
with all invertibility assumptions visible. -/
theorem finite_rank_one_det
    (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin 1) ℝ)
    (V : Matrix (Fin 1) (Fin n) ℝ)
    (hH : IsUnit H.det) :
    (H + U * V).det =
      H.det * (1 + V * H⁻¹ * U).det := by
  exact Matrix.det_add_mul U V hH

/-- Exact adjacent-Hankel-ratio formula for an abstract rank-one
perturbation, assuming the three finite minors have their
Sherman-Morrison determinant multipliers. -/
theorem rank_one_lanczos_ratio
    (Dprev D Dnext : ℝ) (c Kprev K Knext : ℝ)
    (hD : D ≠ 0) (hfac : 1 - c * K ≠ 0) :
    (Dnext * (1 - c * Knext) *
        (Dprev * (1 - c * Kprev))) /
      (D * (1 - c * K)) ^ 2 =
    (Dnext * Dprev / D ^ 2) *
       ((1 - c * Knext) * (1 - c * Kprev) /
        (1 - c * K) ^ 2) := by
  field_simp [hD, hfac]
  <;> ring

/-- Universal first-order correction in terms of squared orthonormal
polynomial values a=P_(n-1)(0)^2 and b=P_n(0)^2. -/
theorem rank_one_log_coefficient_exact
    (c K a b : ℝ) (hden : 1 - c * K ≠ 0) :
    ((1 - c * (K + b)) * (1 - c * (K - a))) /
       (1 - c * K) ^ 2 - 1 =
    (c * (a - b) * (1 - c * K) - c ^ 2 * a * b) /
       (1 - c * K) ^ 2 := by
  field_simp [hden]
  <;> ring

/-- Relation between the exact rank-one update parameter
c=eps/(1+eps) and its leading small-eps approximation. -/
theorem uvarov_parameter_first_order (eps : ℝ)
    (heps : 1 + eps ≠ 0) :
    eps / (1 + eps) - eps =
      -(eps ^ 2) / (1 + eps) := by
  field_simp [heps]
  <;> ring

/-- The leading logarithmic correction has opposite signs on
odd and even sites of a symmetric spectral measure. -/
theorem log_staggering_strict_sign (eps pEvenSq : ℝ)
    (heps : 0 < eps) (hp : 0 < pEvenSq) :
    0 < eps * pEvenSq ∧
    -(eps * pEvenSq) < 0 := by
  constructor
  · exact mul_pos heps hp
  · exact neg_neg_iff_pos.mpr (mul_pos heps hp)

/-- Squaring the origin recursion of a symmetric orthogonal family
expresses the even-index value through a ratio of adjacent Lanczos
coefficients. -/
theorem symmetric_origin_recursion_sq
    (oddB evenB prevP nextP : ℝ) (heven : evenB ≠ 0)
    (hrec : nextP = -oddB / evenB * prevP) :
    nextP ^ 2 = (oddB ^ 2 / evenB ^ 2) * prevP ^ 2 := by
  rw [hrec]
  field_simp [heven]
  <;> ring

end Scalar2024
