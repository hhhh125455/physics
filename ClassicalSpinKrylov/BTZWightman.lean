import Mathlib

/-!
# BTZ Wightman moments and the inner-horizon fingerprint

Frozen physical starting point (NOT established in this Lean file):
  C(t) = cosh(alphaPlus*t)^(-2*h) * cosh(alphaMinus*t)^(-2*h)
with x=alphaPlus^2, y=alphaMinus^2 and h>0.
The analytic Taylor coefficients mu2, mu4 are calculated independently.

This file rigorously checks only the algebraic translation
  (mu2,mu4) -> (b1^2,b2^2) -> fingerprint -> rotating BTZ radii.
It does NOT prove the bulk/boundary Wightman correspondence,
the Taylor expansion of C, nor the complete Krylov evolution.
No new axioms or proof holes are used.
-/

namespace BTZWightman

def mu2 (h x y : ℝ) : ℝ :=
  2 * h * (x + y)

def mu4 (h x y : ℝ) : ℝ :=
  4 * h * (x ^ 2 + y ^ 2) + 12 * h ^ 2 * (x + y) ^ 2

noncomputable def b2Sq (h x y : ℝ) : ℝ :=
  4 * h * (x + y) + 2 * (x ^ 2 + y ^ 2) / (x + y)

noncomputable def fingerprint (x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2) / (x + y) ^ 2

/-- The first two spectral moments of a symmetric Jacobi chain determine b1,b2. -/
theorem moments_lanczos (h x y : ℝ) (hs : x + y ≠ 0) :
    mu4 h x y = (mu2 h x y) ^ 2 + mu2 h x y * b2Sq h x y := by
  unfold mu4 mu2 b2Sq
  field_simp [hs]
  ring

/-- Extract a dimensionless Lanczos fingerprint; h must be nonzero. -/
theorem fingerprint_from_lanczos (h x y : ℝ)
    (hh : h ≠ 0) (hs : x + y ≠ 0) :
    h * (b2Sq h x y / mu2 h x y - 2) = fingerprint x y := by
  unfold b2Sq mu2 fingerprint
  have hd : 2 * h * (x + y) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hh) hs
  field_simp [hh, hs, hd]
  ring

/-- Outer radius r, inner radius s; their overall length scale cancels. -/
theorem horizon_fingerprint (r s : ℝ) (h0 : r ^ 2 + s ^ 2 ≠ 0) :
    fingerprint ((r + s) ^ 2) ((r - s) ^ 2) =
      (1 : ℝ) / 2 + 2 * r ^ 2 * s ^ 2 / (r ^ 2 + s ^ 2) ^ 2 := by
  have hp : (r + s) ^ 2 + (r - s) ^ 2 = 2 * (r ^ 2 + s ^ 2) := by
    ring
  have hn : (r + s) ^ 2 + (r - s) ^ 2 ≠ 0 := by
    rw [hp]
    exact mul_ne_zero (by norm_num) h0
  unfold fingerprint
  field_simp [hn, h0]
  ring

/-- A strictly positive inner radius yields a fingerprint above 1/2. -/
theorem inner_horizon_detectable (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    (1 : ℝ) / 2 <
      (1 : ℝ) / 2 + 2 * r ^ 2 * s ^ 2 / (r ^ 2 + s ^ 2) ^ 2 := by
  have hp : 0 < 2 * r ^ 2 * s ^ 2 / (r ^ 2 + s ^ 2) ^ 2 := by
    positivity
  linarith

/-- At zero inner radius, the diagnostic is exactly 1/2. -/
theorem nonrotating_fingerprint (r : ℝ) (hr : r ≠ 0) :
    fingerprint ((r + 0) ^ 2) ((r - 0) ^ 2) = (1 : ℝ) / 2 := by
  have h0 : r ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by
    simp [pow_ne_zero _ hr]
  simpa using horizon_fingerprint r 0 h0

noncomputable def ratioFingerprint (q : ℝ) : ℝ :=
  (1 : ℝ) / 2 + 2 * q ^ 2 / (1 + q ^ 2) ^ 2

/-- An algebraic inversion invariant for q = rMinus/rPlus. -/
theorem ratio_inversion_identity (q : ℝ) :
    2 * (1 - ratioFingerprint q) =
      ((1 - q ^ 2) / (1 + q ^ 2)) ^ 2 := by
  unfold ratioFingerprint
  have hp : 1 + q ^ 2 ≠ 0 := by positivity
  field_simp [hp]
  ring


/-!
The following formalizes the algebraic K(t) jet:
  K''(0) = 2*b1^2,  K''''(0) = 4*b1^2*(b2^2 - 2*b1^2).
These two derivative identities are derived separately from the Krylov-chain
short-time expansion, not proved as derivatives of an infinite-dimensional
evolution in this file.
-/

/-- Reconstruction of the Lanczos ratio from the fourth and second K jets. -/
theorem kjet_reconstruction (h b1Sq b2Sq : ℝ) (hb : b1Sq ≠ 0) :
    h * (4 * b1Sq * (b2Sq - 2 * b1Sq)) / (2 * b1Sq) ^ 2 =
      h * (b2Sq / b1Sq - 2) := by
  field_simp [hb]
  ring

/-- The dimensionless black-hole fingerprint written directly with K jets. -/
theorem horizon_from_kjet (h x y : ℝ)
    (hh : h ≠ 0) (hs : x + y ≠ 0) :
    h * (4 * mu2 h x y * (b2Sq h x y - 2 * mu2 h x y)) /
        (2 * mu2 h x y) ^ 2 = fingerprint x y := by
  have hb : mu2 h x y ≠ 0 := by
    unfold mu2
    exact mul_ne_zero (mul_ne_zero (by norm_num) hh) hs
  calc
    h * (4 * mu2 h x y * (b2Sq h x y - 2 * mu2 h x y)) /
        (2 * mu2 h x y) ^ 2 =
      h * (b2Sq h x y / mu2 h x y - 2) :=
        kjet_reconstruction h (mu2 h x y) (b2Sq h x y) hb
    _ = fingerprint x y := fingerprint_from_lanczos h x y hh hs

/-- Short-time Krylov chain probability expansion, as a polynomial identity. -/
theorem kjet_from_first_two_amplitudes (u v : ℝ) :
    -(u ^ 4 + u ^ 2 * v ^ 2) / 3 + u ^ 2 * v ^ 2 / 2 =
      u ^ 2 * (v ^ 2 - 2 * u ^ 2) / 6 := by
  ring

end BTZWightman
