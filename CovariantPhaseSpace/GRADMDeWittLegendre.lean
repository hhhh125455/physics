import Mathlib

/-!
# GR H2: pointwise ADM DeWitt Legendre inversion in 3 spatial dimensions

We work at one spatial point in an orthonormal frame for the spatial metric h.
The ADM Legendre map, after dividing by the nonzero density factor
alpha = sqrt(det h)/(16 pi G), is

P_ij = K_ij - (trace K) delta_ij.

All nine matrix entries are allowed in this algebraic calculation; in the GR
application K and P are symmetric. The inverse is

K_ij = P_ij - (trace P / 2) delta_ij.

This verifies the algebraic invertibility of the spatial velocity Hessian in
3+1 GR. It does NOT prove the Einstein-Hilbert to ADM integration by parts,
the ADM constraints, functional-analytic H2, or the full diffeomorphism gauge
identification (H3).
-/

namespace CovariantPhaseSpace

section ADMPointwiseLegendre

def admTrace3 (K : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  K 0 0 + K 1 1 + K 2 2

def admLegendre3 (K : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => K i j - (if i = j then admTrace3 K else 0)

def admInverse3 (P : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => P i j - (if i = j then admTrace3 P / 2 else 0)

theorem admLegendre3_trace (K : Matrix (Fin 3) (Fin 3) ℝ) :
    admTrace3 (admLegendre3 K) = -2 * admTrace3 K := by
  simp [admTrace3, admLegendre3]
  ring

theorem admInverse3_trace (P : Matrix (Fin 3) (Fin 3) ℝ) :
    admTrace3 (admInverse3 P) = -(admTrace3 P) / 2 := by
  simp [admTrace3, admInverse3]
  ring

/-- Left inverse: reconstruct every component of the extrinsic curvature. -/
theorem admInverse3_legendre3 (K : Matrix (Fin 3) (Fin 3) ℝ) :
    admInverse3 (admLegendre3 K) = K := by
  ext i j
  change admLegendre3 K i j -
    (if i = j then admTrace3 (admLegendre3 K) / 2 else 0) = K i j
  rw [admLegendre3_trace]
  by_cases h : i = j
  · simp [admLegendre3, h]
    ring
  · simp [admLegendre3, h]

/-- Right inverse: all ADM momentum components arise from K. -/
theorem admLegendre3_inverse3 (P : Matrix (Fin 3) (Fin 3) ℝ) :
    admLegendre3 (admInverse3 P) = P := by
  ext i j
  change admInverse3 P i j -
    (if i = j then admTrace3 (admInverse3 P) else 0) = P i j
  rw [admInverse3_trace]
  by_cases h : i = j
  · simp [admInverse3, h]
    ring
  · simp [admInverse3, h]

end ADMPointwiseLegendre

end CovariantPhaseSpace
