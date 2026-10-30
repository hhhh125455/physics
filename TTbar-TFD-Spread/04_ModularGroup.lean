import Mathlib

/-!
Audit of original source lines 69--143: modular transformations of the torus.
Proves the determinant, lattice and Möbius algebra as mathematical statements.
T invariance of physical partition functions is NOT automatic: the spectrum's
spin quantization, central-charge anomaly and spin structures matter.
-/

namespace TTbarTFD

def det2 (a b c d : ℤ) : ℤ := a * d - b * c

/-- An integer inverse matrix forces determinant to be plus or minus one. -/
theorem integer_factors_of_one (x y : ℤ) (h : x * y = 1) :
    x = 1 ∨ x = -1 := by
  have hx : x ≠ 0 := by
    intro he
    simp [he] at h
  by_cases hp : 0 ≤ x
  · have hxpos : 1 ≤ x := by omega
    have hypos : 1 ≤ y := by nlinarith
    have haux : 0 ≤ x * (y - 1) :=
      mul_nonneg (by omega) (by omega)
    have hxle : x ≤ 1 := by nlinarith [haux]
    left
    omega
  · have hxneg : x ≤ -1 := by omega
    have hyneg : y ≤ -1 := by nlinarith
    have haux : 0 ≤ (-x) * (-y - 1) :=
      mul_nonneg (by omega) (by omega)
    have hxge : -1 ≤ x := by nlinarith [haux]
    right
    omega

theorem determinant_inverse_product
    (a b c d e f g h : ℤ)
    (h11 : e*a + f*c = 1) (h12 : e*b + f*d = 0)
    (h21 : g*a + h*c = 0) (h22 : g*b + h*d = 1) :
    det2 a b c d * det2 e f g h = 1 := by
  unfold det2
  calc
    (a*d-b*c)*(e*h-f*g) =
      (e*a+f*c)*(g*b+h*d) - (e*b+f*d)*(g*a+h*c) := by ring
    _ = 1 := by rw [h11, h12, h21, h22]; ring

theorem basis_change_det_sign
    (a b c d e f g h : ℤ)
    (h11 : e*a + f*c = 1) (h12 : e*b + f*d = 0)
    (h21 : g*a + h*c = 0) (h22 : g*b + h*d = 1) :
    det2 a b c d = 1 ∨ det2 a b c d = -1 :=
  integer_factors_of_one _ _
    (determinant_inverse_product a b c d e f g h h11 h12 h21 h22)

/-- Determinant one supplies an explicit integer inverse of a cycle basis. -/
theorem inverse_first_cycle (a b c d : ℤ) (v₁ v₂ : ℂ)
    (hdet : det2 a b c d = 1) :
    (d : ℂ) * ((a : ℂ)*v₁+(b : ℂ)*v₂) -
       (b : ℂ) * ((c : ℂ)*v₁+(d : ℂ)*v₂) = v₁ := by
  have hd : (a : ℂ)*(d : ℂ)-(b : ℂ)*(c : ℂ) = 1 := by
    exact_mod_cast hdet
  calc
    _ = ((a : ℂ)*(d : ℂ)-(b : ℂ)*(c : ℂ)) * v₁ := by ring
    _ = v₁ := by rw [hd]; ring

theorem inverse_second_cycle (a b c d : ℤ) (v₁ v₂ : ℂ)
    (hdet : det2 a b c d = 1) :
    -(c : ℂ) * ((a : ℂ)*v₁+(b : ℂ)*v₂) +
       (a : ℂ) * ((c : ℂ)*v₁+(d : ℂ)*v₂) = v₂ := by
  have hd : (a : ℂ)*(d : ℂ)-(b : ℂ)*(c : ℂ) = 1 := by
    exact_mod_cast hdet
  calc
    _ = ((a : ℂ)*(d : ℂ)-(b : ℂ)*(c : ℂ)) * v₂ := by ring
    _ = v₂ := by rw [hd]; ring

noncomputable def mobius (a b c d : ℤ) (τ : ℂ) : ℂ :=
  ((a : ℂ)*τ + (b : ℂ)) / ((c : ℂ)*τ + (d : ℂ))

/-- A nondegenerate oriented lattice cannot develop a zero denominator. -/
theorem denominator_ne_zero (a b c d : ℤ) (τ : ℂ)
    (hτ : 0 < τ.im) (hdet : det2 a b c d = 1) :
    (c : ℂ) * τ + (d : ℂ) ≠ 0 := by
  intro hz
  have him := congrArg Complex.im hz
  have hcprod : (c : ℝ) * τ.im = 0 := by
    simpa [Complex.mul_im, Complex.add_im] using him
  have hc : c = 0 := by
    have hcR : (c : ℝ) = 0 :=
      (mul_eq_zero.mp hcprod).resolve_right (ne_of_gt hτ)
    exact_mod_cast hcR
  have hdC : (d : ℂ) = 0 := by simpa [hc] using hz
  have hd : d = 0 := by exact_mod_cast hdC
  simp [det2, hc, hd] at hdet

/-- Imaginary part of a modular transform: orientation is the determinant. -/
theorem mobius_imag (a b c d : ℤ) (τ : ℂ)
    (hdet : det2 a b c d = 1) :
    (mobius a b c d τ).im =
      τ.im / Complex.normSq ((c : ℂ)*τ+(d : ℂ)) := by
  have hdR : (a : ℝ)*(d : ℝ)-(b : ℝ)*(c : ℝ) = 1 := by
    exact_mod_cast hdet
  unfold mobius
  rw [Complex.div_im, ← sub_div]
  congr 1
  simp [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re]
  calc
    _ = ((a : ℝ)*(d : ℝ)-(b : ℝ)*(c : ℝ))*τ.im := by ring
    _ = τ.im := by rw [hdR]; ring

theorem mobius_upper_half_plane (a b c d : ℤ) (τ : ℂ)
    (hτ : 0 < τ.im) (hdet : det2 a b c d = 1) :
    0 < (mobius a b c d τ).im := by
  rw [mobius_imag a b c d τ hdet]
  exact div_pos hτ
    (Complex.normSq_pos.mpr (denominator_ne_zero a b c d τ hτ hdet))

/-- Matrices T=(1,1;0,1), S=(0,-1;1,0). -/
theorem T_det : det2 1 1 0 1 = 1 := by norm_num [det2]
theorem S_det : det2 0 (-1) 1 0 = 1 := by norm_num [det2]

theorem T_action (τ : ℂ) : mobius 1 1 0 1 τ = τ + 1 := by
  simp [mobius]

theorem S_action (τ : ℂ) (hτ : τ ≠ 0) :
    mobius 0 (-1) 1 0 τ = -1 / τ := by
  simp [mobius]

/-- The formula derived from choosing a new lattice basis. -/
theorem basis_modulus (a b c d : ℤ) (τ v₂ : ℂ)
    (hv₂ : v₂ ≠ 0)
    (hden : (c : ℂ) * τ + (d : ℂ) ≠ 0) :
    ((a : ℂ)*(τ*v₂)+(b : ℂ)*v₂) /
      ((c : ℂ)*(τ*v₂)+(d : ℂ)*v₂) = mobius a b c d τ := by
  unfold mobius
  field_simp [hv₂, hden]
  ring

/-- The T-induced spectral phase cancels for an integer-spin state. -/
theorem integer_spin_T_phase (β θ E : ℝ) (j : ℤ) :
    Complex.exp (((-β*E : ℝ) : ℂ) +
      Complex.I * (((θ+2*Real.pi)*(j:ℝ) : ℝ) : ℂ)) =
    Complex.exp (((-β*E : ℝ) : ℂ) +
      Complex.I * (((θ*(j:ℝ) : ℝ) : ℂ))) := by
  have heq :
      (((-β*E : ℝ) : ℂ) + Complex.I *
        (((θ+2*Real.pi)*(j:ℝ) : ℝ) : ℂ)) =
      (((-β*E : ℝ) : ℂ) + Complex.I *
        (((θ*(j:ℝ) : ℝ) : ℂ))) +
        (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- A half-integer spin supplies a counterexample to unconditional T invariance. -/
theorem half_spin_T_failure :
    Complex.exp ((Real.pi : ℂ) * Complex.I) ≠ Complex.exp (0 : ℂ) := by
  simp

end TTbarTFD
