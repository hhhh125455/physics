import Mathlib

/-!
# Odd scalar angular mode and characteristic-edge obstruction

For an area blow-up X=c*(U+V), the scalar transport equation
  ∂U(X∂V φ) + ∂V(X∂U φ) = 0
with degree-zero angular ansatz
  η=(U-V)/(U+V), φ=f(η)
reduces to
  (1-η²) f''(η) = η f'(η).

The nonconstant odd solution is proportional to arcsin(η).
Its U-derivative equals a*sqrt(V)/(sqrt(U)*(U+V)), which along
U=1/n², V=1 becomes a*n³/(n²+1). We prove that this sequence
is unbounded for a>0; hence the mode cannot have bounded
characteristic-edge U-derivative.

The angular calculus reduction and arcsin derivative formula
are independently checked by SymPy; Lean checks the rational
reduction and the unboundedness argument, NOT the full PDE calculus.
-/

namespace GammaHalf

theorem angular_scalar_transport_algebra
    (u v c fp fpp : ℝ) (hz : u + v ≠ 0) :
    2 * c * ((u ^ 2 - v ^ 2) * fp - 4 * u * v * fpp) /
       (u + v) ^ 3 =
    (2 * c / (u + v)) *
      (((u - v) / (u + v)) * fp -
        (1 - ((u - v) / (u + v)) ^ 2) * fpp) := by
  field_simp
  <;> ring

/-- A positive-amplitude odd angular mode has an unbounded
    (candidate) U-characteristic derivative as U tends to zero,
    witnessed on U=1/n² and V=1. -/
theorem angular_gradient_sequence_unbounded
    (a : ℝ) (ha : 0 < a) (M : ℝ) :
    ∃ n : ℕ, (1 : ℝ) ≤ (n : ℝ) ∧
      M < a * (n : ℝ) ^ 3 / ((n : ℝ) ^ 2 + 1) := by
  obtain ⟨n, hn⟩ :=
    exists_nat_gt (max (1 : ℝ) (2 * max M 0 / a + 1))
  have hn1 : (1 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hn
  have hnbig : 2 * max M 0 / a + 1 < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hden : (0 : ℝ) < (n : ℝ) ^ 2 + 1 := by positivity
  have hdenle : (n : ℝ) ^ 2 + 1 ≤ 2 * (n : ℝ) ^ 2 := by
    nlinarith
  have hm : M < a * (n : ℝ) / 2 := by
    have h' : 2 * max M 0 / a < (n : ℝ) := by linarith
    have h'' : 2 * max M 0 < a * (n : ℝ) := by
      nlinarith [(div_lt_iff₀ ha).mp h']
    have hM : M ≤ max M 0 := le_max_left _ _
    linarith
  have hhalfn : (0 : ℝ) ≤ a * (n : ℝ) / 2 := by positivity
  have hbounded :
      a * (n : ℝ) / 2 ≤
        a * (n : ℝ) ^ 3 / ((n : ℝ) ^ 2 + 1) := by
    apply (le_div_iff₀ hden).2
    calc
      (a * (n : ℝ) / 2) * ((n : ℝ) ^ 2 + 1) ≤
          (a * (n : ℝ) / 2) * (2 * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hdenle hhalfn
      _ = a * (n : ℝ) ^ 3 := by ring
  exact ⟨n, le_of_lt hn1, lt_of_lt_of_le hm hbounded⟩

end GammaHalf
