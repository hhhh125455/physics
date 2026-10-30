import Mathlib

/-!
# Symbolic verification of arXiv:2610.38428 (v1)

Formalizes selected exact algebraic statements in Guo--Liu--Liu,
"Quasinormal Modes of a Rotating Horava Black Hole".
The variable s represents sin²(theta), D represents r²+a²,
and Sigma represents the paper's Σ². These proofs do NOT certify
numerical QNM results, physical field equations, or asymptotics.
-/

namespace HoravaQNM

-- Eqs. (20), (25), (56).
theorem sigma_identity (M r a s : ℝ) :
    (r ^ 2 + a ^ 2) * (r ^ 2 + a ^ 2 * (1 - s)) +
        2 * M * r * a ^ 2 * s =
      (r ^ 2 + a ^ 2) ^ 2 - a ^ 2 * (r ^ 2 - 2 * M * r + a ^ 2) * s := by
  ring

-- Eq. (48).
theorem horizon_relation (M r a : ℝ)
    (hΔ : r ^ 2 - 2 * M * r + a ^ 2 = 0) :
    2 * M * r = r ^ 2 + a ^ 2 := by
  nlinarith

-- Eqs. (30), (76).
theorem horizon_sigma (D a s : ℝ) :
    D ^ 2 - a ^ 2 * (0 : ℝ) * s = D ^ 2 := by
  ring

-- Eq. (19) at m=0: exact axisymmetric null test.
theorem axisymmetric_LV_vanishes (η a M r ω Δ Sigma : ℂ) :
    -4 * η * a * M * r * ω * (0 : ℂ) / Δ +
        4 * η * (η + 2) * a ^ 2 * M ^ 2 * r ^ 2 * (0 : ℂ) ^ 2 /
          (Δ * Sigma) = 0 := by
  simp

-- Eq. (19) at η=0: exact Kerr limit.
theorem kerr_limit_LV_vanishes (a M r ω m Δ Sigma : ℂ) :
    -4 * (0 : ℂ) * a * M * r * ω * m / Δ +
        4 * (0 : ℂ) * (0 + 2) * a ^ 2 * M ^ 2 * r ^ 2 * m ^ 2 /
          (Δ * Sigma) = 0 := by
  simp

-- Eq. (19) at a=0: exact static limit.
theorem static_limit_LV_vanishes (η M r ω m Δ Sigma : ℂ) :
    -4 * η * (0 : ℂ) * M * r * ω * m / Δ +
        4 * η * (η + 2) * (0 : ℂ) ^ 2 * M ^ 2 * r ^ 2 * m ^ 2 /
          (Δ * Sigma) = 0 := by
  simp

-- Eqs. (26)--(29): exact difference between the full and truncated kernels.
theorem kernel_error_identity (D a Δ s : ℝ)
    (hD : D ≠ 0) (hSigma : D ^ 2 - a ^ 2 * Δ * s ≠ 0) :
    1 / (D ^ 2 - a ^ 2 * Δ * s) - 1 / D ^ 2 =
      (a ^ 2 * Δ * s) / ((D ^ 2 - a ^ 2 * Δ * s) * D ^ 2) := by
  field_simp
  ring

-- Eq. (27): 0 ≤ q < 1, under explicit exterior/sign hypotheses.
theorem q_in_unit_interval (D a Δ s : ℝ)
    (hD : 0 < D) (hΔ : 0 ≤ Δ) (hs : 0 ≤ s)
    (hSigma : 0 < D ^ 2 - a ^ 2 * Δ * s) :
    0 ≤ a ^ 2 * Δ * s / D ^ 2 ∧ a ^ 2 * Δ * s / D ^ 2 < 1 := by
  have hD2 : 0 < D ^ 2 := by positivity
  have hnum : 0 ≤ a ^ 2 * Δ * s := by positivity
  constructor
  · exact div_nonneg hnum (le_of_lt hD2)
  · apply (div_lt_one hD2).2
    linarith

-- Eq. (31): exact two-term expansion with explicit remainder.
theorem kernel_second_order_remainder (D B P : ℝ)
    (hD : D ≠ 0) (hSigma : D ^ 2 - B ≠ 0) :
    P / (D ^ 2 - B) = P / D ^ 2 + P * B / D ^ 4 +
      P * B ^ 2 / (D ^ 4 * (D ^ 2 - B)) := by
  field_simp
  ring

-- Eq. (55): η-linear term and an exact quadratic remainder.
theorem linear_eta_decomposition (η A B : ℂ) :
    η * A + η * (η + 2) * B = η * (A + 2 * B) + η ^ 2 * B := by
  ring

-- Eqs. (43),(44): common linear η order.
theorem separable_potential_linearization (η P : ℂ) :
    η * (η + 2) * P = 2 * η * P + η ^ 2 * P := by
  ring

-- Eq. (49): Kerr + two LV horizon contributions yield (ω - m Ω_H)^2.
-- Uses D(r₊)=2 M r₊; D is nonzero at a regular horizon.
theorem horizon_potential_is_square (D a m η ω : ℂ) (hD : D ≠ 0) :
    (D * ω - a * m) ^ 2 / D ^ 2 -
        2 * η * ω * a * m / D +
        η * (η + 2) * (a * m) ^ 2 / D ^ 2 =
      (ω - m * (a * (1 + η) / D)) ^ 2 := by
  field_simp
  ring

end HoravaQNM

/- Verification extension uses the source PDF and checks equation chains. -/
