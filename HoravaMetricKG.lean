import Mathlib

/-!
# ADM metric: Klein–Gordon coefficient algebra and radial Liouville transform

Source compared to arXiv:2610.38428v1, PDF pages 3–7.\nThe metric and the radial Sturm–Liouville ODE are explicit mathematical
premises. These theorems certify their subsequent algebraic consequences;
they do not automatically certify the paper's transcription or PDE calculus.
Symbols: D=r²+a², Delta=r²-2Mr+a², rho=ρ², Sigma=Σ², s=sin²θ.
The jet variables u, ur, urr model a function and its first two r-derivatives.
-/
namespace HoravaMetricKG

theorem sigma_squared (M r a s : ℝ) :
    (r ^ 2 + a ^ 2) * (r ^ 2 + a ^ 2 - a ^ 2 * s) +
      2 * M * r * a ^ 2 * s =
    (r ^ 2 + a ^ 2) ^ 2 -
      a ^ 2 * (r ^ 2 - 2 * M * r + a ^ 2) * s := by
  ring

theorem adm_block_determinant (N2 q B : ℝ) :
    (-N2 + q * B ^ 2) * q - (q * B) ^ 2 = -N2 * q := by
  ring

theorem metric_determinant (Delta rho Sigma s : ℝ)
    (hDelta : Delta ≠ 0) (hrho : rho ≠ 0) (hSigma : Sigma ≠ 0) :
    (-(Delta * rho / Sigma) * (Sigma * s / rho)) *
      (rho / Delta) * rho = -rho ^ 2 * s := by
  field_simp
  ring

theorem angular_identity_cleared (M r a s : ℝ) :
    (r ^ 2 - 2 * M * r + a ^ 2) *
        (r ^ 2 + a ^ 2 - a ^ 2 * s) ^ 2 -
        4 * M ^ 2 * a ^ 2 * r ^ 2 * s =
      ((r ^ 2 + a ^ 2) ^ 2 -
         a ^ 2 * (r ^ 2 - 2 * M * r + a ^ 2) * s) *
        ((r ^ 2 - 2 * M * r + a ^ 2) - a ^ 2 * s) := by
  ring

theorem kerr_fourier_rearrangement
    (M r a omega m s : ℝ)
    (hDelta : r ^ 2 - 2 * M * r + a ^ 2 ≠ 0)
    (hs : s ≠ 0) :
    (r ^ 2 + a ^ 2) ^ 2 * omega ^ 2 /
        (r ^ 2 - 2 * M * r + a ^ 2) -
      a ^ 2 * s * omega ^ 2 -
      4 * M * a * r * omega * m /
        (r ^ 2 - 2 * M * r + a ^ 2) -
      m ^ 2 / s + a ^ 2 * m ^ 2 /
        (r ^ 2 - 2 * M * r + a ^ 2) =
      ((r ^ 2 + a ^ 2) * omega - a * m) ^ 2 /
        (r ^ 2 - 2 * M * r + a ^ 2) -
        (a ^ 2 * omega ^ 2 - 2 * a * m * omega) +
        a ^ 2 * omega ^ 2 * (1 - s) - m ^ 2 / s := by
  field_simp
  ring

theorem lv_fourier_decomposition
    (eta M a r omega m Delta Sigma : ℝ) :
    -(4 * M * a * r * omega * m * (1 + eta)) / Delta +
        4 * M ^ 2 * a ^ 2 * r ^ 2 * m ^ 2 * (1 + eta) ^ 2 /
          (Delta * Sigma) =
      -(4 * M * a * r * omega * m) / Delta +
        4 * M ^ 2 * a ^ 2 * r ^ 2 * m ^ 2 / (Delta * Sigma) -
        4 * eta * M * a * r * omega * m / Delta +
        4 * eta * (eta + 2) * M ^ 2 * a ^ 2 * r ^ 2 * m ^ 2 /
          (Delta * Sigma) := by
  ring

/-
The following full 2-jet identity follows from R=u/sqrt(D),
d/dr_*=(Delta/D)d/dr, and the radial equation
Delta R'' + Delta' R' + (W/Delta)R=0.
The differential product and chain rules are premises of this algebraic
jet theorem rather than formalized functions and derivatives.
-/
theorem radial_liouville_jet
    (D Delta Dp Dpp DeltaP W u ur urr : ℝ)
    (hD : D ≠ 0) (hDelta : Delta ≠ 0) :
    Delta *
        (urr - Dp * ur / D +
          (3 * Dp ^ 2 / (4 * D ^ 2) - Dpp / (2 * D)) * u) +
        DeltaP * (ur - Dp * u / (2 * D)) +
        W / Delta * u =
      D ^ 2 / Delta *
        ((Delta / D) ^ 2 * urr +
          (Delta / D) * (DeltaP / D - Delta * Dp / D ^ 2) * ur +
          (W / D ^ 2 -
            Delta * (DeltaP * Dp + Delta * Dpp) / (2 * D ^ 3) +
            3 * Delta ^ 2 * Dp ^ 2 / (4 * D ^ 4)) * u) := by
  field_simp
  ring

theorem geometric_potential_specialization
    (D Delta DeltaP r : ℝ) :
    -(Delta * (DeltaP * (2 * r) + Delta * 2)) / (2 * D ^ 3) +
      3 * Delta ^ 2 * (2 * r) ^ 2 / (4 * D ^ 4) =
      -Delta * (r * DeltaP + Delta) / D ^ 3 +
      3 * Delta ^ 2 * r ^ 2 / D ^ 4 := by
  ring

theorem radial_lv_potential_expansion
    (eta M a r omega m D : ℝ) :
    -(4 * eta * M * a * r * omega * m) / D ^ 2 +
        4 * eta * (eta + 2) * M ^ 2 * a ^ 2 * r ^ 2 * m ^ 2 /
          D ^ 4 =
      eta * (-(4 * M * a * r * omega * m) / D ^ 2 +
        8 * M ^ 2 * a ^ 2 * r ^ 2 * m ^ 2 / D ^ 4) +
        eta ^ 2 * (4 * M ^ 2 * a ^ 2 * r ^ 2 * m ^ 2 / D ^ 4) := by
  ring


-- Paper (40)-(41): G=r Δ/D², dG/dr*=(Δ/D)dG/dr.
-- All algebraic statements also hold for complex QNM variables.
theorem eq40_geometric_potential_complex
    (D Delta r DeltaP : ℂ) (hD : D ≠ 0) :
    -(Delta / D) *
        ((Delta + r * DeltaP) / D ^ 2 -
          4 * r ^ 2 * Delta / D ^ 3) -
        (r * Delta / D ^ 2) ^ 2 =
      -(Delta * (r * DeltaP + Delta)) / D ^ 3 +
        3 * r ^ 2 * Delta ^ 2 / D ^ 4 := by
  field_simp
  ring

end HoravaMetricKG
