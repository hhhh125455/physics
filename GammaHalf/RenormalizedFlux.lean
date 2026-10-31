import Mathlib

/-!
# Renormalized focusing flux and the singular null-constraint balance

Set X=r², E=exp(-2*sigma)>0 and H=E/X, where X>0.
The charged area equation becomes
  X_uv = (H/2)*(q²-X)
and its parameter variation can be written without separate Y/X² and Z/X terms.
The variation of H is
  H_A = - E/X² * (Y+2*X*Z), where Y=X_A, Z=sigma_A.

The "renormalized sigma" rho = sigma+(1/2)*log X has E=X*exp(-2*rho).
The U-null constraint, expressed with rho, reads
  2 X Xuu - 3 Xu² + 4 X Xu rho_u + 4k X² phi_u² = 0.

This implies a quantitative obstruction to a nonzero linear blow-up with
all three balance channels negligible. The file proves those algebraic
identities and the quantitative disjunction. It DOES NOT prove the
hypothesized asymptotic limits or existence of the blown-up solution.
-/

namespace GammaHalf

theorem charged_source_regularized (X E q2 : ℝ) (hX : X ≠ 0) :
    E / 2 * (q2 / X - 1) = (E / X) / 2 * (q2 - X) := by
  field_simp

/-- Exact source difference in the regularized variables H_i=E_i/X_i. -/
theorem charged_source_difference_regularized
    (X1 X2 E1 E2 q2 : ℝ) (hX1 : X1 ≠ 0) (hX2 : X2 ≠ 0) :
    E2 / 2 * (q2 / X2 - 1) -
       E1 / 2 * (q2 / X1 - 1) =
       q2 / 2 * (E2 / X2 - E1 / X1) - (E2 - E1) / 2 := by
  field_simp
  ring

/-- Parameter derivative of the positive flux H=E/X,
    given E_A=-2EZ. A derivative *identity*, stated algebraically. -/
theorem regularized_flux_variation
    (X E Y Z H_A : ℝ) (hX : X ≠ 0)
    (hE_A : H_A = (-2 * E * Z) / X - E * Y / X ^ 2) :
    H_A = -(E / X ^ 2) * (Y + 2 * X * Z) := by
  rw [hE_A]
  field_simp
  ring

/-- Original singular-looking variational focusing source
    is exactly the regularized-source variation. -/
theorem area_variation_flux_cancellation
    (X E q2 Y Z : ℝ) (hX : X ≠ 0) :
    -E * q2 / (2 * X ^ 2) * Y
      - E * (q2 / X - 1) * Z =
       q2 / 2 * (-(E / X ^ 2) * (Y + 2 * X * Z)) + E * Z := by
  field_simp
  ring

/-- Geometric null constraint transformed from sigma to
    rho=sigma+log(X)/2; valid on the regular X>0 region. -/
theorem renormalized_null_constraint
    (X Xu Xuu Su Rhou Pu k : ℝ) (hX : X ≠ 0)
    (hSu : Su = Rhou - Xu / (2 * X))
    (hnull :
      2 * X * Xuu - Xu ^ 2 + 4 * X * Su * Xu +
      4 * k * X ^ 2 * Pu ^ 2 = 0) :
    2 * X * Xuu - 3 * Xu ^ 2 + 4 * X * Xu * Rhou +
       4 * k * X ^ 2 * Pu ^ 2 = 0 := by
  rw [hSu] at hnull
  field_simp [hX] at hnull
  nlinarith [hnull]

/-- The renormalized sigma equation, using the area evolution
    2*X*Xuv=E*(q2-X). -/
theorem renormalized_sigma_equation
    (X Xu Xv Xuv Suv Ruv E q2 Pu Pv k : ℝ)
    (hX : X ≠ 0)
    (hR : Ruv = Suv + Xuv / (2 * X) - Xu * Xv / (2 * X ^ 2))
    (hArea : 2 * X * Xuv = E * (q2 - X))
    (hSigma : 4 * X ^ 2 * Suv + Xu * Xv -
        E * (2 * q2 - X) - 4 * k * X ^ 2 * Pu * Pv = 0) :
    4 * X ^ 2 * Ruv + 3 * Xu * Xv -
      E * (3 * q2 - 2 * X) - 4 * k * X ^ 2 * Pu * Pv = 0 := by
  have hRmult : 4 * X ^ 2 * Ruv =
       4 * X ^ 2 * Suv + 2 * X * Xuv - 2 * Xu * Xv := by
    rw [hR]
    field_simp [hX]
    ring
  nlinarith [hRmult, hArea, hSigma]

/-- If Xu has a nonvanishing first-order limit, at least one term
    in the renormalized constraint must stay comparably large:
    X Xuu, X Xu rho_u, or k X² phi_u². -/
theorem linear_area_requires_nonsmall_channel
    (X Xu Xuu Rhou Pu k : ℝ)
    (hNull : 2 * X * Xuu - 3 * Xu ^ 2 +
      4 * X * Xu * Rhou + 4 * k * X ^ 2 * Pu ^ 2 = 0) :
    Xu ^ 2 ≤ |2 * X * Xuu| ∨
    Xu ^ 2 ≤ |4 * X * Xu * Rhou| ∨
    Xu ^ 2 ≤ |4 * k * X ^ 2 * Pu ^ 2| := by
  by_contra h
  push Not at h
  rcases h with ⟨ha, hb, hc⟩
  have hla : 2 * X * Xuu ≤ |2 * X * Xuu| := le_abs_self _
  have hlb : 4 * X * Xu * Rhou ≤ |4 * X * Xu * Rhou| :=
    le_abs_self _
  have hlc : 4 * k * X ^ 2 * Pu ^ 2 ≤ |4 * k * X ^ 2 * Pu ^ 2| :=
    le_abs_self _
  nlinarith

end GammaHalf
