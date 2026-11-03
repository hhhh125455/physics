import Mathlib

/-!
# Exact first-jet algebra for the coupled Einstein–Maxwell–scalar system

Use double-null coordinates, X=r²>0, E=exp(-2sigma), k=4*pi,
and q2=q².  The *undivided* equations read

 area:  2 X Xuv - E(q2-X) = 0
 scalar: 2 X Puv + Xu Pv + Xv Pu = 0
 sigma:  4 X² Suv + Xu Xv - E(2q2-X) - 4k X² Pu Pv = 0
 U-null: 2 X Xuu - Xu² + 4X Su Xu + 4k X² Pu² = 0.

The V-null equation is the U/V exchange of U-null.

For the parameter A, denote the linearized variables
 δX=Y, δsigma=Z, δphi=Psi; so δE=-2E Z.

Every theorem below is an EXACT polynomial identity in an auxiliary
epsilon.  It proves the coefficient of epsilon for all four equations,
including the remainder terms.  There are no PDE-solution regularity
claims here: identifying these coefficients with actual A-derivatives
requires differentiability of the PDE solution family.
-/

namespace GammaHalf

private def areaP (X Xuv E q2 : ℝ) : ℝ :=
  2 * X * Xuv - E * (q2 - X)

private def areaL (X Xuv E q2 Y Yuv Z : ℝ) : ℝ :=
  2 * Y * Xuv + 2 * X * Yuv + E * Y + 2 * E * Z * (q2 - X)

theorem exact_area_first_jet
    (X Xuv E q2 Y Yuv Z eps : ℝ) :
    areaP (X + eps * Y) (Xuv + eps * Yuv)
       (E - 2 * eps * E * Z) q2 =
      areaP X Xuv E q2 +
        eps * areaL X Xuv E q2 Y Yuv Z +
        eps ^ 2 * (2 * Y * Yuv - 2 * E * Z * Y) := by
  unfold areaP areaL
  ring

private def scalarP (X Xu Xv Puv Pu Pv : ℝ) : ℝ :=
  2 * X * Puv + Xu * Pv + Xv * Pu

private def scalarL (X Xu Xv Puv Pu Pv
    Y Yu Yv Psiuv Psiu Psiv : ℝ) : ℝ :=
  2 * X * Psiuv + Xu * Psiv + Xv * Psiu +
    2 * Y * Puv + Yu * Pv + Yv * Pu

theorem exact_scalar_first_jet
    (X Xu Xv Puv Pu Pv Y Yu Yv Psiuv Psiu Psiv eps : ℝ) :
    scalarP (X + eps * Y) (Xu + eps * Yu) (Xv + eps * Yv)
       (Puv + eps * Psiuv) (Pu + eps * Psiu) (Pv + eps * Psiv) =
      scalarP X Xu Xv Puv Pu Pv +
      eps * scalarL X Xu Xv Puv Pu Pv Y Yu Yv Psiuv Psiu Psiv +
      eps ^ 2 * (2 * Y * Psiuv + Yu * Psiv + Yv * Psiu) := by
  unfold scalarP scalarL
  ring

private def sigmaP (X Xu Xv Suv E Pu Pv q2 k : ℝ) : ℝ :=
  4 * X ^ 2 * Suv + Xu * Xv - E * (2 * q2 - X) -
    4 * k * X ^ 2 * Pu * Pv

private def sigmaL (X Xu Xv Suv E Pu Pv q2 k
    Y Yu Yv Zuv Z Psiu Psiv : ℝ) : ℝ :=
  4 * X ^ 2 * Zuv + 8 * X * Y * Suv +
    Yu * Xv + Xu * Yv +
    2 * E * Z * (2 * q2 - X) + E * Y -
    8 * k * X * Y * Pu * Pv -
    4 * k * X ^ 2 * (Psiu * Pv + Pu * Psiv)

theorem exact_sigma_first_jet
    (X Xu Xv Suv E Pu Pv q2 k
     Y Yu Yv Zuv Z Psiu Psiv eps : ℝ) :
    sigmaP (X + eps * Y) (Xu + eps * Yu) (Xv + eps * Yv)
       (Suv + eps * Zuv) (E - 2 * eps * E * Z)
       (Pu + eps * Psiu) (Pv + eps * Psiv) q2 k =
      sigmaP X Xu Xv Suv E Pu Pv q2 k +
      eps * sigmaL X Xu Xv Suv E Pu Pv q2 k
        Y Yu Yv Zuv Z Psiu Psiv +
      eps ^ 2 * (
        - 2 * E * Y * Z
        - 4 * k * (X ^ 2 * Psiu * Psiv +
          2 * X * Y * (Psiu * Pv + Pu * Psiv) + Y ^ 2 * Pu * Pv)
        + 4 * Y ^ 2 * Suv + 8 * X * Y * Zuv + Yu * Yv) +
      eps ^ 3 * (
        - 8 * k * X * Y * Psiu * Psiv
        - 4 * k * Y ^ 2 * (Psiu * Pv + Pu * Psiv)
        + 4 * Y ^ 2 * Zuv) +
      eps ^ 4 * (-4 * k * Y ^ 2 * Psiu * Psiv) := by
  unfold sigmaP sigmaL
  ring

private def nullP (X Xu Xuu Su Pu k : ℝ) : ℝ :=
  2 * X * Xuu - Xu ^ 2 + 4 * X * Su * Xu +
    4 * k * X ^ 2 * Pu ^ 2

private def nullL (X Xu Xuu Su Pu k Y Yu Yuu Zu Psiu : ℝ) : ℝ :=
  2 * Y * Xuu + 2 * X * Yuu -
    2 * Xu * Yu +
    4 * Y * Su * Xu + 4 * X * Zu * Xu + 4 * X * Su * Yu +
    8 * k * X * Y * Pu ^ 2 + 8 * k * X ^ 2 * Pu * Psiu

theorem exact_null_constraint_first_jet
    (X Xu Xuu Su Pu k Y Yu Yuu Zu Psiu eps : ℝ) :
    nullP (X + eps * Y) (Xu + eps * Yu) (Xuu + eps * Yuu)
      (Su + eps * Zu) (Pu + eps * Psiu) k =
      nullP X Xu Xuu Su Pu k +
      eps * nullL X Xu Xuu Su Pu k Y Yu Yuu Zu Psiu +
      eps ^ 2 * (
        2 * Y * Yuu - Yu ^ 2 +
        4 * Su * Y * Yu + 4 * Zu * (X * Yu + Xu * Y) +
        4 * k * (X ^ 2 * Psiu ^ 2 +
          4 * X * Y * Pu * Psiu + Y ^ 2 * Pu ^ 2)) +
      eps ^ 3 * (
        4 * Y * Yu * Zu +
        8 * k * X * Y * Psiu ^ 2 +
        8 * k * Y ^ 2 * Pu * Psiu) +
      eps ^ 4 * (4 * k * Y ^ 2 * Psiu ^ 2) := by
  unfold nullP nullL
  ring

/-- Substituting the area equation into its linearization yields the
    exact regular-point variational equation. This verifies the
    positivity of the Y-potential coefficient algebraically. -/
theorem area_variation_regular (X Xuv E q2 Y Yuv Z : ℝ)
    (hX : X ≠ 0)
    (harea : 2 * X * Xuv = E * (q2 - X))
    (hlin : areaL X Xuv E q2 Y Yuv Z = 0) :
    Yuv + E * q2 / (2 * X ^ 2) * Y =
      -(E * (q2 / X - 1) * Z) := by
  unfold areaL at hlin
  have hareaY : 2 * X * Xuv * Y = E * (q2 - X) * Y := by
    simpa only [mul_assoc] using congrArg (fun t : ℝ => t * Y) harea
  have hlinX :
      X * (2 * Y * Xuv + 2 * X * Yuv + E * Y +
        2 * E * Z * (q2 - X)) = 0 := by
    simpa using congrArg (fun t : ℝ => X * t) hlin
  field_simp [hX]
  nlinarith [hareaY, hlinX]

end GammaHalf
