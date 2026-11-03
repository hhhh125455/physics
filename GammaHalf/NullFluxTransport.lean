import Mathlib

/-!
# Exact null transport identity for the renormalized charge focusing H

The exact Einstein null constraint, using
  X=r², H=e^(-2*sigma)/X and k=4*pi, is

  2X Xuu - 3Xu² - 2X Xu (Hu/H) + 4k X² phi_u² = 0.

On intervals X>0, H>0, Xu != 0, it implies
  (log H - log |Xu| + 3/2 log X)_u
     = 2k X phi_u² / Xu.

In the direction Xu>0, the source is nonnegative. Thus the
quantity J=H X^(3/2)/Xu is formally nondecreasing along that null
ray. The exact logarithmic *algebra* and sign are Lean-checked here;
the calculus/FTC step is not yet formalized in Lean.

This reveals the scalar-gradient compensation required when
X has a nonzero first-order corner gradient.
-/

namespace GammaHalf

theorem renormalized_null_log_transport
    (X Xu Xuu H Hu Pu k : ℝ)
    (hX : X ≠ 0) (hXu : Xu ≠ 0) (hH : H ≠ 0)
    (hnull : 2 * X * H * Xuu - 3 * H * Xu ^ 2 -
        2 * X * Xu * Hu + 4 * k * X ^ 2 * H * Pu ^ 2 = 0) :
    Hu / H - Xuu / Xu + 3 * Xu / (2 * X) =
      2 * k * X * Pu ^ 2 / Xu := by
  field_simp [hX, hXu, hH]
  nlinarith [hnull]

theorem positive_scalar_transport_source
    (X Xu Pu k : ℝ)
    (hX : 0 < X) (hXu : 0 < Xu) (hk : 0 ≤ k) :
    0 ≤ 2 * k * X * Pu ^ 2 / Xu := by
  positivity

/-- If a nonzero first derivative exists, the renormalized
    constraint forces the scalar and/or geometric terms to remain
    appreciable; they cannot all be small. -/
theorem null_linear_tip_requires_compensation
    (X Xu Xuu H Hu Pu k : ℝ)
    (hnull : 2 * X * H * Xuu - 3 * H * Xu ^ 2 -
        2 * X * Xu * Hu + 4 * k * X ^ 2 * H * Pu ^ 2 = 0)
    (hH : 0 < H) (hm : 0 < Xu ^ 2) :
    0 < (2 * X * H * Xuu) -
        (2 * X * Xu * Hu) + (4 * k * X ^ 2 * H * Pu ^ 2) := by
  nlinarith [mul_pos hH hm]

end GammaHalf
