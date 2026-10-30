import Mathlib

/-!
# Linear characteristic branch: exact area-equation example and leading coupled balances

The exact charged area equation is X_uv = E/2*(q^2/X-1).

Part I proves an explicit solution of THAT equation alone with q^2=1,
X=z+z^2, z=u+v, E=4X/(1-X). Here X is linear at the corner
while E/X -> 4, so a linear area profile does not force E -> constant.

Part II verifies the leading *algebraic* Einstein-scalar balances for a
different, singular-inner asymptotic candidate:
  X=c*(u+v), sigma=(1/4+k)*log(u+v)-k*log(u*v),
  k=4*pi*a^2,
  phi=a*asin((u-v)/(u+v)).
In this part the charge terms are omitted from the LEADING balances only.
The phi derivative, asymptotic order estimates, and existence of an exact
coupled solution require independent proofs.
-/

namespace GammaHalf

def toyArea (u v : ℝ) : ℝ :=
  (u + v) + (u + v) ^ 2

noncomputable def toyConformal (u v : ℝ) : ℝ :=
  4 * toyArea u v / (1 - toyArea u v)

/-- The U derivative of the polynomial area profile, computed with real calculus. -/
theorem toy_area_deriv_u (u v : ℝ) :
    deriv (fun t : ℝ => toyArea t v) u = 1 + 2 * (u + v) := by
  have hlin : HasDerivAt (fun t : ℝ => t + v) 1 u := by
    simpa only [id_eq] using (hasDerivAt_id u).add_const v
  have hfun :
      (fun t : ℝ => toyArea t v) =
        (fun t : ℝ => t + v) + (fun t : ℝ => t + v) ^ 2 := by
    funext t
    rfl
  rw [hfun]
  simpa only [Nat.reduceSub, pow_one, mul_one] using
    (hlin.add (hlin.pow 2)).deriv

/-- Unlike the toy source identity, this verifies an actual mixed derivative. -/
theorem toy_area_mixed (u v : ℝ) :
    deriv (fun y : ℝ => deriv (fun x : ℝ => toyArea x y) u) v = 2 := by
  have hext :
      (fun y : ℝ => deriv (fun x : ℝ => toyArea x y) u) =
      (fun y : ℝ => 1 + 2 * (u + y)) := by
    funext y
    exact toy_area_deriv_u u y
  rw [hext]
  have hy : HasDerivAt (fun y : ℝ => 1 + 2 * (u + y)) 2 v := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id v).const_add u |>.const_mul 2 |>.const_add 1)
  exact hy.deriv

/-- An exact *algebraic* charged source with q^2=1, not a coupled solution. -/
theorem toy_charged_source (u v : ℝ)
    (hX : toyArea u v ≠ 0)
    (hden : 1 - toyArea u v ≠ 0) :
    toyConformal u v / 2 * (1 / toyArea u v - 1) = 2 := by
  unfold toyConformal
  field_simp [hX, hden]
  <;> ring

/-- The exact area function has a nonzero linear term at the diagonal corner. -/
theorem toy_linear_corner (eps : ℝ) :
    toyArea eps eps = 2 * eps + 4 * eps ^ 2 := by
  unfold toyArea
  ring

/-- E/X=4/(1-X); thus E vanishes linearly when X tends to zero. -/
theorem toy_conformal_order (u v : ℝ)
    (hX : toyArea u v ≠ 0)
    (hden : 1 - toyArea u v ≠ 0) :
    toyConformal u v / toyArea u v =
      4 / (1 - toyArea u v) := by
  unfold toyConformal
  field_simp [hX, hden]

/-- U-null constraint, divided by r, at the leading homogeneous degree. -/
theorem leading_null_u (u v k : ℝ)
    (hu : u ≠ 0) (hz : u + v ≠ 0) :
    -(1 : ℝ) / (4 * (u + v) ^ 2) +
      2 * ((1 / 4 + k) / (u + v) - k / u) *
        (1 / (2 * (u + v))) +
      k * v / (u * (u + v) ^ 2) = 0 := by
  field_simp
  <;> ring

/-- V-null constraint: the symmetric counterpart of leading_null_u. -/
theorem leading_null_v (u v k : ℝ)
    (hv : v ≠ 0) (hz : u + v ≠ 0) :
    -(1 : ℝ) / (4 * (u + v) ^ 2) +
      2 * ((1 / 4 + k) / (u + v) - k / v) *
        (1 / (2 * (u + v))) +
      k * u / (v * (u + v) ^ 2) = 0 := by
  field_simp
  <;> ring

/-- Mixed Einstein sigma equation: sigma_uv - r_uv/r - 4pi phi_u phi_v=0.
    The leading phi_u*phi_v is -k/(4pi*(u+v)^2). -/
theorem leading_sigma_uv (u v k : ℝ)
    (hz : u + v ≠ 0) :
    -(1 / 4 + k) / ((u + v) ^ 2) +
      1 / (4 * (u + v) ^ 2) +
      k / ((u + v) ^ 2) = 0 := by
  field_simp
  <;> ring

/-- The scalar transport equation after inserting the predicted
    angular derivatives reduces to this rational identity. -/
theorem leading_scalar_transport (u v : ℝ)
    (huv : u + v ≠ 0) :
    (u - v) / (2 * (u + v) ^ 2) +
      (v - u) / (2 * (u + v) ^ 2) = 0 := by
  field_simp
  <;> ring

end GammaHalf
