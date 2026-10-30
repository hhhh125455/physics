import Mathlib

/-!
# Exact area-equation families with distinct critical exponents

Physical interpretation and LIMITATION:

The charged area evolution equation at q^2 = 1 is
   X_{UV} = E / 2 * (1 / X - 1),   E = exp(-2*sigma).

For any natural number n, let
   X_delta(U,V) = delta^n + U + V + U*V,
   E_delta = 2*X_delta/(1-X_delta).

On each region 0 < X_delta < 1, this is an EXACT solution of the
charged AREA equation, with a positive conformal factor E_delta.

At U=V=0 the radius is sqrt(delta^n), so n=1 gives exponent 1/2
and n=2 gives exponent 1. For delta=0 the two characteristic edges
satisfy X(0,V)=V>0 and X(U,0)=U>0 away from the corner.

THESE ARE NOT CLAIMED TO SATISFY THE OTHER EINSTEIN EQUATIONS
OR THE SCALAR FIELD EQUATION. They prove a logical insufficiency
of the area equation plus characteristic-edge positivity.
-/

namespace GammaHalf

def counterArea (delta : ℝ) (n : ℕ) (u v : ℝ) : ℝ :=
  delta ^ n + u + v + u * v

noncomputable def counterConformal (delta : ℝ) (n : ℕ)
    (u v : ℝ) : ℝ :=
  2 * counterArea delta n u v /
    (1 - counterArea delta n u v)

theorem counter_area_deriv_u (delta : ℝ) (n : ℕ)
    (u v : ℝ) :
    deriv (fun t : ℝ => counterArea delta n t v) u = 1 + v := by
  have heq :
      (fun t : ℝ => counterArea delta n t v) =
        (fun t : ℝ => t * (1 + v) + (delta ^ n + v)) := by
    funext t
    unfold counterArea
    ring
  rw [heq]
  simpa only [id_eq, one_mul] using
    (((hasDerivAt_id u).mul_const (1 + v)).add_const
      (delta ^ n + v)).deriv

/-- A genuine mixed second derivative of the area profile. -/
theorem counter_area_deriv_uv (delta : ℝ) (n : ℕ)
    (u v : ℝ) :
    deriv (fun y : ℝ =>
      deriv (fun x : ℝ => counterArea delta n x y) u) v = 1 := by
  have heq :
      (fun y : ℝ =>
        deriv (fun x : ℝ => counterArea delta n x y) u) =
        (fun y : ℝ => 1 + y) := by
    funext y
    exact counter_area_deriv_u delta n u y
  rw [heq]
  simpa only [id_eq] using ((hasDerivAt_id v).const_add (1 : ℝ)).deriv

theorem counter_exact_source (X : ℝ)
    (hX : X ≠ 0) (hden : 1 - X ≠ 0) :
    (2 * X / (1 - X)) / 2 * (1 / X - 1) = 1 := by
  field_simp
  <;> ring

theorem counter_exact_area_equation (delta : ℝ) (n : ℕ)
    (u v : ℝ)
    (hX : counterArea delta n u v ≠ 0)
    (hden : 1 - counterArea delta n u v ≠ 0) :
    deriv (fun y : ℝ =>
       deriv (fun x : ℝ => counterArea delta n x y) u) v =
     counterConformal delta n u v / 2 *
        (1 / counterArea delta n u v - 1) := by
  rw [counter_area_deriv_uv]
  unfold counterConformal
  exact (counter_exact_source _ hX hden).symm

theorem counter_conformal_positive (X : ℝ)
    (hX : 0 < X) (hsmall : X < 1) :
    0 < 2 * X / (1 - X) := by
  exact div_pos (mul_pos (by norm_num) hX) (sub_pos.mpr hsmall)

/-- The critical corner is zero but both characteristic edges stay positive. -/
theorem critical_edges_positive (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) :
    counterArea 0 1 u 0 = u ∧ counterArea 0 1 0 v = v := by
  simp [counterArea]

theorem linear_corner (delta : ℝ) :
    counterArea delta 1 0 0 = delta := by
  simp [counterArea]

theorem quadratic_corner (delta : ℝ) :
    counterArea delta 2 0 0 = delta ^ 2 := by
  simp [counterArea]

theorem quadratic_corner_radius (delta : ℝ)
    (hdelta : 0 ≤ delta) :
    Real.sqrt (counterArea delta 2 0 0) = delta := by
  rw [quadratic_corner]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg hdelta

/-- An exactly even-in-x scalar ansatz depending only on U+V cannot
    satisfy a nontrivial odd-in-x reflection condition. -/
theorem odd_sum_profile_vanishes
    (f : ℝ → ℝ)
    (hodd : ∀ u v : ℝ, f (u + v) = -f (v + u))
    (u v : ℝ) :
    f (u + v) = 0 := by
  have h := hodd u v
  rw [add_comm v u] at h
  linarith

end GammaHalf
