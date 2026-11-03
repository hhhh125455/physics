import Mathlib

/-!
# A weaker sufficient condition for gamma = 1/2 than a derivative limit

The new arXiv:2610.40043 tests the *limit*
  -d_A X_S -> c_* > 0.

This theorem isolates a weaker and more stable target: on a
one-sided subcritical interval a < A*, it is enough that
  0 < b <= -d_A X_S <= B < infinity.
No pointwise limit of the derivative at A* is needed.

Continuity up to A* (where X_S=0), differentiability strictly
inside, and these derivative bounds imply
  b (A*-a) <= X_S(a) <= B (A*-a).
Consequently r_S=sqrt(X_S) has a two-sided sqrt law. These
are calculus theorems, but the Einstein PDE has not yet been
proved to satisfy the derivative bounds.
-/

namespace GammaHalf

private theorem affine_interval_monotone
    (f : ℝ → ℝ) (a b C : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
    (hderiv : ∀ x ∈ Set.Ioo a b, 0 ≤ deriv f x + C) :
    MonotoneOn (fun x => f x + C*x) (Set.Icc a b) := by
  have hc : ContinuousOn (fun x : ℝ => C * x) (Set.Icc a b) :=
    (continuous_const.mul continuous_id).continuousOn
  have hgcont : ContinuousOn (fun x => f x + C*x) (Set.Icc a b) :=
    hcont.add hc
  have hgdiff : DifferentiableOn ℝ (fun x => f x + C*x)
      (Set.Ioo a b) := by
    intro x hx
    have hf : HasDerivAt f (deriv f x) x := (hdiff x hx).hasDerivAt
    have hlin : HasDerivAt (fun t : ℝ => C*t) C x := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id x).const_mul C
    have hfun : (fun t : ℝ => f t + C*t) =
        f + (fun t : ℝ => C*t) := by
      funext t
      rfl
    rw [hfun]
    exact (hf.add hlin).differentiableAt.differentiableWithinAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hgcont
  · simpa only [interior_Icc] using hgdiff
  · intro x hx
    have hx' : x ∈ Set.Ioo a b := by
      simpa only [interior_Icc] using hx
    have hf : HasDerivAt f (deriv f x) x := (hdiff x hx').hasDerivAt
    have hlin : HasDerivAt (fun t : ℝ => C*t) C x := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id x).const_mul C
    have hfun : (fun t : ℝ => f t + C*t) =
        f + (fun t : ℝ => C*t) := by
      funext t
      rfl
    have heq : deriv (fun t => f t + C*t) x = deriv f x + C := by
      rw [hfun]
      exact (hf.add hlin).deriv
    rw [heq]
    exact hderiv x hx'

theorem one_sided_derivative_bounds_imply_linear_area
    (f : ℝ → ℝ) (a astar b B : ℝ)
    (hab : a ≤ astar) (hb : 0 < b) (hB : b ≤ B)
    (hcont : ContinuousOn f (Set.Icc a astar))
    (hdiff : ∀ x ∈ Set.Ioo a astar, DifferentiableAt ℝ f x)
    (hlo : ∀ x ∈ Set.Ioo a astar, -B ≤ deriv f x)
    (hhi : ∀ x ∈ Set.Ioo a astar, deriv f x ≤ -b)
    (hzero : f astar = 0) :
    b * (astar-a) ≤ f a ∧ f a ≤ B*(astar-a) := by
  have hA : a ∈ Set.Icc a astar := ⟨le_rfl, hab⟩
  have hS : astar ∈ Set.Icc a astar := ⟨hab, le_rfl⟩
  have huppermono :
      MonotoneOn (fun x => f x + B*x) (Set.Icc a astar) :=
    affine_interval_monotone f a astar B hab hcont hdiff
      (by
        intro x hx
        linarith [hlo x hx])
  have hnegcont : ContinuousOn (fun x => -f x) (Set.Icc a astar) :=
    hcont.neg
  have hnegdiff : ∀ x ∈ Set.Ioo a astar,
      DifferentiableAt ℝ (fun t => -f t) x := by
    intro x hx
    exact (hdiff x hx).neg
  have hnegderiv : ∀ x ∈ Set.Ioo a astar,
      0 ≤ deriv (fun t => -f t) x - b := by
    intro x hx
    have hf : HasDerivAt f (deriv f x) x := (hdiff x hx).hasDerivAt
    have hneg : deriv (fun t => -f t) x = - deriv f x :=
      hf.neg.deriv
    rw [hneg]
    linarith [hhi x hx]
  have hlowerMono :
      MonotoneOn (fun x => -f x + (-b)*x) (Set.Icc a astar) :=
    affine_interval_monotone (fun x => -f x) a astar (-b)
      hab hnegcont hnegdiff
      (by
        intro x hx
        simpa only [sub_eq_add_neg] using hnegderiv x hx)
  have hup := huppermono hA hS hab
  have hlow := hlowerMono hA hS hab
  dsimp at hup hlow
  rw [hzero] at hup hlow
  constructor <;> nlinarith

/-- The radius is squeezed between square roots once the
    monotone response bounds above are available. -/
theorem one_sided_area_bounds_imply_sqrt_radius
    (r a astar b B : ℝ)
    (hr : 0 ≤ r) (hdelta : a ≤ astar)
    (hb : 0 < b) (hB : b ≤ B)
    (hlo : b*(astar-a) ≤ r^2)
    (hhi : r^2 ≤ B*(astar-a)) :
    Real.sqrt (b*(astar-a)) ≤ r ∧
      r ≤ Real.sqrt (B*(astar-a)) := by
  have h1 := Real.sqrt_le_sqrt hlo
  have h2 := Real.sqrt_le_sqrt hhi
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hr] using
    And.intro h1 h2

end GammaHalf
