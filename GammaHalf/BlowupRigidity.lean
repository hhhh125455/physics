import Mathlib

/-!
# Rigidity of a symmetric first-order free-wave blow-up profile

Suppose a corner blow-up of the areal variable X=r^2 exists, satisfies
the homogeneous 1+1 wave equation (so F(u,v)=f(u)+g(v)), is symmetric
under u<->v, is homogeneous of degree one and vanishes at the tip.

Then on the nonnegative quadrant it MUST have the form
  F(u,v)=c*(u+v), c=F(1,0).

The theorem below formalizes this exact conclusion.
It does not prove that a blow-up limit exists, is differentiable, has
zero mixed derivative, or possesses c>0 for the charged Einstein system.
-/

namespace GammaHalf

theorem symmetric_free_wave_blowup_rigidity
    (F : ℝ → ℝ → ℝ) (f g : ℝ → ℝ)
    (hsep : ∀ u v, F u v = f u + g v)
    (hsym : ∀ u v, F u v = F v u)
    (hcorner : F 0 0 = 0)
    (hscale : ∀ t u v : ℝ, 0 ≤ t →
      F (t * u) (t * v) = t * F u v)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    F u v = F 1 0 * (u + v) := by
  have hcross : F u v = F u 0 + F 0 v - F 0 0 := by
    simp only [hsep]
    ring
  have hU : F u 0 = u * F 1 0 := by
    simpa only [mul_one, mul_zero] using (hscale u 1 0 hu)
  have hV : F 0 v = v * F 0 1 := by
    simpa only [mul_zero, mul_one] using (hscale v 0 1 hv)
  calc
    F u v = F u 0 + F 0 v - F 0 0 := hcross
    _ = u * F 1 0 + v * F 0 1 := by rw [hU, hV, hcorner]; ring
    _ = F 1 0 * (u + v) := by rw [hsym 0 1]; ring

end GammaHalf
