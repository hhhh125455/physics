import Mathlib

/-!
Infinitesimal angular displacement:
Exact algebraic identities for the first-order rotation map
T_a(t) r = r + t (a × r).

No theorem silently discards higher-order terms.
The Rodrigues-to-tangent approximation is NOT proved here.
-/

namespace InfinitesimalRotation

theorem cross_add_x (ay az by bz y z : ℝ) :
    (ay + by) * z - (az + bz) * y =
      (ay*z - az*y) + (by*z - bz*y) := by ring

theorem cross_add_y (ax az bx bz x z : ℝ) :
    (az + bz) * x - (ax + bx) * z =
      (az*x - ax*z) + (bz*x - bx*z) := by ring

theorem cross_add_z (ax ay bx by x y : ℝ) :
    (ax + bx) * y - (ay + by) * x =
      (ax*y - ay*x) + (bx*y - by*x) := by ring

-- T_b(t)(T_a(t)r) = r + t (a+b)×r + t² b×(a×r), for all t.
theorem compose_x (t ax ay az bx by bz x y z : ℝ) :
    x + t*(ay*z-az*y) +
      t*(by*(z+t*(ax*y-ay*x)) - bz*(y+t*(az*x-ax*z))) =
    x + t*((ay+by)*z-(az+bz)*y) +
      t^2*(by*(ax*y-ay*x)-bz*(az*x-ax*z)) := by ring

theorem compose_y (t ax ay az bx by bz x y z : ℝ) :
    y + t*(az*x-ax*z) +
      t*(bz*(x+t*(ay*z-az*y)) - bx*(z+t*(ax*y-ay*x))) =
    y + t*((az+bz)*x-(ax+bx)*z) +
      t^2*(bz*(ay*z-az*y)-bx*(ax*y-ay*x)) := by ring

theorem compose_z (t ax ay az bx by bz x y z : ℝ) :
    z + t*(ax*y-ay*x) +
      t*(bx*(y+t*(az*x-ax*z)) - by*(x+t*(ay*z-az*y))) =
    z + t*((ax+bx)*y-(ay+by)*x) +
      t^2*(bx*(az*x-ax*z)-by*(ay*z-az*y)) := by ring

-- [b×,a×]r = (b×a)×r, componentwise.
theorem commutator_x (ax ay az bx by bz x y z : ℝ) :
    (by*(ax*y-ay*x)-bz*(az*x-ax*z)) -
      (ay*(bx*y-by*x)-az*(bz*x-bx*z)) =
    (bz*ax-bx*az)*z-(bx*ay-by*ax)*y := by ring

theorem commutator_y (ax ay az bx by bz x y z : ℝ) :
    (bz*(ay*z-az*y)-bx*(ax*y-ay*x)) -
      (az*(by*z-bz*y)-ax*(bx*y-by*x)) =
    (bx*ay-by*ax)*x-(by*az-bz*ay)*z := by ring

theorem commutator_z (ax ay az bx by bz x y z : ℝ) :
    (bx*(az*x-ax*z)-by*(ay*z-az*y)) -
      (ax*(bz*x-bx*z)-ay*(by*z-bz*y)) =
    (by*az-bz*ay)*y-(bz*ax-bx*az)*x := by ring

theorem noncommuting_example (t : ℝ) :
    t^2 * ((0:ℝ)-1) = -t^2 := by ring

-- Explicit limit checks, with no axioms added.
theorem quadratic_correction_tends_zero (c : ℝ) :
    Filter.Tendsto (fun t : ℝ => t^2*c) (nhds 0) (nhds 0) := by
  have hc : Continuous (fun t : ℝ => t^2*c) :=
    (continuous_id.pow 2).mul continuous_const
  simpa using hc.tendsto (0 : ℝ)

theorem first_order_remainder_tends_zero (c : ℝ) :
    Filter.Tendsto (fun t : ℝ => t*c) (nhds 0) (nhds 0) := by
  have hc : Continuous (fun t : ℝ => t*c) :=
    continuous_id.mul continuous_const
  simpa using hc.tendsto (0 : ℝ)

end InfinitesimalRotation
