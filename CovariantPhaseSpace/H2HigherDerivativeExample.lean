import Mathlib

/-!
# H2 explicit check on a regular higher-derivative mechanical model

Model L = (1/2) (q¨)^2 with equation q'''' = 0.
A solution is q(t) = a + b*t + (c/2)*t^2 + (d/6)*t^3.
At t = 0 the independent solution data are (a,b,c,d).
The D3A endpoint potential is θ = -d δa + c δb.
Ostrogradsky initial data are (q,qdot,p0,p1) = (a,b,-d,c).

The equality below is a direct comparison of the 2-form from
antisymmetrized variations of θ and the canonical
dp0 ∧ dq + dp1 ∧ dqdot on Ostrogradsky data. It demonstrates H2
in this non-gauge 4-dimensional example, not general H2 for PDEs.
-/

namespace CovariantPhaseSpace

section HigherDerivativeExample

/-- Initial-data coordinates (q,qdot,p0,p1) obtained from
the solution coefficients (a,b,c,d). -/
def higherDerivativeInitialData (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![u 0, u 1, -u 3, u 2]

/-- Endpoint potential in solution coefficients, θ = -d δa + c δb. -/
def higherDerivativeTheta (base variation : Fin 4 → ℝ) : ℝ :=
  -(base 3) * variation 0 + base 2 * variation 1

/-- Covariant presymplectic form δθ calculated on two independent
variations of the solution parameters. -/
def higherDerivativeCovariantOmega (u v : Fin 4 → ℝ) : ℝ :=
  higherDerivativeTheta u v - higherDerivativeTheta v u

/-- Canonical form dp0 ∧ dq + dp1 ∧ dqdot in Ostrogradsky coordinates. -/
def higherDerivativeCanonicalOmega (x y : Fin 4 → ℝ) : ℝ :=
  x 2 * y 0 - y 2 * x 0 + x 3 * y 1 - y 3 * x 1

/-- H2 tested explicitly for L=(q¨)^2/2: the covariant 2-form
coincides with the pullback of the canonical Ostrogradsky 2-form. -/
theorem higher_derivative_symplectic_pullback
    (u v : Fin 4 → ℝ) :
    higherDerivativeCovariantOmega u v =
      higherDerivativeCanonicalOmega
        (higherDerivativeInitialData u)
        (higherDerivativeInitialData v) := by
  simp [higherDerivativeCovariantOmega, higherDerivativeTheta,
    higherDerivativeCanonicalOmega, higherDerivativeInitialData]
  ring

end HigherDerivativeExample

end CovariantPhaseSpace
