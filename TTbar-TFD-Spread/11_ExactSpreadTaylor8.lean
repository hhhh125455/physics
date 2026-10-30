import Mathlib

/-!
TTbar/TFD Part 11: exact finite-u t^8 coefficient of the
Cardy-saddle TFD spread complexity.

All polynomial/rational identities are in real arithmetic.
The finite Jacobi path enumeration is proved, with the first
five Krylov sites sufficient for the order-t^8 coefficient.
This does not by itself formalize the convergence of the
infinite-dimensional unitary time evolution.
-/

namespace TTbarExactSpread8

def action (x y z g h q r : ℝ) (v : Fin 5 → ℝ) : Fin 5 → ℝ := fun n =>
  if n = 0 then g*v 1
  else if n = 1 then v 0 + x*v 1 + h*v 2
  else if n = 2 then v 1 + y*v 2 + q*v 3
  else if n = 3 then v 2 + z*v 3 + r*v 4
  else v 3

def start : Fin 5 → ℝ := fun n => if n = 0 then 1 else 0

def path (x y z g h q r : ℝ) : ℕ → Fin 5 → ℝ
  | 0 => start
  | k+1 => action x y z g h q r (path x y z g h q r k)

noncomputable def evenSite (x y z g h q r : ℝ)
    (m : ℕ) (n : Fin 5) : ℝ :=
  (-1 : ℝ)^m *
    ∑ k ∈ Finset.range (2*m+1),
      (-1 : ℝ)^k * (path x y z g h q r k n) *
      (path x y z g h q r (2*m-k) n) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (2*m-k) : ℝ))

noncomputable def c8 (x y z g h q r : ℝ) : ℝ :=
    g * evenSite x y z g h q r 4 1
    + 2*g*h * evenSite x y z g h q r 4 2
    + 3*g*h*q * evenSite x y z g h q r 4 3
    + 4*g*h*q*r * evenSite x y z g h q r 4 4

/-- Universal t^8 coefficient, before substituting any thermal model. -/
theorem c8_universal (x y z g h q r : ℝ) :
    c8 x y z g h q r =
    -g*(64*g^3+66*g^2*h+48*g^2*x^2
       -60*g*h^2+44*g*h*q+12*g*h*x^2
       +48*g*h*x*y-12*g*h*y^2+12*g*x^4
       -62*h^3-12*h^2*q-36*h^2*x^2
       +48*h^2*x*y-39*h^2*y^2
       +50*h*q^2-20*h*q*r+3*h*q*x^2
       +18*h*q*x*y+2*h*q*x*z+3*h*q*y^2
       -26*h*q*y*z+15*h*q*z^2
       -2*h*x^4+18*h*x^3*y-18*h*x^2*y^2
       +16*h*x*y^3-6*h*y^4+x^6)/20160 := by
  simp [c8, evenSite, path, action, start, Finset.sum_range_succ]
  ring

noncomputable def modelY (u : ℝ) : ℝ := 3*(8*u+5)/(4*u+3)
noncomputable def modelZ (u : ℝ) : ℝ :=
  36*(u+1)^2*(16*u^2+24*u+7) /
    ((4*u+3)*(16*u^3+48*u^2+45*u+12))
noncomputable def modelQ (u : ℝ) : ℝ :=
  6*(16*u^3+48*u^2+45*u+12)/(4*u+3)^2
noncomputable def modelR (u : ℝ) : ℝ :=
  8*(4*u+3)*(64*u^6+480*u^5+1440*u^4+
    2175*u^3+1710*u^2+648*u+90)/
    (16*u^3+48*u^2+45*u+12)^2

/-- Exact finite-u coefficient for x=t/beta at order x^8. -/
theorem c8_model (u : ℝ) (hu : 0 < u) :
    c8 3 (modelY u) (modelZ u) (2*u) (4*u+3)
      (modelQ u) (modelR u) =
      -3*u*(24*u^4+80*u^3+90*u^2+39*u+6)/
        (2*(4*u+3)*(16*u^3+48*u^2+45*u+12)) := by
  rw [c8_universal]
  unfold modelY modelZ modelQ modelR
  have h1 : 4*u+3 ≠ 0 := by positivity
  have h2 : 16*u^3+48*u^2+45*u+12 ≠ 0 := by positivity
  field_simp [h1, h2]
  ring

end TTbarExactSpread8
