import Mathlib

/-!
Exact finite-u Taylor coefficients of TFD spread complexity in
Z0(beta)=exp(A/beta), without an early large-u expansion.

We use the diagonal-shift-invariant Jacobi parameters
x=alpha1-alpha0, y=alpha2-alpha0, g=b1²,h=b2²,q=b3²
in dimensionless energy units. psi_n=B_n*v_n with
B_n=b1...bn, and the transformed tridiagonal action is below.
Terms of order t^6 only see n<=3.

The finite Taylor path calculation is formalized here; extension to
the full unbounded Jacobi evolution requires an analytic-vector
argument and is not itself formalized in this file.
-/
namespace TTbarExactSpread

def action (x y g h q : ℝ) (v : Fin 4 → ℝ) : Fin 4 → ℝ := fun n =>
  if n = 0 then g*v 1
  else if n = 1 then v 0 + x*v 1 + h*v 2
  else if n = 2 then v 1 + y*v 2 + q*v 3
  else v 2

def start : Fin 4 → ℝ := fun n => if n = 0 then 1 else 0

def path (x y g h q : ℝ) : ℕ → Fin 4 → ℝ
  | 0 => start
  | k+1 => action x y g h q (path x y g h q k)

/-- Exact path powers obtained from repeated Jacobi action. -/
theorem p11 (x y g h q : ℝ) : path x y g h q 1 1 = 1 := by
  simp [path, action, start]
theorem p12 (x y g h q : ℝ) : path x y g h q 2 1 = x := by
  simp [path, action, start]
theorem p13 (x y g h q : ℝ) :
    path x y g h q 3 1 = g+h+x^2 := by
  simp [path, action, start]
  ring
theorem p14 (x y g h q : ℝ) :
    path x y g h q 4 1 = 2*g*x+2*h*x+h*y+x^3 := by
  simp [path, action, start]
  ring
theorem p15 (x y g h q : ℝ) :
    path x y g h q 5 1 =
      g^2+2*g*h+3*g*x^2+h^2+h*q+
      3*h*x^2+2*h*x*y+h*y^2+x^4 := by
  simp [path, action, start]
  ring
theorem p22 (x y g h q : ℝ) : path x y g h q 2 2 = 1 := by
  simp [path, action, start]
theorem p23 (x y g h q : ℝ) : path x y g h q 3 2 = x+y := by
  simp [path, action, start]
  ring
theorem p24 (x y g h q : ℝ) :
    path x y g h q 4 2 = g+h+q+x^2+x*y+y^2 := by
  simp [path, action, start]
  ring
theorem p33 (x y g h q : ℝ) : path x y g h q 3 3 = 1 := by
  simp [path, action, start]

/-- Coefficient from a single site in |psi_n(t)|², with all
    factorial and sign factors of exp(-itH). -/
noncomputable def evenSite (x y g h q : ℝ)
    (m : ℕ) (n : Fin 4) : ℝ :=
  (-1 : ℝ)^m *
    ∑ k ∈ Finset.range (2*m+1),
      (-1 : ℝ)^k * (path x y g h q k n) *
      (path x y g h q (2*m-k) n) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (2*m-k) : ℝ))

/-- Each Krylov site contributes n*(b1...bn)². -/
noncomputable def c2 (x y g h q : ℝ) : ℝ :=
  g * evenSite x y g h q 1 1
noncomputable def c4 (x y g h q : ℝ) : ℝ :=
  g * evenSite x y g h q 2 1 +
    2*g*h * evenSite x y g h q 2 2
noncomputable def c6 (x y g h q : ℝ) : ℝ :=
  g * evenSite x y g h q 3 1 +
    2*g*h * evenSite x y g h q 3 2 +
    3*g*h*q * evenSite x y g h q 3 3

/-- Universal time coefficients proved by path enumeration. -/
theorem c2_universal (x y g h q : ℝ) : c2 x y g h q = g := by
  simp [c2, evenSite, path, action, start, Finset.sum_range_succ]
  ring

theorem c4_universal (x y g h q : ℝ) :
    c4 x y g h q = -g*(4*g-2*h+x^2)/12 := by
  simp [c4, evenSite, path, action, start, Finset.sum_range_succ]
  ring

theorem c6_universal (x y g h q : ℝ) :
    c6 x y g h q =
      g*(16*g^2+2*g*h+8*g*x^2-14*h^2+6*h*q-
        2*h*x^2+7*h*x*y-4*h*y^2+x^4)/360 := by
  simp [c6, evenSite, path, action, start, Finset.sum_range_succ]
  ring

/-- Exact model parameters, before any large-u limit. -/
noncomputable def modelY (u : ℝ) : ℝ :=
  (4*u^2+27*u+15)/(4*u+3)-u
noncomputable def modelQ (u : ℝ) : ℝ :=
  6*(16*u^3+48*u^2+45*u+12)/(4*u+3)^2

theorem c2_model (u : ℝ) :
    c2 3 (modelY u) (2*u) (4*u+3) (modelQ u) = 2*u := by
  rw [c2_universal]

theorem c4_model (u : ℝ) :
    c4 3 (modelY u) (2*u) (4*u+3) (modelQ u) = -u/2 := by
  rw [c4_universal]
  ring

theorem c6_model (u : ℝ) (hu : 0 < u) :
    c6 3 (modelY u) (2*u) (4*u+3) (modelQ u) =
      u*(2*u+1)/(4*u+3) := by
  rw [c6_universal]
  unfold modelY modelQ
  have hden : 4*u+3 ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- The classical-leading term is separated ONLY after c6 is formed. -/
theorem c6_classical_split (u : ℝ) (hu : 0 < u) :
    u*(2*u+1)/(4*u+3) = u/2-u/(2*(4*u+3)) := by
  have hden : 4*u+3 ≠ 0 := by positivity
  field_simp [hden]
  ring

end TTbarExactSpread
