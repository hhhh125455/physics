import Mathlib

/-!
# Characteristic-corner identities for the charged area equation

For X = r^2 and E = exp(-2*sigma), the Einstein evolution equation is

    X_UV = E / 2 * (q^2 / X - 1).

Near X=0 with 0<X<q^2 and E>0, the mixed derivative is positive.

This file formalizes:
* positivity of the exact charge source;
* nonnegative mixed derivatives imply a supermodular corner inequality
  (by two applications of the mean value theorem);
* the exact algebraic source scaling under X_e(x,y)=X(e*x,e*y)/e;
* a conditional square-root sandwich for the area-radius observable.

The existence of a PDE solution and uniform parameter bounds are not asserted.
-/

namespace GammaHalf

theorem charged_source_positive (X E q : ℝ)
    (hX : 0 < X) (hE : 0 < E) (hcharge : X < q ^ 2) :
    0 < E / 2 * (q ^ 2 / X - 1) := by
  have hXne : X ≠ 0 := ne_of_gt hX
  have hpos : 0 < (q ^ 2 - X) / X :=
    div_pos (sub_pos.mpr hcharge) hX
  have heq : q ^ 2 / X - 1 = (q ^ 2 - X) / X := by
    field_simp
    ring
  rw [heq]
  exact mul_pos (div_pos hE (by norm_num)) hpos

/-- This is a genuine calculus statement: positive mixed derivative of
    X(U,V) implies nonnegative characteristic rectangle cross-difference.
    Derivatives are taken in the order U then V. -/
theorem corner_supermodular
    (X : ℝ → ℝ → ℝ)
    (hX : ∀ v, Differentiable ℝ (fun u => X u v))
    (hXu : ∀ u, Differentiable ℝ (fun v => deriv (fun z => X z v) u))
    (hXuv : ∀ u v, 0 ≤ deriv (fun y => deriv (fun z => X z y) u) v)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    X u v + X 0 0 ≥ X u 0 + X 0 v := by
  have hmonov (z : ℝ) :
      Monotone (fun y => deriv (fun t => X t y) z) :=
    monotone_of_deriv_nonneg (hXu z) (hXuv z)
  have hD (z : ℝ) :
      0 ≤ deriv (fun t => X t v - X t 0) z := by
    have hmv : deriv (fun t => X t 0) z ≤
        deriv (fun t => X t v) z := hmonov z hv
    have hdv : HasDerivAt (fun t => X t v)
        (deriv (fun t => X t v) z) z := (hX v z).hasDerivAt
    have hd0 : HasDerivAt (fun t => X t 0)
        (deriv (fun t => X t 0) z) z := (hX 0 z).hasDerivAt
    rw [(hdv.sub hd0).deriv]
    linarith
  have hmonou : Monotone (fun z => X z v - X z 0) :=
    monotone_of_deriv_nonneg ((hX v).sub (hX 0)) hD
  have h := hmonou hu
  dsimp at h
  linarith

/-- The exact source rescales under a corner blow-up X_e=X/e.
    The second, nonsingular term is explicitly of order epsilon. -/
theorem rescaled_charged_source
    (eps X E q : ℝ)
    (heps : eps ≠ 0) (hX : X ≠ 0) :
    eps * (E / 2 * (q ^ 2 / X - 1)) =
       E / 2 * (q ^ 2 / (X / eps) - eps) := by
  field_simp
  ring

/-- Conditional bounds on the characteristic area produce sqrt-bounds
    on the areal radius. This does not establish the PDE hypotheses. -/
theorem area_to_radius_sandwich
    (delta r low high : ℝ)
    (hdelta : 0 ≤ delta) (hr : 0 ≤ r)
    (hlow : 0 ≤ low) (hhigh : 0 ≤ high)
    (h1 : low * delta ≤ r ^ 2)
    (h2 : r ^ 2 ≤ high * delta) :
    Real.sqrt (low * delta) ≤ r ∧
      r ≤ Real.sqrt (high * delta) := by
  have hl : Real.sqrt (low * delta) ≤ Real.sqrt (r ^ 2) :=
    Real.sqrt_le_sqrt h1
  have hh : Real.sqrt (r ^ 2) ≤ Real.sqrt (high * delta) :=
    Real.sqrt_le_sqrt h2
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hr] using And.intro hl hh

end GammaHalf
