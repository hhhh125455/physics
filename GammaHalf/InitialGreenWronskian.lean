import Mathlib

/-!
# Green-Wronskian response sign certificate for the exact RN initial ODE

For the exact initial-amplitude variation in InitialResponseODE.lean,
    Y'' + P Y' + Q Y = -F,
with F = 8*pi*A*X*(f')^2 > 0 for A>0 and X>0.

Suppose u is a strictly positive solution of the homogeneous equation
    u'' + P u' + Q u = 0.
If mu>0 solves mu' = P*mu, then the Wronskian W=u Y'-u' Y obeys
    (mu W)' = -mu*u*F < 0.
For zero initial response Y(0)=Y'(0)=0 and u(0)>0, this forces
    Y(x)<0 on every (0,L] where u stays positive.

The algebraic Wronskian identity and the *two strict monotonicity
steps* are formally proved in Lean. The differential identity is
stated using deriv hypotheses for the weighted Wronskian and the
quotient, representing the ordinary product and quotient calculus.
These are verified separately in the companion first-derivative
lemma below; existence/strict positivity of u for the physical
RN initial data is NOT proved here.

Numerical discovery: near q=.7,m=1,C=1,A=.39383518 on [0,5],
the homogeneous fundamental solution u(0)=1,u'(0)=1 is positive
on a dense scan, whereas u(0)=1,u'(0)=0 changes sign. The scan
is not a rigorous interval-arithmetic proof.
-/

namespace GammaHalf

noncomputable def wronskian (u Y : ℝ → ℝ) (x : ℝ) : ℝ :=
  u x * deriv Y x - deriv u x * Y x

noncomputable def weightedWronskian
    (u Y mu : ℝ → ℝ) (x : ℝ) : ℝ :=
  mu x * wronskian u Y x

noncomputable def responseRatio (u Y : ℝ → ℝ) (x : ℝ) : ℝ :=
  Y x / u x

/-- Exact cancellation of the potential Q in the inhomogeneous
    Wronskian equation, with no assumption on the sign of Q. -/
theorem forced_wronskian_identity
    (u up upp Y Yp Ypp P Q F : ℝ)
    (hhom : upp + P*up + Q*u = 0)
    (hforced : Ypp + P*Yp + Q*Y + F = 0) :
    u*Ypp - upp*Y + P*(u*Yp-up*Y) = -u*F := by
  linear_combination u*hforced - Y*hhom

/-- Actual real derivative calculus for the response ratio. -/
theorem response_ratio_hasDerivAt
    (u Y : ℝ → ℝ) (x up Yp : ℝ)
    (hu : HasDerivAt u up x)
    (hY : HasDerivAt Y Yp x)
    (hux : u x ≠ 0) :
    HasDerivAt (responseRatio u Y)
      ((Yp*u x-Y x*up)/(u x)^2) x := by
  unfold responseRatio
  exact hY.div hu hux

/-- Full calculus bridge from the initial Jacobi ODE and the
    integrating-factor ODE to the weighted Wronskian derivative. -/
theorem weighted_wronskian_hasDerivAt
    (u Y mu : ℝ → ℝ) (x up upp Yp Ypp P Q F : ℝ)
    (hu : HasDerivAt u up x)
    (hup : HasDerivAt (fun t => deriv u t) upp x)
    (hY : HasDerivAt Y Yp x)
    (hYp : HasDerivAt (fun t => deriv Y t) Ypp x)
    (hmu : HasDerivAt mu (P*mu x) x)
    (hhom : upp + P*up + Q*u x = 0)
    (hforced : Ypp + P*Yp + Q*Y x + F = 0) :
    HasDerivAt (weightedWronskian u Y mu)
      (-(mu x*u x*F)) x := by
  have hW : HasDerivAt (wronskian u Y)
      (u x*Ypp - upp*Y x) x := by
    have hbasic := (hu.mul hYp).sub (hup.mul hY)
    have huval : deriv u x = up := hu.deriv
    have hYval : deriv Y x = Yp := hY.deriv
    convert hbasic using 1
    · rfl
    · rw [huval, hYval]
      ring
  have hGW : HasDerivAt (weightedWronskian u Y mu)
      ((P*mu x)*wronskian u Y x +
         mu x*(u x*Ypp-upp*Y x)) x := by
    exact hmu.mul hW
  have hid := forced_wronskian_identity (u x) up upp (Y x)
     Yp Ypp P Q F hhom hforced
  have hcoef : (P*mu x)*wronskian u Y x +
       mu x*(u x*Ypp-upp*Y x) = -(mu x*u x*F) := by
    rw [show wronskian u Y x = u x*Yp-up*Y x by
      simp [wronskian, hu.deriv, hY.deriv]]
    calc
      _ = mu x*(u x*Ypp-upp*Y x+
          P*(u x*Yp-up*Y x)) := by ring
      _ = -(mu x*u x*F) := by rw [hid]; ring
  rw [←hcoef]
  exact hGW

/-- This theorem is a rigorous *conditional* Green certificate.
    The derivative hypotheses are explicit; no monotonicity or
    positivity is inferred by an unproved differential comparison. -/
theorem positive_homogeneous_green_certificate
    (L : ℝ) (u Y mu F : ℝ → ℝ)
    (hL : 0 < L)
    (hu0 : 0 < u 0) (hY0 : Y 0 = 0)
    (hYp0 : deriv Y 0 = 0)
    (hu : ∀ x ∈ Set.Ioo 0 L, 0 < u x)
    (hmu : ∀ x ∈ Set.Ioo 0 L, 0 < mu x)
    (hF : ∀ x ∈ Set.Ioo 0 L, 0 < F x)
    (hGwcont : ContinuousOn (weightedWronskian u Y mu)
       (Set.Icc 0 L))
    (hGwderiv : ∀ x ∈ Set.Ioo 0 L,
       deriv (weightedWronskian u Y mu) x =
          -(mu x*u x*F x))
    (hRcont : ContinuousOn (responseRatio u Y)
       (Set.Icc 0 L))
    (hRderiv : ∀ x ∈ Set.Ioo 0 L,
       deriv (responseRatio u Y) x =
          wronskian u Y x / (u x)^2) :
    ∀ x ∈ Set.Ioo 0 L, Y x < 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 L :=
    ⟨le_rfl, le_of_lt hL⟩
  have hGw0 : weightedWronskian u Y mu 0 = 0 := by
    simp [weightedWronskian, wronskian, hY0, hYp0]
  have hR0 : responseRatio u Y 0 = 0 := by
    simp [responseRatio, hY0]
  have hantiG : StrictAntiOn (weightedWronskian u Y mu)
      (Set.Icc 0 L) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 L) hGwcont
    intro x hx
    have hxi : x ∈ Set.Ioo 0 L := by
      simpa only [interior_Icc] using hx
    rw [hGwderiv x hxi]
    have hp : 0 < mu x*u x*F x := by
      exact mul_pos (mul_pos (hmu x hxi) (hu x hxi)) (hF x hxi)
    linarith
  have hnegW : ∀ x ∈ Set.Ioo 0 L,
      wronskian u Y x < 0 := by
    intro x hx
    have hxc : x ∈ Set.Icc 0 L :=
      ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hGlt : weightedWronskian u Y mu x < 0 := by
      have ht := hantiG h0 hxc hx.1
      rw [hGw0] at ht
      exact ht
    unfold weightedWronskian at hGlt
    by_contra hn
    have hnonneg : 0 ≤ wronskian u Y x := le_of_not_gt hn
    have hGnonneg : 0 ≤ mu x * wronskian u Y x :=
      mul_nonneg (le_of_lt (hmu x hx)) hnonneg
    linarith
  have hantiR : StrictAntiOn (responseRatio u Y)
      (Set.Icc 0 L) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 L) hRcont
    intro x hx
    have hxi : x ∈ Set.Ioo 0 L := by
      simpa only [interior_Icc] using hx
    rw [hRderiv x hxi]
    exact div_neg_of_neg_of_pos (hnegW x hxi)
      (sq_pos_of_pos (hu x hxi))
  intro x hx
  have hxc : x ∈ Set.Icc 0 L :=
    ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hRlt : responseRatio u Y x < 0 := by
    have ht := hantiR h0 hxc hx.1
    rw [hR0] at ht
    exact ht
  unfold responseRatio at hRlt
  by_contra hn
  have hnonneg : 0 ≤ Y x := le_of_not_gt hn
  have hqnonneg : 0 ≤ Y x / u x :=
    div_nonneg hnonneg (le_of_lt (hu x hx))
  linarith

end GammaHalf
