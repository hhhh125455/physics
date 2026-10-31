import Mathlib

/-!
# Sharp mathematical content of a proposed concavity route

If X_S(A) is concave on [A0,A*], X_S(A*)=0 and
X_S(A0)>0, concavity yields a LINEAR LOWER bound on X_S.

It does *not* yield an upper bound. The explicit concave
family X_S(A)=sqrt(A*-A) has radius r_S=(A*-A)^(1/4)
and violates every putative uniform linear upper bound.

Thus proving second variation X_S''<=0 would yield a
partial critical-exponent bound (gamma<=1/2 within pure
power laws), but NOT the claimed equality gamma=1/2.
The Lean formalization makes no assertion that the
Einstein–Maxwell–scalar evolution actually preserves concavity.
-/

namespace GammaHalf

theorem concavity_yields_linear_lower_area
    (f : ℝ → ℝ) (A0 A Astar : ℝ)
    (h0 : A0 < Astar)
    (hAlo : A0 ≤ A) (hAhi : A ≤ Astar)
    (hzero : f Astar = 0)
    (hconc : ∀ (u v theta : ℝ),
      A0 ≤ u → u ≤ Astar → A0 ≤ v → v ≤ Astar →
      0 ≤ theta → theta ≤ 1 →
      theta*f u + (1-theta)*f v ≤
        f (theta*u+(1-theta)*v)) :
    f A0 * (Astar-A) ≤ f A * (Astar-A0) := by
  let d : ℝ := Astar - A0
  have hd : 0 < d := by dsimp [d]; linarith
  let theta : ℝ := (Astar-A)/d
  have ht0 : 0 ≤ theta := by
    dsimp [theta]
    apply div_nonneg
    · linarith
    · exact le_of_lt hd
  have ht1 : theta ≤ 1 := by
    dsimp [theta]
    exact (div_le_one hd).mpr (by linarith)
  have hcombo : theta*A0 + (1-theta)*Astar = A := by
    have hden : Astar-A0 ≠ 0 := ne_of_gt (sub_pos.mpr h0)
    dsimp [theta,d]
    field_simp [hden]
    ring
  have hcc := hconc A0 Astar theta
    le_rfl (le_of_lt h0) (le_of_lt h0) le_rfl ht0 ht1
  rw [hcombo,hzero] at hcc
  simp only [mul_zero,add_zero] at hcc
  have hscale := mul_le_mul_of_nonneg_right hcc (le_of_lt hd)
  have htheta : theta*d=Astar-A := by
    dsimp [theta]
    field_simp
  have hrel : (theta*f A0)*d = f A0*(Astar-A) := by
    calc
      (theta*f A0)*d = f A0*(theta*d) := by ring
      _ = f A0*(Astar-A) := by rw [htheta]
  rw [hrel] at hscale
  simpa only [d] using hscale

/-- Weighted Jensen inequality for the square-root function. -/
theorem sqrt_weighted_concave
    (s t theta : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hth0 : 0 ≤ theta) (hth1 : theta ≤ 1) :
    theta * Real.sqrt s + (1-theta)*Real.sqrt t
      ≤ Real.sqrt (theta*s+(1-theta)*t) := by
  let a := Real.sqrt s
  let b := Real.sqrt t
  let d := Real.sqrt (theta*s+(1-theta)*t)
  have hwt : 0 ≤ 1-theta := by linarith
  have ha : 0 ≤ a := Real.sqrt_nonneg s
  have hb : 0 ≤ b := Real.sqrt_nonneg t
  have harg : 0 ≤ theta*s+(1-theta)*t :=
    add_nonneg (mul_nonneg hth0 hs) (mul_nonneg hwt ht)
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hsum : 0 ≤ theta*a+(1-theta)*b :=
    add_nonneg (mul_nonneg hth0 ha) (mul_nonneg hwt hb)
  have hdsq : d^2 = theta*a^2+(1-theta)*b^2 := by
    dsimp [d,a,b]
    rw [Real.sq_sqrt harg, Real.sq_sqrt hs, Real.sq_sqrt ht]
  have hdiff :
      d^2 - (theta*a+(1-theta)*b)^2 =
        theta*(1-theta)*(a-b)^2 := by
    rw [hdsq]
    ring
  have hnonneg : 0 ≤ theta*(1-theta)*(a-b)^2 :=
    mul_nonneg (mul_nonneg hth0 hwt) (sq_nonneg _)
  have hsq : (theta*a+(1-theta)*b)^2 ≤ d^2 := by
    linarith [hdiff]
  have hmain : theta*a+(1-theta)*b ≤ d := by
    nlinarith
  exact hmain

/-- Explicit concavity of sqrt(Astar-A) on the one-sided domain. -/
theorem sqrt_endpoint_family_is_concave
    (Astar u v theta : ℝ)
    (hu : u ≤ Astar) (hv : v ≤ Astar)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) :
    theta*Real.sqrt (Astar-u) +
      (1-theta)*Real.sqrt (Astar-v) ≤
      Real.sqrt (Astar-(theta*u+(1-theta)*v)) := by
  have hu' : 0 ≤ Astar-u := by linarith
  have hv' : 0 ≤ Astar-v := by linarith
  have h := sqrt_weighted_concave (Astar-u) (Astar-v) theta
     hu' hv' ht0 ht1
  have harg : theta*(Astar-u)+(1-theta)*(Astar-v) =
      Astar-(theta*u+(1-theta)*v) := by ring
  rwa [harg] at h

/-- No finite linear bound sqrt(delta)<=B*delta can hold as
    delta tends to zero: for every B>0 there is a witness. -/
theorem sqrt_endpoint_has_no_uniform_linear_upper
    (B : ℝ) (hB : 0 < B) :
    ∃ delta : ℝ, 0 < delta ∧
      B*delta < Real.sqrt delta := by
  have hden : 0 < 2*B := by positivity
  have hpos : 0 < (1/(2*B) : ℝ) := by positivity
  let x : ℝ := 1/(2*B)
  refine ⟨x^2, pow_pos hpos _, ?_⟩
  have hroot : Real.sqrt (x^2) = x := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hpos)]
  rw [hroot]
  have hx2 : B*x^2 = x/2 := by
    dsimp [x]
    field_simp
  rw [hx2]
  linarith [hpos]

end GammaHalf
