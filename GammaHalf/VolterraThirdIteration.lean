import Mathlib

/-!
# Third-order Volterra certificate for a Sturm equation

For a self-adjoint initial-value Jacobi equation
    (mu*u')' + mu*Q*u = 0,   u(0)=u'(0)=1,
write its Volterra equation
    u = B - K u,
where B>0 is the free solution and
    (Kf)(x) = integral_0^x [integral_s^x 1/mu(t) dt]
                      mu(s)*Q(s)*f(s) ds.

When mu>0 and Q>=0, K is order-preserving on each
prefix interval [0,T], and K(0)=0.

The important point is that the crude first bound
    L1=B-KB
can be negative while the THIRD lower bound
    L3=B-K(B-K(B-KB))
stays strictly positive.

Lean proves the exact order-iteration theorem:
if u>=0 on [0,T], then L3<=u there.

Therefore, if L3>0 on every prefix, a continuous positive
solution u(0)>0 cannot acquire a first zero. The final
first-zero existence/topology step and interval certification
of L3>0 for the physical RN coefficients remain separate.
-/

namespace GammaHalf

noncomputable def volterraL1
    (K : (ℝ → ℝ) → ℝ → ℝ) (B : ℝ → ℝ) : ℝ → ℝ :=
  fun x => B x - K B x

noncomputable def volterraU1
    (K : (ℝ → ℝ) → ℝ → ℝ) (B : ℝ → ℝ) : ℝ → ℝ :=
  fun x => B x - K (volterraL1 K B) x

noncomputable def volterraL3
    (K : (ℝ → ℝ) → ℝ → ℝ) (B : ℝ → ℝ) : ℝ → ℝ :=
  fun x => B x - K (volterraU1 K B) x

theorem third_volterra_bound_on_positive_prefix
    (T : ℝ) (K : (ℝ → ℝ) → ℝ → ℝ)
    (B u : ℝ → ℝ)
    (hzero : ∀ x ∈ Set.Icc 0 T, K (fun _ => (0:ℝ)) x = 0)
    (hmono : ∀ f g : ℝ → ℝ,
      (∀ x ∈ Set.Icc 0 T, f x ≤ g x) →
      ∀ x ∈ Set.Icc 0 T, K f x ≤ K g x)
    (hfix : ∀ x ∈ Set.Icc 0 T, u x = B x - K u x)
    (hnonneg : ∀ x ∈ Set.Icc 0 T, 0 ≤ u x) :
    ∀ x ∈ Set.Icc 0 T, volterraL3 K B x ≤ u x := by
  have hupper0 : ∀ x ∈ Set.Icc 0 T, u x ≤ B x := by
    intro x hx
    have hk := hmono (fun _ => (0:ℝ)) u hnonneg x hx
    rw [hzero x hx] at hk
    have he := hfix x hx
    linarith
  have hlow1 : ∀ x ∈ Set.Icc 0 T,
      volterraL1 K B x ≤ u x := by
    intro x hx
    have hk := hmono u B hupper0 x hx
    have he := hfix x hx
    dsimp [volterraL1]
    linarith
  have hupper1 : ∀ x ∈ Set.Icc 0 T,
      u x ≤ volterraU1 K B x := by
    intro x hx
    have hk := hmono (volterraL1 K B) u hlow1 x hx
    have he := hfix x hx
    dsimp [volterraU1]
    linarith
  intro x hx
  have hk := hmono u (volterraU1 K B) hupper1 x hx
  have he := hfix x hx
  dsimp [volterraL3]
  linarith

/-- Strict third-order positivity excludes a zero at the end
    of any prefix on which the exact homogeneous solution
    was already known to be nonnegative. -/
theorem third_volterra_excludes_first_zero
    (T : ℝ) (K : (ℝ → ℝ) → ℝ → ℝ)
    (B u : ℝ → ℝ)
    (hT : 0 ≤ T)
    (hzero : ∀ x ∈ Set.Icc 0 T, K (fun _ => (0:ℝ)) x = 0)
    (hmono : ∀ f g : ℝ → ℝ,
      (∀ x ∈ Set.Icc 0 T, f x ≤ g x) →
      ∀ x ∈ Set.Icc 0 T, K f x ≤ K g x)
    (hfix : ∀ x ∈ Set.Icc 0 T, u x = B x - K u x)
    (hnonneg : ∀ x ∈ Set.Icc 0 T, 0 ≤ u x)
    (hlow : 0 < volterraL3 K B T) :
    u T ≠ 0 := by
  have h := third_volterra_bound_on_positive_prefix
     T K B u hzero hmono hfix hnonneg T ⟨hT, le_rfl⟩
  have ht : 0 < u T := lt_of_lt_of_le hlow h
  exact ne_of_gt ht

end GammaHalf
