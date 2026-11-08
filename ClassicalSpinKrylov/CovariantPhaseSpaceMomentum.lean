import Mathlib
import ClassicalSpinKrylov.CovariantPhaseSpaceAudit

/-!
# D3A: Euler-Lagrange expression and Ostrogradsky endpoint momenta

This module connects the finite-sum momentum definition to the
Euler-Lagrange expression. It proves the identity E = F_0 - D p_0
for an abstract linear differential operator D.
-/

namespace CovariantPhaseSpaceAudit

section HigherDerivativeEulerIdentity

variable {K V : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]

/-- Reverse-indexed finite Euler-Lagrange sum:
F_0 + sum_{m=1}^k (-D)^m F_m. -/
def higherOrderEulerExpression
    (D : V →ₗ[K] V) (F : ℕ → V) (k : ℕ) : V :=
  F 0 + ∑ r ∈ Finset.range k, ((-D) ^ (k - r)) (F (k - r))

/-- Applying D to (-D)^n gives -(-D)^(n+1). -/
lemma D_apply_neg_pow
    (D : V →ₗ[K] V) (n : ℕ) (v : V) :
    D (((-D) ^ n) v) = -(((-D) ^ (n + 1)) v) := by
  calc
    D (((-D) ^ n) v) = -((-D) (((-D) ^ n) v)) := by simp
    _ = -(((-D) ^ (n + 1)) v) := by
      rw [pow_succ']
      rfl

/-- The finite-order Euler-Lagrange expression is F_0 - D p_0,
where p_0 is the Ostrogradsky momentum defined in the audit module. -/
theorem higherOrderEuler_eq_F0_sub_D_momentum
    (D : V →ₗ[K] V) (F : ℕ → V) (k : ℕ) :
    higherOrderEulerExpression D F k =
      F 0 - D (higherOrderMomentum D F k 0) := by
  unfold higherOrderEulerExpression higherOrderMomentum
  rw [map_sum]
  simp only [Nat.sub_zero]
  have hsum :
      (∑ r ∈ Finset.range k, ((-D) ^ (k - r)) (F (k - r))) =
        -(∑ r ∈ Finset.range k,
          D (((-D) ^ (k - 1 - r)) (F (k - r))) ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hrlt : r < k := Finset.mem_range.mp hr
    have hidx : k - r = (k - 1 - r) + 1 := by omega
    rw [hidx]
    exact D_apply_neg_pow D (k - 1 - r) (F (k - r))
  calc
    F 0 + (∑ r ∈ Finset.range k, ((-D) ^ (k - r)) (F (k - r))) =
        F 0 + -(∑ r ∈ Finset.range k,
          D (((-D) ^ (k - 1 - r)) (F (k - r))) ) :=
      congrArg (fun x => F 0 + x) hsum
    _ = F 0 - (∑ r ∈ Finset.range k,
          D (((-D) ^ (k - 1 - r)) (F (k - r))) ) := by simp

end HigherDerivativeEulerIdentity

end CovariantPhaseSpaceAudit
