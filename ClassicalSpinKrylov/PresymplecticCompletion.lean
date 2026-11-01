import Mathlib

/-!
# Presymplectic completion for finite-dimensional solution families

FROZEN CLAIM FROM USER DISCUSSION:

Given a finite-dimensional presymplectic space (V, omega) with kernel
spanned by k_0,...,k_{r-1}, choose r real-valued linear charge
differentials q_a.  Assume the square pairing matrix
  B_{ja} = q_a(k_j)
has nonzero determinant.
Extend V by r candidate conjugate directions R^r and define
  Omega_ext((v,w),(u,z)) =
    omega(v,u) + sum_a [q_a(v) z_a - q_a(u) w_a].
Prove Omega_ext is nondegenerate.  B_{ja} is the TRANSPOSE of the
B_{ab}=dQ_a(v_b) used in the original mathematical statement;
determinant nonvanishing is the same.

These are statements about the linear algebra on tangent spaces.
Lean does NOT prove that the added directions are actual gravitational
boundary degrees of freedom, that Omega_ext is globally closed on
an arbitrary solution manifold, or that the Liouville ensemble is normalizable.
The inputs hker and hspan mathematically encode that the chosen k_j
form a spanning family of the full presymplectic kernel.
-/

namespace PresymplecticCompletion

universe u
variable {V : Type u} [AddCommGroup V] [Module ℝ V]
variable {r : ℕ}

/-- The completed antisymmetric pairing. -/
noncomputable def completedPair
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (q : Fin r → V →ₗ[ℝ] ℝ)
    (p t : V × (Fin r → ℝ)) : ℝ :=
  omega p.1 t.1 +
    ∑ a : Fin r, (q a p.1 * t.2 a - q a t.1 * p.2 a)

/-- The completed form is skew whenever the original form is skew. -/
theorem completedPair_skew
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (q : Fin r → V →ₗ[ℝ] ℝ)
    (hskew : ∀ v u, omega v u = -omega u v)
    (p t : V × (Fin r → ℝ)) :
    completedPair omega q p t = - completedPair omega q t p := by
  simp only [completedPair]
  rw [hskew p.1 t.1]
  simp only [Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- A nondegeneracy lemma formulated directly as a kernel criterion.
hB is exactly injectivity of the charge pairing on the kernel. -/
theorem completedPair_nondegenerate_of_kernel_test
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (q : Fin r → V →ₗ[ℝ] ℝ)
    (k : Fin r → V)
    (hskew : ∀ v u, omega v u = -omega u v)
    (hk : ∀ j u, omega (k j) u = 0)
    (hB : ∀ w : Fin r → ℝ,
      (∀ j : Fin r, (∑ a : Fin r, q a (k j) * w a) = 0) → w = 0)
    (hKQ : ∀ v : V, (∀ u, omega v u = 0) →
       (∀ a : Fin r, q a v = 0) → v = 0)
    (p : V × (Fin r → ℝ))
    (h : ∀ t : V × (Fin r → ℝ), completedPair omega q p t = 0) :
    p = 0 := by
  have hq (a : Fin r) : q a p.1 = 0 := by
    have ha := h (0, fun i => if i = a then (1 : ℝ) else 0)
    simp [completedPair] at ha
    exact ha
  have hωk (j : Fin r) : omega p.1 (k j) = 0 := by
    rw [hskew p.1 (k j), hk j p.1]
    ring
  have hwTest (j : Fin r) :
      (∑ a : Fin r, q a (k j) * p.2 a) = 0 := by
    have hj := h (k j, 0)
    simp only [completedPair] at hj
    simp at hj
    simp only [Finset.sum_neg_distrib] at hj
    rw [hωk j] at hj
    linarith
  have hw : p.2 = 0 := hB p.2 hwTest
  have hω (u : V) : omega p.1 u = 0 := by
    have hu := h (u, 0)
    simpa [completedPair, hw] using hu
  have hv : p.1 = 0 := hKQ p.1 hω hq
  apply Prod.ext
  · exact hv
  · exact hw

/-- Pairing matrix in the (kernel basis, charge) convention. -/
noncomputable def kernelChargeMatrix
    (q : Fin r → V →ₗ[ℝ] ℝ) (k : Fin r → V) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun j a => q a (k j)

/-- Matrix determinant nonzero proves that no nonzero extended conjugate
vector can remain in the null space. -/
theorem kernelChargeMatrix_injective
    (q : Fin r → V →ₗ[ℝ] ℝ) (k : Fin r → V)
    (hdet : (kernelChargeMatrix q k).det ≠ 0)
    (w : Fin r → ℝ)
    (hw : ∀ j, (∑ a : Fin r, q a (k j) * w a) = 0) :
    w = 0 := by
  let B := kernelChargeMatrix q k
  have hb : B.mulVec w = 0 := by
    funext j
    simpa [B, kernelChargeMatrix, Matrix.mulVec, dotProduct] using hw j
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet hb

/-- The kernel spanning hypothesis and det B ≠ 0 imply that the only
kernel vector killed by all charge differentials is zero. -/
theorem kernel_charge_separation
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (q : Fin r → V →ₗ[ℝ] ℝ)
    (k : Fin r → V)
    (hspan : ∀ v, (∀ u, omega v u = 0) →
      ∃ c : Fin r → ℝ, v = ∑ j : Fin r, c j • k j)
    (hdet : (kernelChargeMatrix q k).det ≠ 0)
    (v : V) (hv : ∀ u, omega v u = 0)
    (hq : ∀ a, q a v = 0) :
    v = 0 := by
  obtain ⟨c, hc⟩ := hspan v hv
  let B := kernelChargeMatrix q k
  have hdetT : B.transpose.det ≠ 0 := by
    simpa [B] using hdet
  have hcTest : B.transpose.mulVec c = 0 := by
    funext a
    have ha := hq a
    rw [hc] at ha
    simp only [map_sum, map_smul, smul_eq_mul] at ha
    simpa [B, kernelChargeMatrix, Matrix.mulVec, dotProduct, mul_comm]
      using ha
  have hc0 : c = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdetT hcTest
  rw [hc, hc0]
  simp

/-- THE MAIN FROZEN THEOREM.
A constant-rank presymplectic kernel spanned by r vectors can be
nondegenerately completed by r conjugate directions exactly when
the chosen r charge differentials pair invertibly with this kernel. -/
theorem symplectic_completion_of_det_ne_zero
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (q : Fin r → V →ₗ[ℝ] ℝ)
    (k : Fin r → V)
    (hskew : ∀ v u, omega v u = -omega u v)
    (hk : ∀ j u, omega (k j) u = 0)
    (hspan : ∀ v, (∀ u, omega v u = 0) →
      ∃ c : Fin r → ℝ, v = ∑ j : Fin r, c j • k j)
    (hdet : (kernelChargeMatrix q k).det ≠ 0)
    (p : V × (Fin r → ℝ))
    (hp : ∀ t : V × (Fin r → ℝ), completedPair omega q p t = 0) :
    p = 0 := by
  apply completedPair_nondegenerate_of_kernel_test omega q k hskew hk
    (kernelChargeMatrix_injective q k hdet)
    (kernel_charge_separation omega q k hspan hdet)
    p hp

/-!
# Explicit two-charge (M,J) model and candidate conjugates (T,Phi).
Mathematical test only.  This does not identify T,Phi as actual
physical boundary variables in any chosen BTZ action.
-/

/-- Coordinates are ordered M,J,T,Phi. -/
def btzCandidatePair (x y : Fin 4 → ℝ) : ℝ :=
  x 0 * y 2 - y 0 * x 2 +
  x 1 * y 3 - y 1 * x 3

theorem btzCandidatePair_skew (x y : Fin 4 → ℝ) :
    btzCandidatePair x y = -btzCandidatePair y x := by
  unfold btzCandidatePair
  ring

theorem btzCandidatePair_nondegenerate (x : Fin 4 → ℝ)
    (h : ∀ y, btzCandidatePair x y = 0) :
    x = 0 := by
  have hM : x 0 = 0 := by
    have hx := h (fun i => if i = 2 then (1 : ℝ) else 0)
    simp [btzCandidatePair] at hx
    exact hx
  have hJ : x 1 = 0 := by
    have hx := h (fun i => if i = 3 then (1 : ℝ) else 0)
    simp [btzCandidatePair] at hx
    exact hx
  have hT : x 2 = 0 := by
    have hx := h (fun i => if i = 0 then (1 : ℝ) else 0)
    simp [btzCandidatePair] at hx
    linarith
  have hPhi : x 3 = 0 := by
    have hx := h (fun i => if i = 1 then (1 : ℝ) else 0)
    simp [btzCandidatePair] at hx
    linarith
  funext i
  fin_cases i
  all_goals simp [hM, hJ, hT, hPhi]

/-- Boundary time Hamiltonian H=M generates a T translation, not M,J
evolution.  Sign follows i_X Omega=dH with Omega=dM∧dT+dJ∧dPhi. -/
def btzTimeVector : Fin 4 → ℝ :=
  fun i => if i = 2 then -1 else 0

theorem btzCandidate_time_Hamiltonian (y : Fin 4 → ℝ) :
    btzCandidatePair btzTimeVector y = y 0 := by
  simp [btzCandidatePair, btzTimeVector]

theorem btzCandidate_conserved_charges :
    btzTimeVector 0 = 0 ∧ btzTimeVector 1 = 0 := by
  simp [btzTimeVector]

end PresymplecticCompletion
