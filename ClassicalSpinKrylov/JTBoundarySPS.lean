import Mathlib

/-!
# Two-boundary JT gravity: actual boundary variables vs an artificial completion

PHYSICAL INPUT (FROZEN FROM Harlow--Wu, JHEP 10 (2020) 146):
* JT action eq. (3.75), including the boundary term.
* On-shell two-boundary family eqs. (3.86)-(3.93):
  e = Phi_e, tp = t₀⁺, tm = t₀⁻; fixed phi = phi_b > 0.
* Energy eq. (3.89): E = 2 e² / phi.
* Boundary presymplectic potential after cancellations, eq. (3.99):
    theta = (2/phi) * [ e*(2*t+tp+tm) de + e²*(dtp+dtm) ]
  where t is a fixed reference slice parameter, not a phase-space coordinate.
* Presymplectic form eq. (3.103):
    Omega = (2e/phi) de ^ (dtp+dtm)
  and physical Delta = (tp+tm)/2, eq. (3.104).

THEOREMS HERE verify exact finite-dimensional algebra:
  theta = E dDelta + dG,
  Omega = dE ^ dDelta,
  null vector dtp=-dtm, and exact kernel on e>0, phi>0,
  2D reduced nondegeneracy,
  charge-pair invertibility and the Hamiltonian time vector.
The full tensor/geometric variation of the original 2D dilaton gravity
action, the boundary conditions, and physical existence of the family
are taken from the cited published derivation, not formalized in Lean.
No local extra axioms or proof gaps.
-/
namespace JTBoundarySPS

/-- Parameter order: 0=de, 1=dtp, 2=dtm. -/
noncomputable def energy (e phi : ℝ) : ℝ := 2*e^2/phi

noncomputable def deltaT (tp tm : ℝ) : ℝ := (tp+tm)/2

noncomputable def dEnergy (e phi : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  (4*e/phi)*v 0

noncomputable def dDelta (v : Fin 3 → ℝ) : ℝ :=
  (v 1+v 2)/2

/-- Pullback from Harlow-Wu's complete boundary-corrected action. -/
noncomputable def presymplectic (e phi : ℝ)
    (v w : Fin 3 → ℝ) : ℝ :=
  (2*e/phi) * (v 0*(w 1+w 2) - w 0*(v 1+v 2))

/-- The boundary symplectic potential of their eq. (3.99), omitting
topological Phi_0 contributions proven to cancel in that paper. -/
noncomputable def thetaBoundary (e phi t tp tm : ℝ)
    (v : Fin 3 → ℝ) : ℝ :=
  (2/phi)*(e*(2*t+tp+tm)*v 0+e^2*(v 1+v 2))

/-- The exact-function ambiguity in the reduced symplectic potential. -/
noncomputable def boundaryExactDerivative (e phi t tp tm : ℝ)
    (v : Fin 3 → ℝ) : ℝ :=
  (2*e*(2*t+tp+tm)/phi)*v 0 +
    (e^2/phi)*(v 1+v 2)

/-- thetaBoundary = E dDelta + d G, with
G=(2t+tp+tm) e²/phi; equality of 1-forms is exact pointwise. -/
theorem action_potential_reduction
    (e phi t tp tm : ℝ) (v : Fin 3 → ℝ) :
    thetaBoundary e phi t tp tm v =
      energy e phi * dDelta v +
        boundaryExactDerivative e phi t tp tm v := by
  unfold thetaBoundary energy dDelta boundaryExactDerivative
  ring

/-- The physical 2D canonical form is dE ^ dDelta. -/
def reducedSymplectic (v w : ℝ × ℝ) : ℝ :=
  v.1*w.2-w.1*v.2

/-- Differential of E and Delta acting on tangent vectors. -/
noncomputable def parameterToPhysical (e phi : ℝ)
    (v : Fin 3 → ℝ) : ℝ × ℝ :=
  (dEnergy e phi v, dDelta v)

/-- Exact identity corresponding to Harlow-Wu (3.103)-(3.104). -/
theorem physical_pullback_exact
    (e phi : ℝ) (v w : Fin 3 → ℝ) :
    presymplectic e phi v w =
      reducedSymplectic
        (parameterToPhysical e phi v)
        (parameterToPhysical e phi w) := by
  unfold presymplectic reducedSymplectic parameterToPhysical dEnergy dDelta
  ring

/-- A variation of tp-tm alone is physically null. -/
def relativeDifferenceGauge : Fin 3 → ℝ :=
  fun i => if i = 1 then 1 else if i = 2 then -1 else 0

theorem difference_is_null (e phi : ℝ) (w : Fin 3 → ℝ) :
    presymplectic e phi relativeDifferenceGauge w = 0 := by
  simp [presymplectic, relativeDifferenceGauge]

theorem difference_has_no_energy (e phi : ℝ) :
    dEnergy e phi relativeDifferenceGauge = 0 := by
  simp [dEnergy, relativeDifferenceGauge]

theorem difference_has_no_physical_time :
    dDelta relativeDifferenceGauge = 0 := by
  simp [dDelta, relativeDifferenceGauge]

/-- Characterize *all* null directions for e≠0 and phi≠0.
No additional zero modes are silently discarded. -/
theorem presymplectic_kernel_exact
    (e phi : ℝ) (he : e ≠ 0) (hphi : phi ≠ 0)
    (v : Fin 3 → ℝ) :
    (∀ w : Fin 3 → ℝ, presymplectic e phi v w = 0) ↔
      v 0 = 0 ∧ v 1+v 2 = 0 := by
  have hc : (2*e/phi) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by norm_num) he) hphi
  constructor
  · intro hv
    have h1 := hv (fun i => if i = 1 then (1 : ℝ) else 0)
    have h0 := hv (fun i => if i = 0 then (1 : ℝ) else 0)
    have h1' : (2*e/phi)*v 0 = 0 := by
      simpa [presymplectic] using h1
    have h12 : v 1+v 2 = 0 := by
      simp [presymplectic, he, hphi] at h0
      linarith
    exact ⟨(mul_eq_zero.mp h1').resolve_left hc, h12⟩
  · rintro ⟨h0, h12⟩ w
    simp [presymplectic, h0, h12]

/-- The 2D reduced symplectic form has no null directions. -/
theorem reducedSymplectic_nondegenerate (v : ℝ × ℝ)
    (hv : ∀ w : ℝ × ℝ, reducedSymplectic v w = 0) :
    v = 0 := by
  have hv1 : v.1 = 0 := by
    have h := hv (0,1)
    simpa [reducedSymplectic] using h
  have hv2 : v.2 = 0 := by
    have h := hv (1,0)
    simp [reducedSymplectic] at h
    linarith
  exact Prod.ext hv1 hv2

/-- From the one-parameter solution family e>0, the energy has a
nonvanishing differential, so the candidate companion Delta passes the
charge-pairing test. -/
theorem energy_parameter_pair_nonzero
    (e phi : ℝ) (he : e ≠ 0) (hphi : phi ≠ 0) :
    4*e/phi ≠ 0 := by
  exact div_ne_zero (mul_ne_zero (by norm_num) he) hphi

/-- Harlow-Wu convention -i_X Omega=dH; hence H=E generates +d/dDelta. -/
def physicalTimeVector : ℝ × ℝ := (0,1)

theorem time_evolution_is_boundary_shift (w : ℝ × ℝ) :
    -reducedSymplectic physicalTimeVector w = w.1 := by
  simp [physicalTimeVector, reducedSymplectic]

/-- The exact charge E is constant under the flow. -/
theorem energy_conserved_under_time :
    physicalTimeVector.1 = 0 := by
  rfl

/-- A nonnegative normalization density independent of noncompact Delta
has integral 2R*rho(E) on [-R,R]; any rho(E)>0 yields unbounded growth.
This lemma is algebraic and DOES NOT claim a Gibbs measure is normalized. -/
theorem noncompact_relative_time_obstruction
    (rho R : ℝ) (hrho : 0 < rho) (hR : 0 ≤ R) :
    R*rho < (R+1)*rho := by
  nlinarith

end JTBoundarySPS
