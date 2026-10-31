import Mathlib

/-!
# TTbar model: exact scaled Hagedorn log-MGF and double-scaling limit

The exact finite-coupling high-temperature *saddle-model* cumulant
function is K(s) = (-s+d-sqrt((beta-s)^2-k^2))/(2 mu),
with d^2 = beta^2-k^2.

Define t=d^2/(2 beta), eta=d/beta, xi=d/(4 mu).
Then K(t*z)=2*xi*(1-sqrt(1-z+eta^2*z^2/4))-xi*eta*z.

The finite-eta identity and the eta->0 limit are Lean proofs.
This does not claim uniform Taylor coefficient convergence: that is a
separate analytic statement necessary for all-order moment limits.
-/

namespace TTbarCriticalMGF

noncomputable def energyScale (β d : ℝ) : ℝ :=
  d^2/(2*β)

noncomputable def eta (β d : ℝ) : ℝ :=
  d/β

noncomputable def xi (μ d : ℝ) : ℝ :=
  d/(4*μ)

noncomputable def Q (β d z : ℝ) : ℝ :=
  1-z + (eta β d)^2*z^2/4

noncomputable def scaledLog (ξ η z : ℝ) : ℝ :=
  2*ξ*(1-Real.sqrt (1-z+η^2*z^2/4))-ξ*η*z

/-- The radicand identity is exact, for all real z and nonzero beta. -/
theorem radicand_identity (β k d z : ℝ)
    (hβ : β ≠ 0) (hdisk : d^2 = β^2-k^2) :
    (β-energyScale β d*z)^2-k^2 = d^2*Q β d z := by
  calc
    (β-energyScale β d*z)^2-k^2 =
      (β^2-k^2)-2*β*(energyScale β d*z)+
        (energyScale β d*z)^2 := by ring
    _ = d^2*Q β d z := by
      rw [← hdisk]
      unfold energyScale Q eta
      field_simp [hβ] <;> ring

/-- Square root stays on the real positive branch for d>=0. -/
theorem radicand_sqrt (β k d z : ℝ)
    (hβ : β ≠ 0) (hd : 0 ≤ d)
    (hdisk : d^2 = β^2-k^2) :
    Real.sqrt ((β-energyScale β d*z)^2-k^2) =
      d*Real.sqrt (Q β d z) := by
  rw [radicand_identity β k d z hβ hdisk]
  rw [Real.sqrt_mul (sq_nonneg d)]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hd]

/-- Fully nonperturbative scaled logarithmic moment generating function. -/
theorem exact_scaled_generator (μ β k d z : ℝ)
    (hμ : μ ≠ 0) (hβ : β ≠ 0) (hd : 0 ≤ d)
    (hdisk : d^2 = β^2-k^2) :
    (-energyScale β d*z+d-
      Real.sqrt ((β-energyScale β d*z)^2-k^2))/(2*μ) =
      scaledLog (xi μ d) (eta β d) z := by
  rw [radicand_sqrt β k d z hβ hd hdisk]
  unfold scaledLog xi eta energyScale Q
  field_simp [hμ, hβ] <;> ring

/-- All-z real-variable continuity at the double scaling eta=0.
    No differentiation under a limit is assumed or proved here. -/
theorem scaled_log_double_limit (ξ z : ℝ) :
    Filter.Tendsto (fun η : ℝ => scaledLog ξ η z)
      (nhds 0) (nhds (2*ξ*(1-Real.sqrt (1-z)))) := by
  have hc : Continuous (fun η : ℝ => scaledLog ξ η z) := by
    unfold scaledLog
    fun_prop
  have hz : scaledLog ξ 0 z = 2*ξ*(1-Real.sqrt (1-z)) := by
    simp [scaledLog]
  rw [← hz]
  exact hc.continuousAt.tendsto

end TTbarCriticalMGF
