import Mathlib

/-!
TTbar TFD audit: derivation of cylinder Casimir energy from the
conformal transformation of the stress tensor, and convergence of
the infinite thermal trace.

Physical input kept explicit: the CFT stress tensor has the Schwarzian
anomaly c/12; cylinder Hamiltonian is the integrated stress tensor.
-/

namespace TTbarTFD

noncomputable def cylinderMap (κ w : ℂ) : ℂ := Complex.exp (κ * w)

theorem cylinderMap_first (κ w : ℂ) :
    HasDerivAt (cylinderMap κ) (κ * cylinderMap κ w) w := by
  have hlin : HasDerivAt (fun z : ℂ => κ * z) κ w := by
    simpa using (hasDerivAt_id w).const_mul κ
  change HasDerivAt (fun z : ℂ => Complex.exp (κ * z))
    (κ * Complex.exp (κ * w)) w
  convert hlin.cexp using 1 <;> first | rfl | ring

theorem cylinderMap_second (κ w : ℂ) :
    HasDerivAt (fun z : ℂ => κ * cylinderMap κ z)
      (κ ^ 2 * cylinderMap κ w) w := by
  simpa only [pow_two, mul_assoc] using
    (cylinderMap_first κ w).const_mul κ

theorem cylinderMap_third (κ w : ℂ) :
    HasDerivAt (fun z : ℂ => κ ^ 2 * cylinderMap κ z)
      (κ ^ 3 * cylinderMap κ w) w := by
  convert (cylinderMap_first κ w).const_mul (κ ^ 2) using 1 <;> first | rfl | ring

noncomputable def schwarzianJets (d₁ d₂ d₃ : ℂ) : ℂ :=
  d₃ / d₁ - (3 / 2 : ℂ) * (d₂ / d₁) ^ 2

theorem schwarzian_exponential (κ w : ℂ) (hκ : κ ≠ 0) :
    schwarzianJets (κ * cylinderMap κ w)
      (κ ^ 2 * cylinderMap κ w) (κ ^ 3 * cylinderMap κ w)
      = -(κ ^ 2) / 2 := by
  have he : cylinderMap κ w ≠ 0 := Complex.exp_ne_zero _
  unfold schwarzianJets
  field_simp
  ring

/- Conformal Ward identity (physical input):
   T_cylinder = (dz/dw)^2 T_plane + (c/12) {z,w}.
   We prove its vacuum consequence, assuming <T_plane>=0. -/
noncomputable def stressTransform (c planeT d₁ d₂ d₃ : ℂ) : ℂ :=
  d₁ ^ 2 * planeT + (c / 12) * schwarzianJets d₁ d₂ d₃

theorem cylinder_vacuum_stress (c κ w : ℂ) (hκ : κ ≠ 0) :
    stressTransform c 0 (κ * cylinderMap κ w)
      (κ ^ 2 * cylinderMap κ w) (κ ^ 3 * cylinderMap κ w)
      = -(c * κ ^ 2) / 24 := by
  simp [stressTransform, schwarzian_exponential κ w hκ]
  ring

/- Energy is the angular integral of the cylinder stress tensor.
   κ=2π/L, cL and cR are independent central charges. -/
noncomputable def cylinderSpectrum (L h hbar cL cR : ℝ) : ℝ :=
  (2 * Real.pi / L) * (h + hbar - (cL + cR) / 24)

theorem cylinder_spectrum_split (L h hbar cL cR : ℝ) :
    cylinderSpectrum L h hbar cL cR =
      (2 * Real.pi / L) * ((h - cL / 24) + (hbar - cR / 24)) := by
  unfold cylinderSpectrum
  ring

theorem cylinder_vacuum_energy (L cL cR : ℝ) :
    cylinderSpectrum L 0 0 cL cR =
       -(Real.pi * (cL + cR)) / (12 * L) := by
  unfold cylinderSpectrum
  ring

/- Infinite traces: a general domination result. The reference trace
   is assumed summable at one positive inverse temperature. -/
theorem summable_partition_at_lower_temperature
    (Δ : ℕ → ℝ) (β₀ β : ℝ)
    (hΔ : ∀ n, 0 ≤ Δ n) (hβ : β₀ ≤ β)
    (h0 : Summable (fun n => Real.exp (-β₀ * Δ n))) :
    Summable (fun n => Real.exp (-β * Δ n)) := by
  apply h0.of_nonneg_of_le
  · intro n
    exact (Real.exp_pos _).le
  · intro n
    apply Real.exp_monotone
    have h := hΔ n
    nlinarith

/- A nonzero vacuum shift does not change trace convergence. -/
theorem summable_partition_vacuum_shift
    (Δ : ℕ → ℝ) (β E₀ : ℝ)
    (h : Summable (fun n => Real.exp (-β * Δ n))) :
    Summable (fun n => Real.exp (-β * (Δ n + E₀))) := by
  have hid : (fun n : ℕ => Real.exp (-β * (Δ n + E₀))) =
      (fun n : ℕ => Real.exp (-β * E₀) * Real.exp (-β * Δ n)) := by
    funext n
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hid]
  exact h.mul_left (Real.exp (-β * E₀))

/- Weighted level density with an exponential envelope. If level
   energies grow at least gap*n and degeneracies are at most
   C*exp(α*n), convergence holds whenever β*gap > α. -/
theorem summable_density_energy_gap
    (d Δ : ℕ → ℝ) (β gap α C : ℝ)
    (hβ : 0 < β) (hgap : 0 < gap)
    (hα : α < β * gap) (hC : 0 ≤ C)
    (hd0 : ∀ n : ℕ, 0 ≤ d n)
    (hd : ∀ n : ℕ, d n ≤ C * Real.exp (α * (n : ℝ)))
    (hΔ : ∀ n : ℕ, gap * (n : ℝ) ≤ Δ n) :
    Summable (fun n => d n * Real.exp (-β * Δ n)) := by
  have hc : α - β * gap < 0 := by linarith
  have hs : Summable (fun n : ℕ => C * Real.exp ((n : ℝ) * (α - β * gap))) :=
    (Real.summable_exp_nat_mul_iff.mpr hc).mul_left C
  apply hs.of_nonneg_of_le
  · intro n
    exact mul_nonneg (hd0 n) (Real.exp_nonneg _)
  · intro n
    have henergy : -β * Δ n ≤ -β * (gap * (n : ℝ)) :=
      mul_le_mul_of_nonpos_left (hΔ n) (by linarith)
    calc
      d n * Real.exp (-β * Δ n) ≤
          (C * Real.exp (α * (n : ℝ))) * Real.exp (-β * Δ n) :=
        mul_le_mul_of_nonneg_right (hd n) (Real.exp_nonneg _)
      _ ≤ (C * Real.exp (α * (n : ℝ))) *
          Real.exp (-β * (gap * (n : ℝ))) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_monotone henergy)
          (mul_nonneg hC (Real.exp_nonneg _))
      _ = C * Real.exp ((n : ℝ) * (α - β * gap)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring


/- Integrate the two constant cylinder stress-tensor vacuum values.
   This verifies the zero-mode normalization H=(1/2π)∫(T+Tbar)dx. -/
theorem integrated_vacuum_stress (L cL cR : ℝ) (hL : L ≠ 0) :
    (1 / (2 * Real.pi)) *
      (∫ x in (0 : ℝ)..L,
          (-(cL + cR) * (2 * Real.pi / L) ^ 2 / 24)) =
      -(Real.pi * (cL + cR)) / (12 * L) := by
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [hL, Real.pi_ne_zero]
  ring

/- The abstract subexponential degeneracy criterion yields convergence
   at EVERY positive inverse temperature, without a fixed Hagedorn threshold. -/
theorem summable_subexponential_density
    (d Δ : ℕ → ℝ) (gap : ℝ) (hgap : 0 < gap)
    (hd0 : ∀ n : ℕ, 0 ≤ d n)
    (hΔ : ∀ n : ℕ, gap * (n : ℝ) ≤ Δ n)
    (hsub : ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ n : ℕ, d n ≤ C * Real.exp (ε * (n : ℝ)))
    (β : ℝ) (hβ : 0 < β) :
    Summable (fun n => d n * Real.exp (-β * Δ n)) := by
  let ε : ℝ := β * gap / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨C, hC, hbound⟩ := hsub ε hε
  apply summable_density_energy_gap d Δ β gap ε C hβ hgap
    (by dsimp [ε]; nlinarith [mul_pos hβ hgap])
    hC hd0 hbound hΔ

/- Elementary upper bound used to absorb Cardy-type sqrt(n) degeneracy
   into an arbitrarily small positive exponential envelope. -/
theorem sqrt_young_bound (x B ε : ℝ) (hx : 0 ≤ x) (hε : 0 < ε) :
    B * Real.sqrt x ≤ ε * x + B ^ 2 / (4 * ε) := by
  have hroot : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsq := sq_nonneg (2 * ε * Real.sqrt x - B)
  have hden : 4 * ε ≠ 0 := by positivity
  have hdiv : (4 * ε) * (B ^ 2 / (4 * ε)) = B ^ 2 := by
    field_simp
  have hmain : (4 * ε) * (B * Real.sqrt x) ≤
      (4 * ε) * (ε * x + B ^ 2 / (4 * ε)) := by
    nlinarith [hsq, hroot, hdiv]
  exact (mul_le_mul_left (show 0 < (4 : ℝ) * ε by positivity)).mp hmain

theorem cardy_bound_gives_subexponential
    (d : ℕ → ℝ) (C₀ B : ℝ) (hC : 0 ≤ C₀)
    (hCardy : ∀ n : ℕ,
      d n ≤ C₀ * Real.exp (B * Real.sqrt (n : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, d n ≤ C * Real.exp (ε * (n : ℝ)) := by
  refine ⟨C₀ * Real.exp (B ^ 2 / (4 * ε)),
    mul_nonneg hC (Real.exp_nonneg _), ?_⟩
  intro n
  calc
    d n ≤ C₀ * Real.exp (B * Real.sqrt (n : ℝ)) := hCardy n
    _ ≤ C₀ * Real.exp (ε * (n : ℝ) + B ^ 2 / (4 * ε)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_monotone (sqrt_young_bound (n : ℝ) B ε
          (Nat.cast_nonneg n) hε)) hC
    _ = (C₀ * Real.exp (B ^ 2 / (4 * ε))) *
        Real.exp (ε * (n : ℝ)) := by
      rw [Real.exp_add]
      ring

theorem summable_cardy_bounded_partition
    (d Δ : ℕ → ℝ) (gap C₀ B β : ℝ)
    (hgap : 0 < gap) (hβ : 0 < β) (hC : 0 ≤ C₀)
    (hd0 : ∀ n : ℕ, 0 ≤ d n)
    (hΔ : ∀ n : ℕ, gap * (n : ℝ) ≤ Δ n)
    (hCardy : ∀ n : ℕ,
      d n ≤ C₀ * Real.exp (B * Real.sqrt (n : ℝ))) :
    Summable (fun n => d n * Real.exp (-β * Δ n)) := by
  apply summable_subexponential_density d Δ gap hgap hd0 hΔ
    (fun ε hε => cardy_bound_gives_subexponential d C₀ B hC hCardy ε hε)
    β hβ


end TTbarTFD
