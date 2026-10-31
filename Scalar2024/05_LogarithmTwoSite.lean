import Mathlib

/-!
# Precise nonanalytic high-temperature term and low-temperature 2-site limit.

This file does NOT assume that the original scalar normalizer has
the stated logarithmic expansion. That expansion is independently
derived from the original integral, as described in the report.

It verifies:
  1. M^2*log(M) is not an ordinary O(M^2) Taylor correction at M->0+.
  2. Once the original spectral p0,p1 limits and normalization are
     known, all higher-site probability vanishes at t=tau/m.
-/

open Filter Set Real

namespace Scalar2024

/-- The ratio (M² log M)/M² tends to -infinity at M->0+.
Consequently a nonzero M² log M term cannot be absorbed into O(M²). -/
theorem small_mass_log_is_not_quadratic :
    Filter.Tendsto
      (fun M : ℝ => M ^ 2 * Real.log M / M ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atBot := by
  have h_eq :
      (fun M : ℝ => M ^ 2 * Real.log M / M ^ 2) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun M : ℝ => Real.log M) := by
    filter_upwards [self_mem_nhdsWithin] with M hM
    have hzero : M ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hM)
    field_simp [hzero]
  exact Real.tendsto_log_nhdsGT_zero.congr' h_eq.symm

/-- An abstract two-site normalization identity. Applying it to the
original scalar field additionally requires the spectral limit
P0->cos²(tau), P1->sin²(tau), which is not asserted as a Lean input here. -/
theorem two_site_tail_vanishes
    (tau : ℝ) (p0 p1 tail : ℕ → ℝ)
    (hnorm : ∀ M : ℕ, p0 M + p1 M + tail M = 1)
    (h0 : Filter.Tendsto p0 atTop (nhds ((Real.cos tau) ^ 2)))
    (h1 : Filter.Tendsto p1 atTop (nhds ((Real.sin tau) ^ 2))) :
    Filter.Tendsto tail atTop (nhds 0) := by
  have hconst :
      Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hh := (hconst.sub h0).sub h1
  have hfun : tail = (fun M : ℕ => 1 - p0 M - p1 M) := by
    funext M
    linarith [hnorm M]
  have htrig : 1 - (Real.cos tau) ^ 2 - (Real.sin tau) ^ 2 = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq tau]
  rw [hfun]
  simpa only [htrig] using hh

end Scalar2024
