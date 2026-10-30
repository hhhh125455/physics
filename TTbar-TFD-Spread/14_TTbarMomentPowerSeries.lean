import Mathlib

/-!
# All-index formal cumulant recurrence for the TTbar high-temperature saddle

The analytic model log-mgf K(s) obeys d*K = s*(F+K)+mu*K^2.
Here the *formal power series* identity is a hypothesis. We prove the
coefficient recurrence for EVERY index without truncating to low order.

This step is separate from proving that the analytic sqrt/exponential
gives the same formal series; the real-variable algebraic identity is
proved in 13_TTbarDeformedMoments.lean, while analytic-to-formal Taylor
transfer is still a separate proof obligation.
-/

namespace TTbarMomentPowerSeries

open PowerSeries

/-- Coefficient of the exact quadratic formal-series identity, all n. -/
theorem coefficient_identity_all
    (μ d F : ℚ) (K : PowerSeries ℚ)
    (h : PowerSeries.C d * K =
      PowerSeries.X * (PowerSeries.C F + K) +
        PowerSeries.C μ * (K*K))
    (n : ℕ) :
    d * (PowerSeries.coeff (n+1)) K =
      ((if n = 0 then F else 0) + (PowerSeries.coeff n) K) +
        μ * (∑ p ∈ Finset.antidiagonal (n+1),
          (PowerSeries.coeff p.1) K * (PowerSeries.coeff p.2) K) := by
  have hc := congrArg
    (fun P : PowerSeries ℚ => (PowerSeries.coeff (n+1)) P) h
  simpa only [map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
    PowerSeries.coeff_C] using hc

end TTbarMomentPowerSeries
