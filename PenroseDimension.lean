import Mathlib

/-!
Penrose-diagram dimension comparison.
This file verifies the algebraic decomposition used for the D=5 radial
null-geodesic principal-value integral. It does NOT claim to formalize
the improper integrals or the spacetime causal interpretation.
-/

noncomputable section

theorem ads5_factorization (r : ℝ) :
    (r ^ 2 - 1) * (r ^ 2 + 1) = r ^ 4 - 1 := by
  ring

theorem ads5_null_partial_fraction (r : ℝ)
    (h1 : r ^ 4 - 1 ≠ 0)
    (h2 : r ^ 2 - 1 ≠ 0)
    (h3 : r ^ 2 + 1 ≠ 0) :
    r ^ 2 / (r ^ 4 - 1) =
      (1 / 2 : ℝ) *
        (1 / (r ^ 2 - 1) + 1 / (r ^ 2 + 1)) := by
  field_simp
  ring
