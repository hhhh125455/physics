/-!
  AdS5 R-current: elementary algebra associated with the bouncing-pole mode.

  Verified status is determined exclusively by the GitHub Actions run.

  This file proves ONLY the finite algebraic implications of two roots.
  It does NOT establish the spectral identity, Jacobi moment formula,
  absolute convergence of the double series, remainder estimates, or
  the geometric interpretation of the poles.

  No `sorry`, `axiom`, or `admit` are used.
-/

import Mathlib

namespace BouncePartial

noncomputable section

/- The quadratic polynomial is u^2 - (6/25) u + 1/25. -/
private def c : ℂ := (6 : ℂ) / 25
private def d : ℂ := (1 : ℂ) / 25

/- These proofs use an explicit hypothesis i*i = -1.  In an eventual
   full proof one specializes i to Complex.I using its standard lemma. -/
theorem plus_root (i : ℂ) (hi : i * i = -1) :
    (((3 : ℂ) + 4 * i) / 25) ^ 2 -
      c * (((3 : ℂ) + 4 * i) / 25) + d = 0 := by
  unfold c d
  calc
    (((3 : ℂ) + 4 * i) / 25) ^ 2 -
        ((6 : ℂ) / 25) * (((3 : ℂ) + 4 * i) / 25) + (1 : ℂ) / 25 =
        ((16 : ℂ) / 625) * (i * i + 1) := by ring
    _ = 0 := by rw [hi]; ring

theorem minus_root (i : ℂ) (hi : i * i = -1) :
    (((3 : ℂ) - 4 * i) / 25) ^ 2 -
      c * (((3 : ℂ) - 4 * i) / 25) + d = 0 := by
  unfold c d
  calc
    (((3 : ℂ) - 4 * i) / 25) ^ 2 -
        ((6 : ℂ) / 25) * (((3 : ℂ) - 4 * i) / 25) + (1 : ℂ) / 25 =
        ((16 : ℂ) / 625) * (i * i + 1) := by ring
    _ = 0 := by rw [hi]; ring

/- Every individual geometric mode satisfies a 2-step recurrence
   provided its base is a root of the characteristic polynomial. -/
theorem geometric_mode_recurrence
    (r A c0 d0 : ℂ)
    (hroot : r ^ 2 - c0 * r + d0 = 0) (n : ℕ) :
    A * r ^ (n + 2) - c0 * (A * r ^ (n + 1)) +
      d0 * (A * r ^ n) = 0 := by
  calc
    A * r ^ (n + 2) - c0 * (A * r ^ (n + 1)) +
        d0 * (A * r ^ n) =
        A * r ^ n * (r ^ 2 - c0 * r + d0) := by
          simp only [pow_add, pow_one, pow_two]
          ring
    _ = 0 := by rw [hroot]; ring

/- A sum of the two conjugate-looking geometric modes satisfies the
   same recurrence. No complex-conjugation properties are assumed here. -/
theorem sum_mode_recurrence
    (r s A B c0 d0 : ℂ)
    (hr : r ^ 2 - c0 * r + d0 = 0)
    (hs : s ^ 2 - c0 * s + d0 = 0) (n : ℕ) :
    (A * r ^ (n + 2) + B * s ^ (n + 2)) -
      c0 * (A * r ^ (n + 1) + B * s ^ (n + 1)) +
      d0 * (A * r ^ n + B * s ^ n) = 0 := by
  have h1 := geometric_mode_recurrence r A c0 d0 hr n
  have h2 := geometric_mode_recurrence s B c0 d0 hs n
  calc
    (A * r ^ (n + 2) + B * s ^ (n + 2)) -
        c0 * (A * r ^ (n + 1) + B * s ^ (n + 1)) +
        d0 * (A * r ^ n + B * s ^ n) =
        (A * r ^ (n + 2) - c0 * (A * r ^ (n + 1)) +
          d0 * (A * r ^ n)) +
        (B * s ^ (n + 2) - c0 * (B * s ^ (n + 1)) +
          d0 * (B * s ^ n)) := by ring
    _ = 0 := by rw [h1, h2]; ring

/- The pole-coordinate relation uses only multiplication by i and
   cancellation of a nonzero complex pi. -/
theorem pole_equation
    (A i p : ℂ) (hi : i * i = -1) (hp : p ≠ 0) :
    A + i * (i * p * A) / p = 0 := by
  calc
    A + i * (i * p * A) / p = A * (1 + i * i) := by
      field_simp [hp]
      ring
    _ = 0 := by rw [hi]; ring

end
end BouncePartial
