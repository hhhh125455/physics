import Mathlib

/-!
  AdS5 R-current: elementary algebra associated with the bouncing-pole mode.

  Verified status is determined exclusively by the GitHub Actions run.

  This file proves ONLY the finite algebraic implications of two roots.
  It does NOT establish the spectral identity, Jacobi moment formula,
  absolute convergence of the double series, remainder estimates, or
  the geometric interpretation of the poles.

  No `sorry`, `axiom`, or `admit` are used.
-/


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
    _ = 0 := by rw [hi]; ring

/-!
### Prony reconstruction from four consecutive moments

These are exact finite-dimensional algebra identities.  The variables x,y
represent the two mode amplitudes at index n; r,s are characteristic roots.
Using the results with an asymptotic moment expansion additionally requires
a separate proof that the remainder is sufficiently small.
-/

theorem prony_determinant (x y r s : ℂ) :
    (x + y) * (x * r ^ 2 + y * s ^ 2) -
      (x * r + y * s) ^ 2 = x * y * (r - s) ^ 2 := by
  ring

theorem prony_sum_numerator (x y r s : ℂ) :
    (x + y) * (x * r ^ 3 + y * s ^ 3) -
      (x * r + y * s) * (x * r ^ 2 + y * s ^ 2) =
        (r + s) * (x * y * (r - s) ^ 2) := by
  ring

theorem prony_product_numerator (x y r s : ℂ) :
    (x * r + y * s) * (x * r ^ 3 + y * s ^ 3) -
      (x * r ^ 2 + y * s ^ 2) ^ 2 =
        (r * s) * (x * y * (r - s) ^ 2) := by
  ring

theorem prony_recovers_sum_product (x y r s : ℂ)
    (hD : x * y * (r - s) ^ 2 ≠ 0) :
    ((x + y) * (x * r ^ 3 + y * s ^ 3) -
      (x * r + y * s) * (x * r ^ 2 + y * s ^ 2)) /
      ((x + y) * (x * r ^ 2 + y * s ^ 2) -
        (x * r + y * s) ^ 2) = r + s ∧
    ((x * r + y * s) * (x * r ^ 3 + y * s ^ 3) -
      (x * r ^ 2 + y * s ^ 2) ^ 2) /
      ((x + y) * (x * r ^ 2 + y * s ^ 2) -
        (x * r + y * s) ^ 2) = r * s := by
  constructor
  · rw [prony_sum_numerator, prony_determinant]
    field_simp [hD]
  · rw [prony_product_numerator, prony_determinant]
    field_simp [hD]

theorem bounce_mode_sum (i : ℂ) :
    (((3 : ℂ) + 4 * i) / 25) +
      (((3 : ℂ) - 4 * i) / 25) = (6 : ℂ) / 25 := by
  ring

theorem bounce_mode_product (i : ℂ) (hi : i * i = -1) :
    (((3 : ℂ) + 4 * i) / 25) *
      (((3 : ℂ) - 4 * i) / 25) = (1 : ℂ) / 25 := by
  calc
    (((3 : ℂ) + 4 * i) / 25) *
        (((3 : ℂ) - 4 * i) / 25) =
        ((9 : ℂ) - 16 * (i * i)) / 625 := by ring
    _ = (1 : ℂ) / 25 := by rw [hi]; ring

theorem bounce_mode_reveals_denominator (i : ℂ) (hi : i * i = -1) :
    (((3 : ℂ) + 4 * i) / 25) * (2 - i) ^ 2 = 1 := by
  have hsq : (2 - i) ^ 2 = (3 : ℂ) - 4 * i := by
    calc
      (2 - i) ^ 2 = 4 - 4 * i + i * i := by ring
      _ = 3 - 4 * i := by rw [hi]; ring
  rw [hsq]
  calc
    (((3 : ℂ) + 4 * i) / 25) * (3 - 4 * i) =
      (25 - 16 * (i * i + 1)) / 25 := by ring
    _ = 1 := by rw [hi]; ring


end
end BouncePartial
