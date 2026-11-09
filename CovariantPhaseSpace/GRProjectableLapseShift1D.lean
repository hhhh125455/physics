import Mathlib

/-!
# ADM projectability: exact lapse/shift cancellation in one spatial dimension

This is an explicit local component check of Pons--Salisbury--Shepley (1997),
eqs. (3.8), (3.9), (3.14). Writing spacetime diffeomorphism descriptors as

  epsilon^0 = alpha / N,
  epsilon^x = beta - B * alpha / N,

makes the transformed lapse N and shift B independent of their velocities
Nt and Bt.  The variables in the theorem are independent formal 1-jets;
field-simp and ring verify the rational expression as an exact identity.

The field-dependent descriptor, not a fixed epsilon^mu, is essential.
This is 1+1 algebraic projectability, not all of H3 for 3+1 GR.
-/

namespace CovariantPhaseSpace

section ADMProjectableDescriptors1D

/-- Equation (3.8) of Pons--Salisbury--Shepley after replacing the
spacetime descriptors by normal/tangential deformation parameters. -/
theorem projectable_lapse_variation_1d
    (N B alpha beta Nt Nx alphat alphax : ℝ)
    (hN : N ≠ 0) :
    (alpha / N) * Nt +
        (beta - B * alpha / N) * Nx +
        N * (alphat / N - alpha * Nt / N ^ 2) -
        N * B * (alphax / N - alpha * Nx / N ^ 2) =
      alphat + beta * Nx - B * alphax := by
  field_simp
  ring

/-- Equation (3.9) of Pons--Salisbury--Shepley; the time
derivatives Nt and Bt cancel exactly. The symbol hinv denotes
the inverse spatial metric component h^(xx). -/
theorem projectable_shift_variation_1d
    (N B hinv alpha beta Nt Nx Bt Bx alphat alphax betat betax : ℝ)
    (hN : N ≠ 0) :
    (alpha / N) * Bt +
      (beta - B * alpha / N) * Bx +
      B * (alphat / N - alpha * Nt / N ^ 2) -
      (N ^ 2 * hinv + B ^ 2) *
        (alphax / N - alpha * Nx / N ^ 2) +
      (betat - Bt * alpha / N -
        B * (alphat / N - alpha * Nt / N ^ 2)) -
      B * (betax - Bx * alpha / N -
        B * (alphax / N - alpha * Nx / N ^ 2)) =
      betat + beta * Bx - B * betax +
        hinv * (alpha * Nx - N * alphax) := by
  field_simp
  ring

end ADMProjectableDescriptors1D

end CovariantPhaseSpace
