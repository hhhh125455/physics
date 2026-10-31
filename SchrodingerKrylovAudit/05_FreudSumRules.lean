import Mathlib

/-!
# Exact-slope argument for original fermionic spectrum.

The analytic integration-by-parts and orthogonality steps that establish
the two Freud-type sum rules are written explicitly in the accompanying
audit note. This file formally checks the *all-index inequalities* obtained
from those sum rules, including a uniform O(1) difference from the
reference Laguerre Lanczos coefficient. We do not claim that Lean
has itself proved the integration-by-parts and polynomial-orthogonality
lemmas in this module.
-/

namespace SchrodingerKrylovAudit

/-- Uniform error bound from the off-diagonal Freud-type identity.
    Here delta is the sum of diagonal errors, and R is a
    Cauchy–Schwarz-controlled cross term. -/
theorem jacobi_offdiag_uniform_bound
    (B b M delta R : ℝ)
    (hB : 0 < B) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hdelta0 : 0 ≤ delta) (hdeltaMax : delta ≤ 2 * M * B)
    (hR : |R| ≤ M * b)
    (hidentity : b ^ 2 = B ^ 2 + delta + 2 * R) :
    |b - B| ≤ 2 * M := by
  rcases abs_le.mp hR with ⟨hRlo, hRhi⟩
  have hpos : 0 < b + B := by linarith
  have hupper : b ^ 2 - B ^ 2 ≤ 2 * M * (b + B) := by
    nlinarith
  have hlower : B ^ 2 - b ^ 2 ≤ 2 * M * (b + B) := by
    nlinarith [mul_nonneg hM hB.le]
  have h1 : b - B ≤ 2 * M := by
    apply (mul_le_mul_right hpos).mp
    nlinarith [hupper]
  have h2 : B - b ≤ 2 * M := by
    apply (mul_le_mul_right hpos).mp
    nlinarith [hlower]
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- Translates moment sum-rule bounds S ≤ M*n into delta ≤ 2*M*B. -/
theorem jacobi_offdiag_from_sumrules
    (b B M n c S R : ℝ)
    (hc : 0 < c) (hn : 0 < n) (hB : n / c ≤ B)
    (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hS0 : 0 ≤ S) (hS1 : S ≤ M * n)
    (hR : |R| ≤ M * b)
    (hidentity : b ^ 2 = B ^ 2 + 2 * S / c + 2 * R) :
    |b - B| ≤ 2 * M := by
  have hBpos : 0 < B := by
    have hd : 0 < n / c := div_pos hn hc
    linarith
  have hd0 : 0 ≤ 2 * S / c := div_nonneg (by positivity) hc.le
  have hd1 : 2 * S / c ≤ 2 * M * B := by
    calc
      2 * S / c ≤ 2 * (M * n) / c := by gcongr
      _ = 2 * M * (n / c) := by ring
      _ ≤ 2 * M * B := by gcongr
  exact jacobi_offdiag_uniform_bound B b M (2 * S / c) R
    hBpos hb hM hd0 hd1 hR hidentity

/-- Reference Laguerre coefficient B(n) is >= n/c. -/
theorem laguerre_reference_lower (n : ℕ) (c : ℝ) (hc : 0 < c) :
    (n : ℝ) / c ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) / c := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have harg : 0 ≤ (n : ℝ) * ((n : ℝ) + 1) :=
    mul_nonneg hn (by linarith)
  have hs : (Real.sqrt ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 =
      (n : ℝ) * ((n : ℝ) + 1) := Real.sq_sqrt harg
  have hs0 := Real.sqrt_nonneg ((n : ℝ) * ((n : ℝ) + 1))
  have hr : (n : ℝ) ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) := by
    nlinarith
  exact (div_le_div_iff₀ hc hc).mpr (by nlinarith [hr])

/-- Laguerre reference coefficient is positive for n >= 1. -/
theorem laguerre_reference_positive (n : ℕ) (c : ℝ)
    (hc : 0 < c) (hn : 0 < n) :
    0 < Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) / c := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) * ((n : ℝ) + 1) := mul_pos hn' (by linarith)
  exact div_pos (Real.sqrt_pos.2 hp) hc

/-- Exact uniform bound on the original b_n once the analytic
    integration-by-parts sum rule is supplied. -/
theorem original_offdiag_all_n
    (n : ℕ) (b M c S R : ℝ)
    (hc : 0 < c) (hn : 0 < n)
    (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hS0 : 0 ≤ S) (hS1 : S ≤ M * (n : ℝ))
    (hR : |R| ≤ M * b)
    (hSumRule :
      b ^ 2 =
        (Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) / c) ^ 2
        + 2 * S / c + 2 * R) :
    |b - Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) / c| ≤ 2 * M := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact jacobi_offdiag_from_sumrules
    b (Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) / c)
    M (n : ℝ) c S R
    hc hn' (laguerre_reference_lower n c hc)
    hb hM hS0 hS1 hR hSumRule

/-- All-index diagonal coefficient deviation from pure Laguerre. -/
theorem original_diagonal_all_n (beta mu n a M e : ℝ)
    (hE0 : 0 ≤ e) (hE1 : e ≤ M)
    (hidentity : a = mu - 4 * (n + 1) / beta - 2 * e) :
    mu - 4 * (n + 1) / beta - 2 * M ≤ a ∧
    a ≤ mu - 4 * (n + 1) / beta := by
  constructor <;> linarith

/-- The spectral shift changes the diagonal coefficient but not b_n. -/
theorem shifted_jacobi_coefficients
    (mu diagX diagOmega offX offOmega : ℝ)
    (ha : diagOmega = mu - diagX)
    (hb : offOmega = offX) :
    (diagOmega + diagX = mu) ∧ (offOmega = offX) := by
  constructor
  · linarith
  · exact hb

end SchrodingerKrylovAudit
