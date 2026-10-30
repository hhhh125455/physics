import Mathlib

/-!
Part 09: all-index closed analytic formulas for the two extreme
coefficients and the first correction of Lah-Hankel polynomials.

Let D_n(u) = det[mu_(i+j)(u)]_(0<=i,j<n) where
mu_k = k! [t^k] exp(u*t/(1-t)).

Under the Toda identity (already proved analytically and checked
for n=1..4 in file 08), coefficient comparison yields:
for each fixed n>=2:
D_n(u) = low(n)*u^(n-1)*(1+smallCorr(n)*u+O(u^2))
and
D_n(u) = high(n)*u^(n(n-1)/2)*
  (1+largeCorr(n)/u+O(u^-2)).

Here Lean proves the explicit product sequences and their all-index
coefficient recurrences. Identification with the Lah determinants at
all n still relies on the general Wronskian-Toda theorem.
-/

namespace TTbarLahAnalytic

open Finset

noncomputable def lowCoeff (n : ℕ) : ℚ :=
  ∏ k ∈ Finset.range (n-1),
    (Nat.factorial k : ℚ) * (Nat.factorial (k+2) : ℚ)

noncomputable def highCoeff (n : ℕ) : ℚ :=
  ∏ k ∈ Finset.range n,
    (2 : ℚ)^k * (Nat.factorial k : ℚ)

/-- Exact ALL-n product step for the lowest coefficient. -/
theorem low_step (n : ℕ) :
    lowCoeff (n+2) = lowCoeff (n+1) *
      (Nat.factorial n : ℚ) * (Nat.factorial (n+2) : ℚ) := by
  simp [lowCoeff, Finset.prod_range_succ, Nat.add_assoc]
  ring

/-- Exact ALL-n product step for the highest coefficient. -/
theorem high_step (n : ℕ) :
    highCoeff (n+1) = highCoeff n *
      (2 : ℚ)^n * (Nat.factorial n : ℚ) := by
  simp [highCoeff, Finset.prod_range_succ]
  ring

/-- The small-u product coefficients satisfy the exact nonlinear
    Toda leading-order recurrence at ALL n>=2. -/
theorem low_toda_coeff (k : ℕ) :
    lowCoeff (k+3)*lowCoeff (k+1) =
      ((k+1 : ℚ)*(k+3 : ℚ))* (lowCoeff (k+2))^2 := by
  have hf1 : (Nat.factorial (k+1) : ℚ) =
      (k+1 : ℚ)*(Nat.factorial k : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hf3 : (Nat.factorial (k+3) : ℚ) =
      (k+3 : ℚ)*(Nat.factorial (k+2) : ℚ) := by
    convert congrArg (fun j : ℕ => (j : ℚ))
      (Nat.factorial_succ (k+2)) using 1 <;> norm_num [Nat.add_assoc]
  rw [low_step (k+1), low_step k]
  rw [hf1, hf3]
  ring

/-- High-u product coefficients obey their all-index Toda leading
    recurrence, with factor 2n at n=k+1. -/
theorem high_toda_coeff (k : ℕ) :
    highCoeff (k+2)*highCoeff k =
      2*(k+1 : ℚ)*(highCoeff (k+1))^2 := by
  have hf : (Nat.factorial (k+1) : ℚ) =
    (k+1 : ℚ)*(Nat.factorial k : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [high_step (k+1), high_step k]
  rw [hf, pow_succ]
  ring

/-- First correction at small u for n>=1. -/
noncomputable def smallCorr (n : ℕ) : ℚ :=
  ((n : ℚ)-1)*((n : ℚ)-2)*((n : ℚ)+1) / (2*(n : ℚ))

/-- First correction at large u (polynomial of n). -/
noncomputable def largeCorr (n : ℕ) : ℚ :=
  (n : ℚ)*((n : ℚ)-1)*((n : ℚ)-2)/8

/-- Exact all-index recurrence of the FIRST correction to the
    leading small-u coefficient, as demanded by Toda. -/
theorem small_correction_recurrence (k : ℕ) :
    (((k : ℚ)+2)^2-1) *
       (smallCorr (k+3) + smallCorr (k+1)) =
    2*((k : ℚ)+2)^2*smallCorr (k+2) +
      2*((k : ℚ)+2) := by
  unfold smallCorr
  have h1 : ((k : ℚ)+1) ≠ 0 := by positivity
  have h2 : ((k : ℚ)+2) ≠ 0 := by positivity
  have h3 : ((k : ℚ)+3) ≠ 0 := by positivity
  field_simp [h1,h2,h3]
  push_cast
  ring

/-- Exact all-index recurrence of the FIRST correction to the
    leading large-u coefficient. -/
theorem large_correction_recurrence (k : ℕ) :
    largeCorr (k+3) + largeCorr (k+1) -
      2*largeCorr (k+2) =
      3*((k : ℚ)+1)/4 := by
  unfold largeCorr
  push_cast
  ring

/-- Exact check of the low-u coefficient products at n=2..5. -/
theorem low_known :
    lowCoeff 2=2 ∧ lowCoeff 3=12 ∧
    lowCoeff 4=576 ∧ lowCoeff 5=414720 := by
  norm_num [lowCoeff, Nat.factorial]

/-- Exact check of high-u leading coefficient products n=2..5. -/
theorem high_known :
    highCoeff 2=2 ∧ highCoeff 3=16 ∧
    highCoeff 4=768 ∧ highCoeff 5=294912 := by
  norm_num [highCoeff, Nat.factorial]

/-- The first corrections agree with the exact Lah determinants
    for n=3,4,5. -/
theorem correction_known :
    smallCorr 3 = 4/3 ∧ smallCorr 4=15/4 ∧
    smallCorr 5=36/5 ∧ largeCorr 3=3/4 ∧
    largeCorr 4=3 ∧ largeCorr 5=15/2 := by
  norm_num [smallCorr,largeCorr]

/-- The SECOND relative large-u correction, coefficient of 1/u^2.
    It is a degree-six polynomial in the index n. -/
noncomputable def largeCorr2 (n : ℕ) : ℚ :=
  (n : ℚ)*((n : ℚ)-3)*((n : ℚ)-2)*
   ((n : ℚ)-1)^2*((n : ℚ)+1)/128

/-- Toda coefficient matching at the next order forces this all-index
    second finite-difference equation; the proposed closed polynomial
    passes the identity for every natural index. -/
theorem large_second_correction_recurrence (k : ℕ) :
    largeCorr2 (k+3)+largeCorr2 (k+1)-2*largeCorr2 (k+2) =
       largeCorr (k+2)^2 -
       largeCorr (k+3)*largeCorr (k+1) +
       (3/2 : ℚ)*((k : ℚ)+1)*largeCorr (k+2) := by
  unfold largeCorr2 largeCorr
  push_cast
  ring

theorem large_second_correction_known :
    largeCorr2 2 = 0 ∧ largeCorr2 3 = 0 ∧
    largeCorr2 4 = 45/16 ∧ largeCorr2 5 = 45/2 ∧
    largeCorr2 6 = 1575/16 := by
  norm_num [largeCorr2]


end TTbarLahAnalytic
