import Mathlib

/-!
Covariant classical Krylov reduction + a geometric infinite-spin test.
No new axioms. The Cauchy-data/solution bijection is an explicit input.
This does not assert existence of a Liouville volume form in infinite dimension.
-/

namespace CovariantKrylov

universe u v

section Transport
variable {P : Type u} {S : Type v}

def pull (r : S ≃ P) (f : P → ℝ) : S → ℝ := fun s => f (r s)
def push (r : S ≃ P) (F : S → ℝ) : P → ℝ := fun p => F (r.symm p)

theorem push_pull (r : S ≃ P) (f : P → ℝ) :
    push r (pull r f) = f := by
  funext p
  simp [push, pull]

theorem pull_push (r : S ≃ P) (F : S → ℝ) :
    pull r (push r F) = F := by
  funext s
  simp [push, pull]

/-- Exactly the pullback of the ORIGINAL canonical inner product. -/
def covInner (r : S ≃ P)
    (inner : (P → ℝ) → (P → ℝ) → ℝ)
    (F G : S → ℝ) : ℝ :=
  inner (push r F) (push r G)

theorem inner_recovery (r : S ≃ P)
    (inner : (P → ℝ) → (P → ℝ) → ℝ) (f g : P → ℝ) :
    covInner r inner (pull r f) (pull r g) = inner f g := by
  simp [covInner, push_pull]

/-- Evolution transported from initial data; no new Hamiltonian chosen. -/
def covL (r : S ≃ P) (L : (P → ℝ) → (P → ℝ))
    (F : S → ℝ) : S → ℝ :=
  pull r (L (push r F))

theorem evolution_recovery (r : S ≃ P)
    (L : (P → ℝ) → (P → ℝ)) (f : P → ℝ) :
    covL r L (pull r f) = pull r (L f) := by
  simp [covL, push_pull]

/-- Unnormalized Krylov chain retaining the initial observable and Liouvillian. -/
def chain {X : Type*} (L : (X → ℝ) → (X → ℝ))
    (f : X → ℝ) : ℕ → (X → ℝ)
  | 0 => f
  | n + 1 => L (chain L f n)

theorem chain_recovery (r : S ≃ P)
    (L : (P → ℝ) → (P → ℝ)) (f : P → ℝ) (n : ℕ) :
    chain (covL r L) (pull r f) n = pull r (chain L f n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change covL r L (chain (covL r L) (pull r f) n) =
        pull r (L (chain L f n))
      rw [ih, evolution_recovery]

/-- All Gram entries and therefore the moments are unchanged. -/
theorem gram_recovery (r : S ≃ P)
    (inner : (P → ℝ) → (P → ℝ) → ℝ)
    (L : (P → ℝ) → (P → ℝ)) (f : P → ℝ) (m n : ℕ) :
    covInner r inner
      (chain (covL r L) (pull r f) m)
      (chain (covL r L) (pull r f) n) =
        inner (chain L f m) (chain L f n) := by
  rw [chain_recovery, chain_recovery, inner_recovery]

/-- The full Lanczos residual (with the SAME coefficients). -/
def residual {X : Type*} (L : (X → ℝ) → (X → ℝ))
    (a b : ℝ) (previous current : X → ℝ) : X → ℝ :=
  fun x => L current x - a * current x - b * previous x

theorem residual_recovery (r : S ≃ P)
    (L : (P → ℝ) → (P → ℝ))
    (a b : ℝ) (previous current : P → ℝ) :
    residual (covL r L) a b (pull r previous) (pull r current) =
      pull r (residual L a b previous current) := by
  funext s
  simp [residual, covL, pull, push]

theorem residual_norm_recovery (r : S ≃ P)
    (inner : (P → ℝ) → (P → ℝ) → ℝ)
    (L : (P → ℝ) → (P → ℝ))
    (a b : ℝ) (previous current : P → ℝ) :
    covInner r inner
      (residual (covL r L) a b (pull r previous) (pull r current))
      (residual (covL r L) a b (pull r previous) (pull r current)) =
    inner (residual L a b previous current)
      (residual L a b previous current) := by
  rw [residual_recovery, inner_recovery]

end Transport

section SpinSeries

def geomSum (q : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, q ^ (j + 1)

theorem geomSum_succ (q : ℝ) (N : ℕ) :
    geomSum q (N + 1) = geomSum q N + q ^ (N + 1) := by
  simp [geomSum, Finset.sum_range_succ]

/-- Exact finite cutoff, NOT an uncontrolled infinite-volume limit. -/
theorem geomSum_closed (q : ℝ) (hq : q ≠ 1) (N : ℕ) :
    geomSum q N = (q - q ^ (N + 1)) / (1 - q) := by
  have hd : 1 - q ≠ 0 := by
    intro h
    apply hq
    linarith
  induction N with
  | zero => simp [geomSum]
  | succ N ih =>
      rw [geomSum_succ, ih]
      simp only [pow_succ]
      field_simp
      ring

theorem geomSum_tail (q : ℝ) (hq : q ≠ 1) (N : ℕ) :
    q / (1 - q) - geomSum q N = q ^ (N + 1) / (1 - q) := by
  rw [geomSum_closed q hq N]
  ring

def ratio (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (2 * n + 1)

/-- This is the EXACT single-spin moment derived separately from sphere integrals. -/
def spinMomentCoeff (n : ℕ) : ℝ :=
  3 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3))

def momentNumerator (N n : ℕ) : ℝ :=
  spinMomentCoeff n * geomSum (ratio n) N

def normWeight (N : ℕ) : ℝ := geomSum (1 / 2) N

def finiteMoment (N n : ℕ) : ℝ := momentNumerator N n / normWeight N

/-- Analytic candidate from the product-Liouville model. -/
def limitMoment (n : ℕ) : ℝ :=
  3 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) *
    ((2 : ℝ) ^ (2 * n + 1) - 1))

theorem limitMoment_zero : limitMoment 0 = 1 := by
  norm_num [limitMoment]

theorem limitMoment_two : limitMoment 1 = 1 / 35 := by
  norm_num [limitMoment]

theorem limitMoment_four : limitMoment 2 = 3 / 1085 := by
  norm_num [limitMoment]

theorem first_lanczos_square : limitMoment 1 = 1 / 35 :=
  limitMoment_two

theorem second_lanczos_square :
    limitMoment 2 / limitMoment 1 - limitMoment 1 = 74 / 1085 := by
  rw [limitMoment_two, limitMoment_four]
  norm_num

end SpinSeries
end CovariantKrylov
