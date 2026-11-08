import Mathlib

/-!
# D3A: the full finite-order integration-by-parts identity

This module formalizes the algebraic identity behind the endpoint momenta.
The operator D is an additive derivation on a commutative ring:
additivity is packaged as an additive homomorphism, and the Leibniz rule
is an explicit hypothesis.

This is an algebraic formalization. It does not identify D with a spacetime
derivative on a function space, justify spatial integrations by parts,
or prove the variational-bicomplex statement for a general field theory.
-/

namespace CovariantPhaseSpaceAudit

section D3A

variable {R : Type*} [CommRing R]

/-- The n-th iterate of an additive differential operator. -/
def iterD (D : R →+ R) : ℕ → R → R
  | 0, x => x
  | n + 1, x => D (iterD D n x)

/-- The n-th iterate of the negative differential operator -D. -/
def negIterD (D : R →+ R) : ℕ → R → R
  | 0, x => x
  | n + 1, x => -D (negIterD D n x)

/-- The boundary expression in the m-th integration-by-parts identity. -/
def ibpBoundary (D : R →+ R) (F q : R) (m : ℕ) : R :=
  ∑ j ∈ Finset.range m,
    negIterD D (m - 1 - j) F * iterD D j q

lemma iterD_succ_right (D : R →+ R) (n : ℕ) (x : R) :
    iterD D (n + 1) x = iterD D n (D x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change D (iterD D (n + 1) x) = D (iterD D n (D x))
      rw [ih]

/-- Shifting the boundary sum by one derivative on q. -/
lemma ibpBoundary_succ (D : R →+ R) (F q : R) (n : ℕ) :
    ibpBoundary D F q (n + 1) =
      negIterD D n F * q + ibpBoundary D F (D q) n := by
  unfold ibpBoundary
  rw [Finset.sum_range_succ']
  have hhead :
      negIterD D (n + 1 - 1 - 0) F * iterD D 0 q =
        negIterD D n F * q := by
    simp [iterD]
  rw [hhead]
  calc
    (∑ j ∈ Finset.range n,
      negIterD D (n + 1 - 1 - (j + 1)) F * iterD D (j + 1) q) +
        negIterD D n F * q =
      negIterD D n F * q +
        (∑ j ∈ Finset.range n,
          negIterD D (n + 1 - 1 - (j + 1)) F * iterD D (j + 1) q) := by
            ac_rfl
    _ = negIterD D n F * q +
        (∑ j ∈ Finset.range n,
          negIterD D (n - 1 - j) F * iterD D j (D q)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            have hjlt : j < n := Finset.mem_range.mp hj
            have hidx : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
            rw [hidx, iterD_succ_right]

/-- The m-th repeated integration-by-parts identity:
F D^m(q) = (-D)^m(F) q + D(B_m(F,q)). -/
theorem iterated_integration_by_parts
    (D : R →+ R)
    (hLeibniz : ∀ x y : R, D (x * y) = D x * y + x * D y)
    (F q : R) :
    ∀ m : ℕ,
      F * iterD D m q =
        negIterD D m F * q + D (ibpBoundary D F q m) := by
  intro m
  induction m generalizing q with
  | zero =>
      simp [iterD, negIterD, ibpBoundary]
  | succ m ih =>
      rw [iterD_succ_right]
      rw [ibpBoundary_succ]
      calc
        F * iterD D m (D q) =
            negIterD D m F * D q + D (ibpBoundary D F (D q) m) :=
          ih (D q)
        _ = negIterD D (m + 1) F * q +
            D (negIterD D m F * q +
              ibpBoundary D F (D q) m) := by
          rw [negIterD]
          rw [D.map_add]
          rw [hLeibniz]
          ring

/-- The Euler-Lagrange expression obtained by summing the signed
derivatives of the partial-derivative coefficients. -/
def eulerExpression (D : R →+ R) (F : ℕ → R) (k : ℕ) : R :=
  ∑ m ∈ Finset.range (k + 1), negIterD D m (F m)

/-- The complete endpoint term, summed over all derivative orders. -/
def totalBoundary (D : R →+ R) (F : ℕ → R) (q : R) (k : ℕ) : R :=
  ∑ m ∈ Finset.range (k + 1), ibpBoundary D (F m) q m

/-- The full finite-order first-variation identity:
sum_m F_m D^m(q) = E q + D(total endpoint term). -/
theorem finite_order_variation_identity
    (D : R →+ R)
    (hLeibniz : ∀ x y : R, D (x * y) = D x * y + x * D y)
    (F : ℕ → R) (q : R) (k : ℕ) :
    (∑ m ∈ Finset.range (k + 1), F m * iterD D m q) =
      eulerExpression D F k * q + D (totalBoundary D F q k) := by
  unfold eulerExpression totalBoundary
  calc
    (∑ m ∈ Finset.range (k + 1), F m * iterD D m q) =
        ∑ m ∈ Finset.range (k + 1),
          (negIterD D m (F m) * q +
            D (ibpBoundary D (F m) q m)) := by
          apply Finset.sum_congr rfl
          intro m hm
          exact iterated_integration_by_parts D hLeibniz (F m) q m
    _ =
        (∑ m ∈ Finset.range (k + 1), negIterD D m (F m) * q) +
        (∑ m ∈ Finset.range (k + 1), D (ibpBoundary D (F m) q m)) := by
          rw [Finset.sum_add_distrib]
    _ =
        (∑ m ∈ Finset.range (k + 1), negIterD D m (F m)) * q +
        D (∑ m ∈ Finset.range (k + 1), ibpBoundary D (F m) q m) := by
          rw [← Finset.sum_mul, ← map_sum]


/-- The endpoint momentum coefficient, written with the derivative order m
as the summation index:
p_j = sum_{m=j+1}^k (-D)^(m-j-1) F_m. -/
def endpointMomentum (D : R →+ R) (F : ℕ → R) (k j : ℕ) : R :=
  ∑ m ∈ Finset.range (k + 1),
    if j < m then negIterD D (m - 1 - j) (F m) else 0

/-- Extending a sum over range m to range n with an indicator. -/
lemma sum_range_extend_if_lt
    {A : Type*} [AddCommMonoid A]
    (m n : ℕ) (hmn : m ≤ n) (f : ℕ → A) :
    (∑ j ∈ Finset.range m, f j) =
      ∑ j ∈ Finset.range n, if j < m then f j else 0 := by
  classical
  have hsubset : Finset.range m ⊆ Finset.range n := by
    intro j hj
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hj) hmn)
  have hzero : ∀ j ∈ Finset.range n, j ∉ Finset.range m →
      (if j < m then f j else 0) = 0 := by
    intro j hj hnot
    have hnotlt : ¬ j < m := by
      intro h
      exact hnot (Finset.mem_range.mpr h)
    simp [hnotlt]
  calc
    (∑ j ∈ Finset.range m, f j) =
        ∑ j ∈ Finset.range m, (if j < m then f j else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < m := Finset.mem_range.mp hj
          simp [hjlt]
    _ = ∑ j ∈ Finset.range n, if j < m then f j else 0 :=
      Finset.sum_subset hsubset hzero

/-- The total endpoint term obtained by repeated integration by parts is
exactly the canonical momentum pairing sum_j p_j D^j(q), with p_j in the
direct m-indexed Ostrogradsky form. -/
theorem totalBoundary_eq_endpointMomentum_pairing
    (D : R →+ R) (F : ℕ → R) (q : R) (k : ℕ) :
    totalBoundary D F q k =
      ∑ j ∈ Finset.range (k + 1),
        endpointMomentum D F k j * iterD D j q := by
  unfold totalBoundary ibpBoundary
  calc
    (∑ m ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range m,
        negIterD D (m - 1 - j) (F m) * iterD D j q) =
      ∑ m ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (k + 1),
          (if j < m then
            negIterD D (m - 1 - j) (F m) * iterD D j q
           else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmn : m ≤ k + 1 :=
          Nat.le_of_lt (Finset.mem_range.mp hm)
        exact sum_range_extend_if_lt m (k + 1) hmn _
    _ =
      ∑ j ∈ Finset.range (k + 1),
        ∑ m ∈ Finset.range (k + 1),
          (if j < m then
            negIterD D (m - 1 - j) (F m) * iterD D j q
           else 0) := by
        rw [Finset.sum_comm]
    _ =
      ∑ j ∈ Finset.range (k + 1),
        endpointMomentum D F k j * iterD D j q := by
        apply Finset.sum_congr rfl
        intro j hj
        unfold endpointMomentum
        calc
          (∑ m ∈ Finset.range (k + 1),
            (if j < m then
              negIterD D (m - 1 - j) (F m) * iterD D j q
             else 0)) =
          ∑ m ∈ Finset.range (k + 1),
            (if j < m then negIterD D (m - 1 - j) (F m) else 0) *
              iterD D j q := by
                apply Finset.sum_congr rfl
                intro m hm
                by_cases h : j < m <;> simp [h]
          _ =
            (∑ m ∈ Finset.range (k + 1),
              if j < m then negIterD D (m - 1 - j) (F m) else 0) *
              iterD D j q := by
                rw [Finset.sum_mul]

end D3A

end CovariantPhaseSpaceAudit
