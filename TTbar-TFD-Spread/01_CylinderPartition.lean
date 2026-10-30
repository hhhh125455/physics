import Mathlib

namespace TTbarTFD

theorem energy_general (h hbar cL cR : ℝ) :
    (h - cL / 24) + (hbar - cR / 24) =
      h + hbar - (cL + cR) / 24 := by
  ring

theorem energy_equal_c (h hbar c : ℝ) :
    (h - c / 24) + (hbar - c / 24) =
      h + hbar - c / 12 := by
  ring

theorem weight_equal_c (h hbar c β : ℝ) :
    Real.exp (-β * ((h - c / 24) + (hbar - c / 24))) =
      Real.exp (-β * (h + hbar - c / 12)) := by
  rw [energy_equal_c]

theorem finite_partition_equal_c
    (n : ℕ) (h hbar : Fin n → ℝ) (c β : ℝ) :
    (∑ i : Fin n, Real.exp (-β *
        ((h i - c / 24) + (hbar i - c / 24)))) =
      (∑ i : Fin n, Real.exp (-β *
        (h i + hbar i - c / 12))) := by
  apply Finset.sum_congr rfl
  intro i _
  exact weight_equal_c (h i) (hbar i) c β

end TTbarTFD
