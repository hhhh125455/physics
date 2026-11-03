import Mathlib

/-!
# Local characteristic rectangle inequality

Unlike the global-C2 lemma in CharacteristicCorner, this theorem assumes
only continuity on a closed rectangle and differentiability strictly inside
each coordinate interval. The corner may fail to be differentiable.

This is the appropriate regularity pattern for a first singular point:
the area variable may be continuous and zero at the corner, while smooth
on the two open characteristic edges away from the corner.
No PDE existence or critical-parameter transversality is assumed.
-/

namespace GammaHalf

theorem local_rectangle_supermodular
    (X : ℝ → ℝ → ℝ)
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hcontU : ∀ v ∈ Set.Icc c d,
      ContinuousOn (fun u => X u v) (Set.Icc a b))
    (hdiffU : ∀ v ∈ Set.Icc c d, ∀ u ∈ Set.Ioo a b,
      DifferentiableAt ℝ (fun z => X z v) u)
    (hcontXu : ∀ u ∈ Set.Ioo a b,
      ContinuousOn (fun v => deriv (fun z => X z v) u) (Set.Icc c d))
    (hdiffXu : ∀ u ∈ Set.Ioo a b,
      DifferentiableOn ℝ (fun v => deriv (fun z => X z v) u) (Set.Ioo c d))
    (hmix : ∀ u ∈ Set.Ioo a b, ∀ v ∈ Set.Ioo c d,
      0 ≤ deriv (fun y => deriv (fun z => X z y) u) v) :
    X b d + X a c ≥ X b c + X a d := by
  have hc : c ∈ Set.Icc c d := ⟨le_rfl, hcd⟩
  have hd : d ∈ Set.Icc c d := ⟨hcd, le_rfl⟩
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hD (z : ℝ) (hz : z ∈ Set.Ioo a b) :
      0 ≤ deriv (fun t => X t d - X t c) z := by
    have hmono : MonotoneOn
        (fun y => deriv (fun t => X t y) z) (Set.Icc c d) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc c d)
        (hcontXu z hz)
      · simpa only [interior_Icc] using hdiffXu z hz
      · intro y hy
        have hy' : y ∈ Set.Ioo c d := by simpa only [interior_Icc] using hy
        exact hmix z hz y hy'
    have hmv : deriv (fun t => X t c) z ≤
        deriv (fun t => X t d) z := hmono hc hd hcd
    have hdv : HasDerivAt (fun t => X t d)
        (deriv (fun t => X t d) z) z :=
      (hdiffU d hd z hz).hasDerivAt
    have hd0 : HasDerivAt (fun t => X t c)
        (deriv (fun t => X t c) z) z :=
      (hdiffU c hc z hz).hasDerivAt
    have heq : deriv (fun t => X t d - X t c) z =
        deriv (fun t => X t d) z - deriv (fun t => X t c) z := by
      have hfun : (fun t => X t d - X t c) =
          (fun t => X t d) - (fun t => X t c) := by
        funext t
        rfl
      rw [hfun]
      exact (hdv.sub hd0).deriv
    rw [heq]
    linarith
  have hcontg : ContinuousOn (fun z => X z d - X z c)
      (Set.Icc a b) := (hcontU d hd).sub (hcontU c hc)
  have hdiffg : DifferentiableOn ℝ (fun z => X z d - X z c)
      (Set.Ioo a b) := by
    intro z hz
    exact ((hdiffU d hd z hz).sub (hdiffU c hc z hz)).differentiableWithinAt
  have hmono : MonotoneOn (fun z => X z d - X z c)
      (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hcontg
    · simpa only [interior_Icc] using hdiffg
    · intro z hz
      have hz' : z ∈ Set.Ioo a b := by simpa only [interior_Icc] using hz
      exact hD z hz'
  have h := hmono ha hb hab
  dsimp at h
  linarith

end GammaHalf
