import Mathlib
import HoravaMetricKG

/-!
# Four-dimensional KG operator with genuine Fréchet pd derivatives

For arbitrary C² complex scalar fields on real Boyer--Lindquist coordinates,
`pd i f x` is a genuine real Fréchet pd derivative, not a jet variable.
We prove the divergence of the sparse inverse-metric tensor is precisely its
four component differential operator. This is the physical real-coordinate/complex-field differential setting.
No proof placeholders or extra axioms.
-/

namespace HoravaKGCalculus

abbrev Point := Fin 4 → ℝ
abbrev ScalarField := Point → ℂ

/-- Actual i-th Fréchet coordinate derivative of a scalar field. -/
noncomputable def pd (i : Fin 4) (f : ScalarField) (x : Point) : ℂ :=
  (fderiv ℝ f x) (Pi.single i (1 : ℝ))

/-- Contravariant rotating metric with only six independent nonzero entries. -/
def sparseInv (tt tp pp rr aa : ScalarField)
    (i j : Fin 4) : ScalarField :=
  if i = 0 ∧ j = 0 then tt
  else if i = 0 ∧ j = 3 then tp
  else if i = 3 ∧ j = 0 then tp
  else if i = 3 ∧ j = 3 then pp
  else if i = 1 ∧ j = 1 then rr
  else if i = 2 ∧ j = 2 then aa
  else 0

/-- Full covariant scalar d'Alembertian: 1/J ∂μ(J g^μν ∂ν Φ). -/
noncomputable def covKG (J : ScalarField) (g : Fin 4 → Fin 4 → ScalarField)
    (phi : ScalarField) (x : Point) : ℂ :=
  ((∑ i : Fin 4,
    pd i (fun y => J y * (∑ j : Fin 4, g i j y * pd j phi y)) x)) / J x

/-- Fully expanded four-direction operator, before using stationarity. -/
noncomputable def kgFourFlux (J tt tp pp rr aa : ScalarField)
    (phi : ScalarField) (x : Point) : ℂ :=
   (pd 0 (fun y => J y * (tt y * pd 0 phi y +
     tp y * pd 3 phi y)) x +
    pd 1 (fun y => J y * (rr y * pd 1 phi y)) x +
    pd 2 (fun y => J y * (aa y * pd 2 phi y)) x +
    pd 3 (fun y => J y * (tp y * pd 0 phi y +
     pp y * pd 3 phi y)) x) / J x

/-- Equality as differential operators on every scalar field, not only modes. -/
theorem covKG_eq_fourFlux
    (J tt tp pp rr aa phi : ScalarField) (x : Point) :
    covKG J (sparseInv tt tp pp rr aa) phi x =
      kgFourFlux J tt tp pp rr aa phi x := by
  simp [covKG, kgFourFlux, sparseInv, Fin.sum_univ_four]


/-- The true multivariable product rule for any scalar field on ℝ⁴. -/
theorem pd_product (i : Fin 4) (f g : ScalarField) (x : Point)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y * g y) x =
      pd i f x * g x + f x * pd i g x := by
  unfold pd
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp only [smul_eq_mul]
  ring

/-- General coordinate-line Leibniz rule, used in the non-constant coefficients. -/
theorem derivative_product (f g : ℝ → ℂ) (z : ℝ)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    deriv (fun w => f w * g w) z =
      deriv f z * g z + f z * deriv g z := by
  exact deriv_mul hf hg

/-- Genuine second derivative of an arbitrary C² product. -/
theorem second_derivative_product
    (f g : ℝ → ℂ) (z : ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hdf : DifferentiableAt ℝ (deriv f) z)
    (hdg : DifferentiableAt ℝ (deriv g) z) :
    deriv (fun w => deriv (fun v => f v * g v) w) z =
      deriv (deriv f) z * g z +
      2 * deriv f z * deriv g z +
      f z * deriv (deriv g) z := by
  have hpoint : (fun w => deriv (fun v => f v * g v) w) =
    (fun w => deriv f w * g w + f w * deriv g w) := by
    funext w
    exact deriv_mul (hf w) (hg w)
  rw [hpoint]
  change deriv (deriv f * g + f * deriv g) z =
    deriv (deriv f) z * g z +
      2 * deriv f z * deriv g z + f z * deriv (deriv g) z
  rw [deriv_add (hdf.mul (hg z)) ((hf z).mul hdg)]
  rw [deriv_mul hdf (hg z), deriv_mul (hf z) hdg]
  ring



/-- The complete radial Sturm--Liouville differential product, with genuine
    derivatives of arbitrary C² complex-valued profiles on the real r-axis. -/
theorem radial_weighted_second_derivative
    (delta scale u : ℝ → ℂ) (r : ℝ)
    (hdelta : Differentiable ℝ delta)
    (hscale : Differentiable ℝ scale)
    (hu : Differentiable ℝ u)
    (hdscale : DifferentiableAt ℝ (deriv scale) r)
    (hdu : DifferentiableAt ℝ (deriv u) r) :
    deriv (fun z => delta z *
        deriv (fun w => scale w * u w) z) r =
      deriv delta r * (deriv scale r * u r + scale r * deriv u r) +
      delta r * (deriv (deriv scale) r * u r +
        2 * deriv scale r * deriv u r +
        scale r * deriv (deriv u) r) := by
  have hR : (fun z => deriv (fun w => scale w * u w) z) =
      (fun z => deriv scale z * u z + scale z * deriv u z) := by
    funext z
    exact deriv_mul (hscale z) (hu z)
  have hRdiff : DifferentiableAt ℝ
      (fun z => deriv (fun w => scale w * u w) z) r := by
    rw [hR]
    exact (hdscale.mul (hu r)).add ((hscale r).mul hdu)
  have houter :
      deriv (fun z => delta z * deriv (fun w => scale w * u w) z) r =
        deriv delta r * deriv (fun w => scale w * u w) r +
        delta r * deriv (fun z => deriv (fun w => scale w * u w) z) r := by
    change deriv (delta * (fun z => deriv (fun w => scale w * u w) z)) r = _
    exact deriv_mul (hdelta r) hRdiff
  rw [houter]
  rw [congrFun hR r,
      second_derivative_product scale u r hscale hu hdscale hdu]

/-! ### Physical rotating Hořava metric coefficients

Coordinates are real (t,r,θ,φ), while the Klein--Gordon field is complex.
All expressions have the same meaning as the paper's ADM inverse metric.
-/

def bhR (x : Point) : ℂ := (x 1 : ℂ)
noncomputable def bhSin (x : Point) : ℂ := (Real.sin (x 2) : ℂ)
noncomputable def bhCos (x : Point) : ℂ := (Real.cos (x 2) : ℂ)

def bhD (a : ℂ) (x : Point) : ℂ :=
  bhR x ^ 2 + a ^ 2

def bhDelta (M a : ℂ) (x : Point) : ℂ :=
  bhD a x - 2 * M * bhR x

noncomputable def bhRho (a : ℂ) (x : Point) : ℂ :=
  bhR x ^ 2 + a ^ 2 * bhCos x ^ 2

noncomputable def bhSigma (M a : ℂ) (x : Point) : ℂ :=
  bhD a x ^ 2 - a ^ 2 * bhDelta M a x * bhSin x ^ 2

noncomputable def bhJ (a : ℂ) (x : Point) : ℂ :=
  bhRho a x * bhSin x

noncomputable def bhTT (M a : ℂ) (x : Point) : ℂ :=
  -bhSigma M a x / (bhDelta M a x * bhRho a x)

noncomputable def bhTP (M a eta : ℂ) (x : Point) : ℂ :=
  -(2 * M * a * bhR x * (1 + eta)) /
    (bhDelta M a x * bhRho a x)

noncomputable def bhPP (M a eta : ℂ) (x : Point) : ℂ :=
  bhRho a x / (bhSigma M a x * bhSin x ^ 2) -
    4 * M ^ 2 * a ^ 2 * bhR x ^ 2 * (1 + eta) ^ 2 /
      (bhDelta M a x * bhRho a x * bhSigma M a x)

noncomputable def bhRR (M a : ℂ) (x : Point) : ℂ :=
  bhDelta M a x / bhRho a x

noncomputable def bhAA (a : ℂ) (x : Point) : ℂ :=
  1 / bhRho a x

/-- The *actual* four-variable curved-space KG divergence for the paper's
    exact metric, before separation or approximation. -/
noncomputable def rotatingHoravaKG
    (M a eta : ℂ) (phi : ScalarField) (x : Point) : ℂ :=
  covKG (bhJ a)
    (sparseInv (bhTT M a) (bhTP M a eta) (bhPP M a eta)
      (bhRR M a) (bhAA a)) phi x

/-- True Fréchet differential-operator identity for every complex field
    on the real four-dimensional coordinate chart (not just mode ansätze). -/
theorem rotatingHoravaKG_fourFlux
    (M a eta : ℂ) (phi : ScalarField) (x : Point) :
    rotatingHoravaKG M a eta phi x =
      kgFourFlux (bhJ a) (bhTT M a) (bhTP M a eta)
        (bhPP M a eta) (bhRR M a) (bhAA a) phi x := by
  exact covKG_eq_fourFlux _ _ _ _ _ _ _ _

end HoravaKGCalculus
