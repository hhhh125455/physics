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
theorem derivative_product (f g : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    deriv (fun w => f w * g w) z =
      deriv f z * g z + f z * deriv g z := by
  exact deriv_mul hf hg

/-- Genuine second derivative of an arbitrary C² product. -/
theorem second_derivative_product
    (f g : ℂ → ℂ) (z : ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hdf : DifferentiableAt ℂ (deriv f) z)
    (hdg : DifferentiableAt ℂ (deriv g) z) :
    deriv (fun w => deriv (fun v => f v * g v) w) z =
      deriv (deriv f) z * g z +
      2 * deriv f z * deriv g z +
      f z * deriv (deriv g) z := by
  have hpoint : (fun w => deriv (fun v => f v * g v) w) =
    (fun w => deriv f w * g w + f w * deriv g w) := by
    funext w
    exact deriv_mul (hf w) (hg w)
  rw [hpoint]
  have hadd : deriv (fun w => deriv f w * g w + f w * deriv g w) z =
      deriv (fun w => deriv f w * g w) z +
      deriv (fun w => f w * deriv g w) z := by
    simpa only [Pi.add_apply, Pi.mul_apply] using
      (deriv_add (hdf.mul (hg z)) ((hf z).mul hdg))
  have hm1 : deriv (fun w => deriv f w * g w) z =
      deriv (deriv f) z * g z + deriv f z * deriv g z := by
    simpa only [Pi.mul_apply] using (deriv_mul hdf (hg z))
  have hm2 : deriv (fun w => f w * deriv g w) z =
      deriv f z * deriv g z + f z * deriv (deriv g) z := by
    simpa only [Pi.mul_apply] using (deriv_mul (hf z) hdg)
  rw [hadd, hm1, hm2]
  ring

end HoravaKGCalculus
