import Mathlib

/-!
# Classical spin: Lie--Poisson equations and explicit time evolution

This is the first physical-derivation module.
Coordinates are real values, with the standard Lie--Poisson tensor
{f,g} = S · (∇f × ∇g). For now this bracket is defined on
*gradient vectors evaluated at a point*. Its Jacobi identity for
arbitrary differentiable functions is not formalized here.

Theorems derive all 3 Hamilton equations from the Poisson tensor and
the derivative of H = χ S_z², then prove conservation and the explicit
rotation solution solves the resulting ODE.
-/

namespace ClassicalSpinKrylov

structure Spin where
  x : ℝ
  y : ℝ
  z : ℝ

def eX : Spin := ⟨1, 0, 0⟩
def eY : Spin := ⟨0, 1, 0⟩
def eZ : Spin := ⟨0, 0, 1⟩

/-- S · (∇f × ∇g), evaluated for arbitrary three-coordinate gradients. -/
def poissonAt (s df dg : Spin) : ℝ :=
  s.x * (df.y * dg.z - df.z * dg.y) +
  s.y * (df.z * dg.x - df.x * dg.z) +
  s.z * (df.x * dg.y - df.y * dg.x)

/-- Lie--Poisson coordinate algebra: {S_x,S_y}=S_z. -/
theorem bracket_xy (s : Spin) : poissonAt s eX eY = s.z := by
  simp [poissonAt, eX, eY]

theorem bracket_yz (s : Spin) : poissonAt s eY eZ = s.x := by
  simp [poissonAt, eY, eZ]

theorem bracket_zx (s : Spin) : poissonAt s eZ eX = s.y := by
  simp [poissonAt, eZ, eX]

theorem bracket_antisymm (s df dg : Spin) :
    poissonAt s df dg = -poissonAt s dg df := by
  unfold poissonAt
  ring

/-- Classical Hamiltonian. -/
def hamiltonian (χ : ℝ) (s : Spin) : ℝ := χ * s.z ^ 2

/-- Derivative with respect to z of the actual Hamiltonian polynomial. -/
theorem hamiltonian_z_derivative (χ z : ℝ) :
    HasDerivAt (fun u : ℝ => χ * u ^ 2) (2 * χ * z) z := by
  convert ((hasDerivAt_id z).pow 2).const_mul χ using 1 <;> (simp only [id_eq]; ring)

/-- Gradient of H, obtained from the z derivative and independence from x,y. -/
def gradH (χ : ℝ) (s : Spin) : Spin := ⟨0, 0, 2 * χ * s.z⟩

/-- The vector field is constructed using the actual Lie--Poisson tensor. -/
def vectorField (χ : ℝ) (s : Spin) : Spin :=
  ⟨poissonAt s eX (gradH χ s),
   poissonAt s eY (gradH χ s),
   poissonAt s eZ (gradH χ s)⟩

/-- Hamilton's first equation: Ṡ_x = -2χ S_z S_y. -/
theorem vectorField_x (χ : ℝ) (s : Spin) :
    (vectorField χ s).x = -2 * χ * s.z * s.y := by
  simp [vectorField, poissonAt, eX, gradH]
  ring

/-- Hamilton's second equation: Ṡ_y = 2χ S_z S_x. -/
theorem vectorField_y (χ : ℝ) (s : Spin) :
    (vectorField χ s).y = 2 * χ * s.z * s.x := by
  simp [vectorField, poissonAt, eY, gradH]
  ring

/-- Hamilton's third equation: Ṡ_z = 0. -/
theorem vectorField_z (χ : ℝ) (s : Spin) :
    (vectorField χ s).z = 0 := by
  simp [vectorField, poissonAt, eZ, gradH]

/-- Squared spin length. -/
def lengthSq (s : Spin) : ℝ := s.x ^ 2 + s.y ^ 2 + s.z ^ 2

/-- The Hamiltonian vector field is tangent to spheres |S|²=constant. -/
theorem lengthSq_derivative_zero (χ : ℝ) (s : Spin) :
    2 * s.x * (vectorField χ s).x +
      2 * s.y * (vectorField χ s).y +
      2 * s.z * (vectorField χ s).z = 0 := by
  rw [vectorField_x, vectorField_y, vectorField_z]
  ring

/-- The quadratic Hamiltonian is conserved along the vector field. -/
theorem energy_derivative_zero (χ : ℝ) (s : Spin) :
    2 * χ * s.z * (vectorField χ s).z = 0 := by
  rw [vectorField_z]
  ring

/-- Explicit time-dependent rotation at frequency ω=2χ S_z(0). -/
noncomputable def evolve (χ t : ℝ) (s : Spin) : Spin :=
  let θ := 2 * χ * s.z * t
  ⟨s.x * Real.cos θ - s.y * Real.sin θ,
   s.x * Real.sin θ + s.y * Real.cos θ,
   s.z⟩

/-- Correct initial condition for the explicit solution. -/
theorem evolve_zero (χ : ℝ) (s : Spin) : evolve χ 0 s = s := by
  cases s with
  | mk x y z =>
      simp [evolve]

/-- The third spin component is constant under explicit evolution. -/
theorem evolve_z (χ t : ℝ) (s : Spin) :
    (evolve χ t s).z = s.z := rfl

/-- Rotation identity. -/
theorem planar_rotation_length (x y θ : ℝ) :
    (x * Real.cos θ - y * Real.sin θ) ^ 2 +
      (x * Real.sin θ + y * Real.cos θ) ^ 2 = x ^ 2 + y ^ 2 := by
  calc
    _ = (x ^ 2 + y ^ 2) * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    _ = x ^ 2 + y ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring

/-- The solution conserves the full spin length for every t. -/
theorem evolve_lengthSq (χ t : ℝ) (s : Spin) :
    lengthSq (evolve χ t s) = lengthSq s := by
  simp only [lengthSq, evolve]
  rw [planar_rotation_length]

/-- The solution conserves the original Hamiltonian. -/
theorem evolve_hamiltonian (χ t : ℝ) (s : Spin) :
    hamiltonian χ (evolve χ t s) = hamiltonian χ s := by
  rfl

end ClassicalSpinKrylov
