import PMAction.HermitianTransport
import PMConstants.LinkFromEvents
import Mathlib.Analysis.Matrix.Spectrum

/-! Discharge spectral data from the actual W/Z link response. The spectral
basis is constructed by the Hermitian spectral theorem. A positive small-step
radius is supplied automatically. The physical link/readout model and overall
mass scale remain inherited assumptions. -/
noncomputable section
namespace PMConstants.LinkSpectralResponse
open Matrix Finset PMAction PMAction.LinkExpansion

namespace HermitianTransport
export PMAction.HermitianTransport
  (basis basis_left basis_right generated transport
   diagonal_unitary transport_unitary transport_zero radius radius_pos
   small_eigenphases coefficient coefficient_nonneg controlled_response)
end HermitianTransport

/-- The supplied scalar-link generator is Hermitian for every real field value. -/
theorem theta_hermitian (g gp W₁ W₂ W₃ B : ℝ) :
    (LinkMass.theta g gp W₁ W₂ W₃ B).IsHermitian := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [LinkMass.theta,conjTranspose_apply]; ring_nf; simp

variable (g gp W₁ W₂ W₃ B : ℝ)

def linkTransport (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  HermitianTransport.transport (theta_hermitian g gp W₁ W₂ W₃ B) ε

def linkRadius : ℝ := HermitianTransport.radius (theta_hermitian g gp W₁ W₂ W₃ B)
def linkCoefficient : ℝ :=
  HermitianTransport.coefficient (theta_hermitian g gp W₁ W₂ W₃ B) ![0,1]

theorem link_radius_pos : 0 < linkRadius g gp W₁ W₂ W₃ B := HermitianTransport.radius_pos _

theorem link_unitary (ε : ℝ) :
    linkTransport g gp W₁ W₂ W₃ B ε ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
  HermitianTransport.transport_unitary _ _

/-- No eigenbasis, diagonalization equation or unexplained eigenphase bound
is an input: only the stated positive step-radius restriction remains. -/
theorem mass_form_controlled {ε : ℝ} (he : |ε| ≤ linkRadius g gp W₁ W₂ W₃ B) :
    |CommonResponse.nsq (![0,1]-linkTransport g gp W₁ W₂ W₃ B ε*ᵥ ![0,1])-
      ε^2*((g^2/4)*(W₁^2+W₂^2)+(1/4)*(g*W₃-gp*B)^2)| ≤
      linkCoefficient g gp W₁ W₂ W₃ B*ε^4 := by
  have h := HermitianTransport.controlled_response
    (theta_hermitian g gp W₁ W₂ W₃ B) ![0,1] he
  rw [LinkFromEvents.vacuum_generator_norm] at h
  exact h

end PMConstants.LinkSpectralResponse
