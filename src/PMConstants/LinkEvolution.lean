import PMAction.LinkEvolution
import PMConstants.LinkSpectralResponse

/-! Paper III compatibility names and the W/Z specialization.
The general evolution proofs now live in Paper II. -/
noncomputable section
namespace PMConstants.LinkEvolution
open Matrix PMAction.HermitianTransport
export PMAction.LinkEvolution
  (phase_add conjugate_mul diagonal_exponential diagonalization_exponential transport_eq_exp
   basis_independent transport_add transport_reverse evolution)

/-- The controlled W/Z result now refers to the ordinary matrix exponential. -/
theorem mass_form_exponential (g gp W₁ W₂ W₃ B ε : ℝ)
    (he : |ε| ≤ LinkSpectralResponse.linkRadius g gp W₁ W₂ W₃ B) :
    |PMAction.CommonResponse.nsq (![0,1]-
        NormedSpace.exp (((ε : ℂ)*Complex.I) • LinkMass.theta g gp W₁ W₂ W₃ B)*ᵥ ![0,1])-
      ε^2*((g^2/4)*(W₁^2+W₂^2)+(1/4)*(g*W₃-gp*B)^2)| ≤
      LinkSpectralResponse.linkCoefficient g gp W₁ W₂ W₃ B*ε^4 := by
  have h := LinkSpectralResponse.mass_form_controlled g gp W₁ W₂ W₃ B he
  simpa only [LinkSpectralResponse.linkTransport,transport_eq_exp] using h

end PMConstants.LinkEvolution
