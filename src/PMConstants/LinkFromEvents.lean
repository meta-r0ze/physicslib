import PMAction.LinkExpansion
import PMConstants.LinkMass
import PMConstants.EventStiffness

/-!
# The W/Z mass form is the leading event-law link response

`LinkMass` took the scalar link cost to be `|θφ̂|²` for the vacuum direction `φ̂ = (0,1)`.
Paper II now prices the link by the event law, cost `(toll·m/4)‖φ̂ − U_εφ̂‖²`
(`PMAction.CommonResponse`), and `PMAction.LinkExpansion.link_expansion` expands it.

* `vacuum_generator_norm`: `‖θφ̂‖² = (g²/4)(W₁² + W₂²) + (1/4)(gW₃ − g'B)²`, the quadratic form of
  `LinkMass.link_quadratic` and `GaugeSpectrum`.
* `mass_form_from_events`: for any unitary eigenbasis of `θ`, the event-law link cost of the vacuum
  direction is `ε²` times that form, with remainder at most `(5/48)ε⁴Σ|c_k|²λ_k⁴`. The charged
  `g²v²/4` and neutral `(g² + g'²)v²/4` mass terms (`w_mass_term`, `z_mass_term`) are therefore
  the leading response of the link readout. They share the gauge prefactor if the link is priced
  by the same event as the gauge plaquette; that is a premise (`EventStiffness.scalar_shares_prefactor`).
-/

noncomputable section
namespace PMConstants.LinkFromEvents
open Matrix PMAction PMAction.LinkExpansion LinkMass

theorem vacuum_generator_norm (g gp W₁ W₂ W₃ B : ℝ) :
    CommonResponse.nsq (theta g gp W₁ W₂ W₃ B *ᵥ ![0, 1]) =
      (g^2/4) * (W₁^2 + W₂^2) + (1/4) * (g*W₃ - gp*B)^2 := by
  rw [theta_on_vacuum, nsq_eq, Fin.sum_univ_two, link_quadratic]

theorem mass_form_from_events (g gp W₁ W₂ W₃ B : ℝ) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (hV1 : Vᴴ * V = 1) (hV2 : V * Vᴴ = 1) (lam : Fin 2 → ℝ)
    (hθ : theta g gp W₁ W₂ W₃ B = V * genDiag lam * Vᴴ) (ε : ℝ) (h : ∀ k, |ε * lam k| ≤ 1) :
    |CommonResponse.nsq (![0, 1] - (V * phaseDiag lam ε * Vᴴ) *ᵥ ![0, 1]) -
        ε^2 * ((g^2/4) * (W₁^2 + W₂^2) + (1/4) * (g*W₃ - gp*B)^2)| ≤
      5/48 * ε^4 * ∑ k, Complex.normSq ((Vᴴ *ᵥ ![0, 1]) k) * lam k ^ 4 := by
  rw [← vacuum_generator_norm, hθ]
  exact link_expansion V hV1 hV2 lam ε ![0, 1] h

end PMConstants.LinkFromEvents
