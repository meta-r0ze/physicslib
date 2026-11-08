import PMElementaryParticles.SubstrateTransition
import PMElementaryParticles.CarrierAmplitude

/-! **Carrier-product transition operator.**

A first substrate-native operator: the weak amplitude for a final-state cohort is
the source weak coupling times the product of the final-carrier weak couplings.
The operator is zero when the cohort is not an allowed `Decay`.

This is a leading carrier-product operator, not the full nonperturbative
interaction.  It makes the general transition form concrete and removes the
per-particle amplitude from the muon example.
-/

noncomputable section
namespace PMElementaryParticles.CarrierTransitionOperator

open PMElementaryParticles.ProtocolDynamics
open PMElementaryParticles.CarrierBridge
open PMElementaryParticles.CarrierCouplings
open PMElementaryParticles.SubstrateTransition

/-- Weak coupling of a carrier species as a complex amplitude. -/
def weakOf (s : CarrierSpecies) : ℂ := ((amplitude s).weak : ℂ)

/-- Leading carrier-product amplitude: source coupling times final couplings. -/
def carrierProductAmplitude (source : CarrierSpecies) (final : List CarrierSpecies) : ℂ :=
  weakOf source * (final.map weakOf).prod

/-- The substrate transition operator on protocol states. -/
def substrateOperator (i : State) (f : List State) : ℂ := by
  classical
  exact if Decay i f then
    carrierProductAmplitude (ofBaseProtocol i.1) (f.map (fun x => ofBaseProtocol x.1))
  else 0

theorem substrateOperator_zero_of_not_decay {i : State} {f : List State}
    (h : ¬ Decay i f) : substrateOperator i f = 0 := by
  simp [substrateOperator, h]

/-- A muon-cohort system whose operator is the carrier-product operator. -/
def muonOperatorSystem (phase : ℝ) : TransitionSystem where
  operator := substrateOperator
  phaseSpace := fun i f =>
    if i = muonInitial ∧ f = muonFinal then phase else 0
  finals := {muonFinal}

theorem muonOperatorSystem_totalWidth (phase : ℝ) :
    totalWidth (muonOperatorSystem phase) muonInitial =
      Complex.normSq (substrateOperator muonInitial muonFinal) * phase := by
  unfold totalWidth muonOperatorSystem partialWidth
  rw [Finset.sum_singleton]
  simp [PMElementaryParticles.SubstrateTransition.muon_decay]

/-- Tau initial state: electron protocol at tier 2. -/
def tauInitial : State := (.electron, ⟨2, by decide⟩)

theorem tau_decay : Decay tauInitial muonFinal := by
  refine ⟨by simp [muonFinal], ?_, ?_⟩
  · norm_num [cohortCharge, baseCharge, muonFinal, tauInitial]
  · intro d hd
    simp only [muonFinal, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> decide

/-- A tau-cohort system with the same carrier-product operator. -/
def tauOperatorSystem (phase : ℝ) : TransitionSystem where
  operator := substrateOperator
  phaseSpace := fun i f =>
    if i = tauInitial ∧ f = muonFinal then phase else 0
  finals := {muonFinal}

theorem tauOperatorSystem_totalWidth (phase : ℝ) :
    totalWidth (tauOperatorSystem phase) tauInitial =
      Complex.normSq (substrateOperator tauInitial muonFinal) * phase := by
  unfold totalWidth tauOperatorSystem partialWidth
  rw [Finset.sum_singleton]
  simp [tau_decay]

end PMElementaryParticles.CarrierTransitionOperator
