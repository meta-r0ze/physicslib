import PMHadrons.CompositeStates
import PMElementaryParticles.CarrierTransitionOperator

/-! **Composite transition operator.**

A composite decay is a nonempty final cohort of composite states with conserved
total charge.  The leading amplitude is the product of the weak carrier
couplings of all constituent states.  This is the composite extension of the
carrier-product operator, not a full bound-state calculation.
-/

noncomputable section
namespace PMHadrons.CompositeTransition
open PMElementaryParticles

open PMHadrons.CompositeStates
open PMElementaryParticles.CarrierTransitionOperator
open PMElementaryParticles.CarrierBridge

/-- Leading weak amplitude of a composite cohort. -/
def compositeAmplitude (c : CompositeState) : ℂ :=
  (c.constituents.map fun x => weakOf (ofBaseProtocol x.state.1)).prod

/-- Total charge of a list of composite states. -/
def compositeChargeList (fs : List CompositeState) : ℚ :=
  (fs.map compositeCharge).sum

/-- Composite decay: nonempty final cohort with conserved charge. -/
def CompositeDecay (i : CompositeState) (fs : List CompositeState) : Prop :=
  fs ≠ [] ∧ compositeChargeList fs = compositeCharge i

/-- Composite transition operator. -/
def compositeOperator (i : CompositeState) (fs : List CompositeState) : ℂ := by
  classical
  exact if CompositeDecay i fs then
    compositeAmplitude i * (fs.map compositeAmplitude).prod
  else 0

/-- `K⁺ → π⁺ π⁰` as a composite cohort. -/
def kaonPionFinal : List CompositeState := [pionPlus, pionZero]

theorem kaonPion_charge :
    compositeChargeList kaonPionFinal = compositeCharge kaonPlus := by
  norm_num [compositeChargeList, compositeCharge, kaonPionFinal, pionPlus, pionZero,
    signedCharge, up, antiDown, antiUp, kaonPlus, kaonPionFinal, PMElementaryParticles.ProtocolDynamics.baseCharge]

theorem kaonPion_decay : CompositeDecay kaonPlus kaonPionFinal := by
  refine ⟨by simp [kaonPionFinal], ?_⟩
  exact kaonPion_charge

theorem kaonPion_operator :
    compositeOperator kaonPlus kaonPionFinal =
      compositeAmplitude kaonPlus *
        (compositeAmplitude pionPlus * compositeAmplitude pionZero) := by
  unfold compositeOperator
  rw [ite_eq_left kaonPion_decay]
  simp [kaonPionFinal, List.prod_cons]

end PMHadrons.CompositeTransition
