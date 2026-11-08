import PMElementaryParticles.TierLedger

/-! **Composite substrate states.**

A composite state is a cohort of signed constituent states.  The sign records a
particle or antiparticle constituent; the tier records which resonant copy is
used.  Charges are summed from the base-protocol charges.  The named composites
below are comparison labels; the structural object is the signed cohort.
-/

noncomputable section
namespace PMElementaryParticles.CompositeStates

open PMElementaryParticles.ProtocolInventory
open PMElementaryParticles.ProtocolDynamics
open PMElementaryParticles.TierLedger

/-- Particle or antiparticle constituent. -/
inductive Sign
  | particle
  | antiparticle
  deriving DecidableEq, Repr

/-- A signed constituent state. -/
structure SignedState where
  state : State
  sign : Sign

/-- Charge of a signed constituent. -/
def signedCharge (x : SignedState) : ℚ :=
  match x.sign with
  | .particle => baseCharge x.state.1
  | .antiparticle => -baseCharge x.state.1

/-- A composite state is a finite signed cohort. -/
structure CompositeState where
  constituents : List SignedState

/-- Total composite charge. -/
def compositeCharge (c : CompositeState) : ℚ :=
  (c.constituents.map signedCharge).sum

/-- Meson-like: two constituents. -/
def CompositeState.isMeson (c : CompositeState) : Bool :=
  c.constituents.length = 2

/-- Baryon-like: three constituents. -/
def CompositeState.isBaryon (c : CompositeState) : Bool :=
  c.constituents.length = 3

def up (t : Tier) : SignedState := ⟨(.up, t), .particle⟩
def down (t : Tier) : SignedState := ⟨(.down, t), .particle⟩
def antiUp (t : Tier) : SignedState := ⟨(.up, t), .antiparticle⟩
def antiDown (t : Tier) : SignedState := ⟨(.down, t), .antiparticle⟩

/-- Charged pion cohort `u + anti-d`. -/
def pionPlus : CompositeState :=
  ⟨[up t0, antiDown t0]⟩

/-- Neutral pion cohort `u + anti-u`. -/
def pionZero : CompositeState :=
  ⟨[up t0, antiUp t0]⟩

/-- Charged kaon cohort `u + anti-s`, with `s` at tier 1. -/
def kaonPlus : CompositeState :=
  ⟨[up t0, antiDown t1]⟩

/-- Proton cohort `u + u + d`. -/
def proton : CompositeState :=
  ⟨[up t0, up t0, down t0]⟩

/-- Neutron cohort `u + d + d`. -/
def neutron : CompositeState :=
  ⟨[up t0, down t0, down t0]⟩

theorem pionPlus_charge : compositeCharge pionPlus = 1 := by
  norm_num [compositeCharge, signedCharge, pionPlus, up, antiDown, baseCharge]

theorem pionZero_charge : compositeCharge pionZero = 0 := by
  norm_num [compositeCharge, signedCharge, pionZero, up, antiUp, baseCharge]

theorem kaonPlus_charge : compositeCharge kaonPlus = 1 := by
  norm_num [compositeCharge, signedCharge, kaonPlus, up, antiDown, baseCharge]

theorem proton_charge : compositeCharge proton = 1 := by
  norm_num [compositeCharge, signedCharge, proton, up, down, baseCharge]

theorem neutron_charge : compositeCharge neutron = 0 := by
  norm_num [compositeCharge, signedCharge, neutron, up, down, baseCharge]

theorem pionPlus_meson : pionPlus.isMeson = true := rfl
theorem kaonPlus_meson : kaonPlus.isMeson = true := rfl
theorem proton_baryon : proton.isBaryon = true := rfl
theorem neutron_baryon : neutron.isBaryon = true := rfl

end PMElementaryParticles.CompositeStates
