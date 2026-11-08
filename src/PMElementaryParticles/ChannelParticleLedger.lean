import PMElementaryParticles.SubstrateFinalStates
import PMElementaryParticles.CarrierSpecies
import PMElementaryParticles.ChargeProtocols

/-! **Channel → base protocol → species ledger.**

One row per substrate channel.  The row records the channel index, the base
protocol (if any), the external species label, colour routing, chirality, anchor,
and the rational charge.  Generational tiers are not channel labels; they are a
separate tier ledger.
-/

noncomputable section
namespace PMElementaryParticles.ChannelParticleLedger

open PMElementaryParticles.ProtocolInventory
open PMElementaryParticles.CarrierBridge
open PMElementaryParticles.SubstrateFinalStates

/-- Rational charge of a channel, read through its base protocol. -/
def channelCharge (c : PMConstants.PacketGaugeActions.Channels) : ℚ :=
  match baseProtocol c with
  | some b => baseCharge b
  | none => 0

/-- One row of the channel/particle ledger. -/
structure ChannelRow where
  channel : PMConstants.PacketGaugeActions.Channels
  index : Fin 16
  base : Option BaseProtocol
  species : Option CarrierSpecies
  colourBulk : Bool
  active : Bool
  anchor : Anchor
  charge : ℚ

/-- Build the ledger row for a channel. -/
def row (c : PMConstants.PacketGaugeActions.Channels) : ChannelRow where
  channel := c
  index := PMConstants.PacketGaugeActions.channelIndex c
  base := baseProtocol c
  species := channelSpecies c
  colourBulk := colourBulk c
  active := active c
  anchor := anchor c
  charge := channelCharge c

/-- The full 16-channel ledger. -/
def ledger : List ChannelRow :=
  (Finset.univ : Finset PMConstants.PacketGaugeActions.Channels).toList.map row

theorem ledger_length : ledger.length = 16 := by
  simp [ledger]

/-- Fifteen active channels; one sterile vacancy. -/
theorem active_channels_card :
    (Finset.univ.filter fun c : PMConstants.PacketGaugeActions.Channels =>
      baseProtocol c ≠ none).card = 15 := by
  decide +kernel

/-- The ledger charge is the substrate charge. -/
theorem channelCharge_eq_Q (c : PMConstants.PacketGaugeActions.Channels) :
    (channelCharge c : ℂ) = PMElementaryParticles.ChargeProtocols.Q c := by
  rw [PMElementaryParticles.ChargeProtocols.Q_eval]
  rcases c with ⟨a, s⟩ | ⟨a, s⟩ | s | s <;> fin_cases s <;>
    simp [channelCharge, baseProtocol, baseCharge]

/-- The species field is `none` exactly on the sterile channel. -/
theorem species_none_iff_sterile (c : PMConstants.PacketGaugeActions.Channels) :
    (row c).species = none ↔ baseProtocol c = none := by
  simp [row, channelSpecies]

end PMElementaryParticles.ChannelParticleLedger
