import PMElementaryParticles.ProtocolInventory

/-! **Experimental/candidate module.**

# Carrier → species bridge

The substrate link/channel labels live in PMAction/PMSubstrate.  The base routing
protocols live in `ProtocolInventory`.  This module supplies the next bridge:
channel label → base protocol → external species label.

It does **not** assign masses or amplitudes; those remain downstream.
-/

noncomputable section
namespace PMElementaryParticles.CarrierBridge

open PMElementaryParticles.ProtocolInventory

/-- External species labels available from the four base protocols. -/
inductive CarrierSpecies
  | electron | up | down | neutrino
  deriving DecidableEq, Repr

/-- Forget the protocol name to the external species label. -/
def ofBaseProtocol : BaseProtocol → CarrierSpecies
  | .electron => .electron
  | .up => .up
  | .down => .down
  | .neutrino => .neutrino

/-- Channel label → species, with `none` for the sterile vacancy. -/
def channelSpecies (c : PMConstants.PacketGaugeActions.Channels) : Option CarrierSpecies :=
  (baseProtocol c).map ofBaseProtocol

/-- The sterile vacancy has no species. -/
theorem sterile_channelSpecies_none (c : PMConstants.PacketGaugeActions.Channels)
    (h : baseProtocol c = none) : channelSpecies c = none := by
  simp [channelSpecies, h]

/-- Every non-sterile channel has a species. -/
theorem channelSpecies_some (c : PMConstants.PacketGaugeActions.Channels) (h : baseProtocol c ≠ none) :
    ∃ s, channelSpecies c = some s := by
  cases hb : baseProtocol c with
  | none => contradiction
  | some b => exact ⟨ofBaseProtocol b, by simp [channelSpecies, hb]⟩

/-- Charge of the external species label. -/
def CarrierSpecies.charge : CarrierSpecies → ℚ
  | .electron => -1
  | .up => 2 / 3
  | .down => -1 / 3
  | .neutrino => 0

/-- The carrier→species bridge respects the E8 charge grading. -/
theorem channelSpecies_charge {c : PMConstants.PacketGaugeActions.Channels}
    {s : CarrierSpecies} (h : channelSpecies c = some s) :
    ChargeProtocols.Q c = s.charge := by
  unfold channelSpecies at h
  cases hb : baseProtocol c with
  | none => simp [hb] at h
  | some b =>
      simp [hb] at h
      rcases h with rfl
      cases b
      · simpa [ofBaseProtocol, CarrierSpecies.charge] using baseProtocol_charge.2.2.1 c hb
      · simpa [ofBaseProtocol, CarrierSpecies.charge] using baseProtocol_charge.1 c hb
      · simpa [ofBaseProtocol, CarrierSpecies.charge] using baseProtocol_charge.2.1 c hb
      · simpa [ofBaseProtocol, CarrierSpecies.charge] using baseProtocol_charge.2.2.2 c hb

end PMElementaryParticles.CarrierBridge
