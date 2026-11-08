import PMElementaryParticles.ChannelParticleLedger
import PMElementaryParticles.TierLedger

/-! **Channel × tier status ledger.**

Each channel row is expanded over the allowed tiers of its base protocol.  The
row records the channel, protocol state, mass provenance and decay provenance.
This is a status ledger, not a derivation: `e8` means the current library has an
E8 formula; `comparison` means measured input; `partial` means some channels are
E8 and others are blocked; `blocked`/`notModeled` are explicit gaps.
-/

noncomputable section
namespace PMElementaryParticles.ChannelStatusLedger

open PMElementaryParticles.ChannelParticleLedger
open PMElementaryParticles.TierLedger
open PMElementaryParticles.ProtocolDynamics

/-- One channel × tier row. -/
structure ChannelStatusRow where
  row : ChannelRow
  state : State
  mass : Provenance
  decay : Provenance

/-- Expand one channel row over its allowed tiers. -/
def statusRowsFor (r : ChannelRow) : List ChannelStatusRow :=
  match r.base with
  | none => []
  | some b =>
      (tiersFor b).map fun t =>
        ⟨r, (b, t), massProvenance (b, t), decayProvenance (b, t)⟩

/-- The full channel × tier status ledger. -/
def statusLedger : List ChannelStatusRow :=
  ledger.flatMap statusRowsFor


end PMElementaryParticles.ChannelStatusLedger
