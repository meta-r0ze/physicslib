import PMElementaryParticles.PhaseToRecord
import PMElementaryParticles.RecordPortIdentification

/-!
# EP protocols on the certified bit-ring machine

A protocol is finite data only:

* one of the 16 packet labels;
* a reference record (colour or lepton);
* one firing pattern per record-bit ring on the 3-ring;
* one certified comparison phase per bit encounter;
* a packet position.

The certified comparison phases are `0` and `π`: `ElectricHeavyRecord.phase_position`
and `phase_sector` produce exact `0/1` flags only at those phases, and
`PhaseToRecord.exact_bit_flip` gives the `π` full flip.  No free real phase is
admitted.

The per-period receiver Toll is the bit-ring table sum: a bit ring registers
only where the label bit differs from the reference bit, and then its weight is
`patternSum` for that firing pattern.
-/

noncomputable section
set_option maxRecDepth 10000
namespace PMElementaryParticles.Protocol

open PMConstants.PacketGaugeActions
open PMKAutomaton
open PMKAutomaton.RingReceiver
open PMElementaryParticles.IsolatedExcitation
open PMElementaryParticles.HeavyFlipControl

/-- Certified comparison phases: `false = 0`, `true = π`. -/
abbrev CertifiedPhase := Bool

def phaseValue (b : CertifiedPhase) : ℝ := if b then Real.pi else 0

end PMElementaryParticles.Protocol

namespace PMElementaryParticles

/-- One protocol on the 3-ring. Its operations live in the namespace
`PMElementaryParticles.Protocol`. -/
structure Protocol where
  label : PMConstants.PacketGaugeActions.Channels
  reference : Bool
  firing : Fin 2 → Fin 3 → Bool
  phase : Fin 2 → Protocol.CertifiedPhase
  x0 : Fin 3

deriving instance DecidableEq for Protocol
deriving instance Fintype for Protocol

end PMElementaryParticles

namespace PMElementaryParticles.Protocol

open PMConstants.PacketGaugeActions
open PMKAutomaton
open PMKAutomaton.RingReceiver
open PMElementaryParticles.IsolatedExcitation
open PMElementaryParticles.HeavyFlipControl

/-- The label record bit at sector/position. -/
def labelBit (p : Protocol) (b : Fin 2) : Bool :=
  bitOf (labelRecord p.label) b

/-- The reference record bit. -/
def referenceBit (p : Protocol) (b : Fin 2) : Bool :=
  bitOf (refRecord p.reference) b

/-- A ring registers only where the label bit differs from the reference bit. -/
def bitDiffers (p : Protocol) (b : Fin 2) : Bool :=
  labelBit p b != referenceBit p b

/-- Per-period receiver Toll: the two bit-ring sums, with the certified phase
`π` acting as the full-flip weight and phase `0` as no registration. -/
noncomputable def receiverToll (p : Protocol) : ℝ :=
  ∑ b : Fin 2,
    if p.phase b then
      if bitDiffers p b then (patternSum (p.firing b) p.x0 : ℝ) else 0
    else 0

theorem receiverToll_nonneg (p : Protocol) : 0 ≤ receiverToll p := by
  unfold receiverToll
  apply Finset.sum_nonneg
  intro b _
  by_cases hp : p.phase b
  · by_cases hd : bitDiffers p b
    · simp [hp, hd, Nat.cast_nonneg]
    · simp [hp, hd]
  · simp [hp]

/-- Empty firing on both rings. -/
def emptyProtocol (label : Channels) (reference : Bool) (x0 : Fin 3) : Protocol where
  label := label
  reference := reference
  firing _ _ := false
  phase _ := true
  x0 := x0

theorem patternSum_empty (x0 : Fin 3) :
    patternSum (fun _ => false) x0 = 0 := by
  fin_cases x0 <;> decide +kernel

theorem emptyProtocol_toll_zero (label : Channels) (reference : Bool) (x0 : Fin 3) :
    receiverToll (emptyProtocol label reference x0) = 0 := by
  unfold receiverToll emptyProtocol
  apply Finset.sum_eq_zero
  intro b _
  simp [patternSum_empty]

/-- The complete finite protocol family. -/
def allProtocols : Finset Protocol := Finset.univ

theorem allProtocols_complete (p : Protocol) : p ∈ allProtocols :=
  Finset.mem_univ p

end PMElementaryParticles.Protocol
