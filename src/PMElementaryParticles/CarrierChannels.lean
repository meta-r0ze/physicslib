import PMConstants.ColourRouting
import PMConstants.CarrierRepresentation
import PMConstants.PacketGaugeActions

/-!
# The 16 channels as carriers: wall, axis and sign

`PMConstants.CarrierRepresentation` builds the channel content from carriers. Each nontrivial
D₄ glue class has eight minimal carriers, `±2eᵢ`: four axes, two signs. The reference holds one
axis, the lepton axis `0`; the other three are the colour axes. There are two domain walls.

This module reads every channel of `PacketGaugeActions.Channels` as a triple:

* `wall`: `true` is the wall that carries the reference. `PMAction.ChiralityConvention`
  (`weak_acts_on_reference`) shows the weak current acts on that wall, so "left-handed" is the
  name of this wall, not an input.
* `axis`: `0` is the lepton axis; `1, 2, 3` are the colour axes.
* `positiveSign`: the carrier's sign, the only move that keeps its axis.

Each (wall, carrier) is exactly one channel (`carrier_exists`, `channel_carrier`,
`channel_unique`). The charges come from the
carriers: `bl` by axis and `t3` by sign (`CarrierRepresentation`). The wall charge is `bl` on the
reference wall and `bl + 2 t3` on the other (`hyper_from_carriers`). The electric charge is
`bl/2 + t3` on both walls (`electric`). `packet_charge_eq` shows the packet's charge table
(`PacketGaugeActions.hyperchargeOperator`) is this carrier charge.
-/

noncomputable section

namespace PMElementaryParticles.CarrierChannels

open PMConstants PacketGaugeActions CarrierRepresentation

/-- The wall: `true` is the wall that carries the reference. -/
def wall : Channels → Bool
  | .inl _ => true
  | .inr (.inl _) => false
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr _)) => false

/-- The carrier axis: `0` is the lepton axis, `1, 2, 3` the colour axes. -/
def axis : Channels → Fin 4
  | .inl (c, _) => c.succ
  | .inr (.inl (c, _)) => c.succ
  | .inr (.inr _) => 0

/-- The carrier sign. -/
def positiveSign : Channels → Bool
  | .inl (_, s) => s = 0
  | .inr (.inl (_, s)) => s = 0
  | .inr (.inr (.inl s)) => s = 0
  | .inr (.inr (.inr s)) => s = 0

/-- The axis of a carrier: the one coordinate that is not zero. -/
def carrierAxis (v : CarrierRepresentation.V) : Fin 4 :=
  if coord v 0 ≠ 0 then 0 else if coord v 1 ≠ 0 then 1 else if coord v 2 ≠ 0 then 2 else 3

/-- Every wall and carrier is a channel. -/
theorem carrier_exists :
    ∀ (w : Bool) (v : CarrierRepresentation.V), ∃ c : Channels,
      wall c = w ∧ axis c = carrierAxis v ∧ positiveSign c = positive v := by
  decide +kernel

/-- Every channel is a wall and a carrier. -/
theorem channel_carrier :
    ∀ c : Channels, ∃ v : CarrierRepresentation.V,
      axis c = carrierAxis v ∧ positiveSign c = positive v := by
  decide +kernel

/-- Wall, axis and sign fix the channel. -/
theorem channel_unique :
    ∀ c c' : Channels, wall c = wall c' → axis c = axis c' → positiveSign c = positiveSign c' →
      c = c' := by
  decide

theorem bl_t3_from_carriers :
    ∀ v : CarrierRepresentation.V, bl v = CarrierRepresentation.blAxis (decide (carrierAxis v = 0)) ∧ t3 v = t3Sign (positive v) := by
  decide +kernel

/-- The wall charge (hypercharge) of a channel. -/
def hyper (c : Channels) : ℚ :=
  if wall c then CarrierRepresentation.blAxis (decide (axis c = 0)) else CarrierRepresentation.blAxis (decide (axis c = 0)) + 2 * t3Sign (positiveSign c)

/-- **The wall charge is the carrier charge of `CarrierRepresentation`.** -/
theorem hyper_from_carriers :
    ∀ (c : Channels) (v : CarrierRepresentation.V),
      axis c = carrierAxis v → positiveSign c = positive v →
        hyper c = if wall c then bl v else bl v + 2 * t3 v := by
  decide +kernel

/-- The electric charge: `bl/2 + t3` on both walls. -/
def electric (c : Channels) : ℚ :=
  Hypercharge.electric (decide (axis c = 0)) (positiveSign c)

/-- The packet's charge table is the carrier charge. -/
theorem packet_charge_eq (c : Channels) : hyperchargeOperator c c = (hyper c : ℂ) := by
  fin_cases c <;> norm_num [hyperchargeOperator_blocks, block, channelIndex, Matrix.kroneckerMap_apply, hyper, wall,
    axis, positiveSign, blAxis, t3Sign]

/-- The packet encoding and the EP channel encoding read the same electric charge. -/
theorem electric_transport (c : Channels) :
    PMConstants.ColourRouting.electric (PMConstants.PacketGaugeActions.channelEquiv c) =
      electric c := by
  have h : ∀ (v : PMConstants.CarrierActions.Packet) (d : Channels),
      PMConstants.CarrierActions.index v = channelIndex d →
        PMConstants.ColourRouting.electric v = electric d := by
    decide +kernel
  exact h _ c (channelEquiv_index c)

end PMElementaryParticles.CarrierChannels
