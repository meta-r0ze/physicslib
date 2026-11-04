import PMConstants.SharedReference
import PMConstants.PrimitiveReadoutSymmetry

/-!
# What the lepton-doublet reference supplies elsewhere

`SharedReference` selected the lepton doublet `L` as the shared electroweak reference. Two open
items in the constants map are consequences.

**The readout asymmetry.** `PrimitiveReadoutSymmetry.current_readouts_break_root` proved that
reproducing the current weak and strong readouts requires breaking invariance under the paired
lepton/colour reflection, and the constants map listed that asymmetry as needed. The reference
supplies it: the lepton-doublet reference is not invariant under that reflection
(`lepton_reference_breaks_root`), because the reflection exchanges the lepton axis with a colour
axis and so moves `L` carriers to `Q` carriers. The asymmetry is the reference itself, not an
extra readout rule.

**The electron as the anchor.** The VEV formula is read in units of the single repair that
maintains the electron (`VevPremises.handoff_is_footprint_repair`), and "why electron
maintenance supplies the anchor" was open. On the reference type the conserved charge
`Q = T₃ + Y/2` takes the values `0` and `−1` (`reference_charges`): of the reference's two
carriers, exactly one is read by the unbroken charge, and it is the electron
(`electron_unique_charged_reference`). So the anchor is the reference's electrically readable
carrier. The remaining VEV premise becomes: the scale is anchored on maintaining the reference,
at one repair.
-/

noncomputable section
namespace PMConstants.ReferenceAnchor
open PMConstants GaugeReadoutWeights RequirementTable ReferenceCharge PrimitiveReadoutSymmetry
open GeneratorNormalization PacketTraceForm

/-- **The lepton-doublet reference breaks the paired reflection.** -/
theorem lepton_reference_breaks_root :
    ¬ ∀ v : CarrierActions.Packet, CarrierReadoutOrbits.typed (ref .L) (root v) = CarrierReadoutOrbits.typed (ref .L) v := by
  intro h
  have := ((root_invariant_iff (ref .L)).mp h).1
  norm_num [ref] at this

/-- The two carriers of the reference type (the left-handed lepton block). -/
def lepton (s : Fin 2) : PacketGaugeActions.Channels := .inr (.inr (.inl s))

theorem lepton_type (s : Fin 2) : channelType (lepton s) = .L := rfl

/-- **The conserved charge on the reference type is `0` and `−1`.** -/
theorem reference_charges :
    (t3 + hyperGen) (lepton 0) (lepton 0) = 0 ∧ (t3 + hyperGen) (lepton 1) (lepton 1) = -1 := by
  constructor <;>
    norm_num [t3, hyperGen, lepton, weakGen, PacketGaugeActions.charge, PacketGaugeActions.block,
      Matrix.add_apply]

/-- **Exactly one reference carrier is read by the unbroken charge: the electron.** -/
theorem electron_unique_charged_reference (s : Fin 2) :
    (t3 + hyperGen) (lepton s) (lepton s) ≠ 0 ↔ s = 1 := by
  fin_cases s
  · simp [reference_charges.1]
  · simp [reference_charges.2]

end PMConstants.ReferenceAnchor
