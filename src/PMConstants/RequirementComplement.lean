import PMConstants.RequirementRows

/-!
# The rest of the requirement table: complement and per-channel routing

Paper III's own wording of the table (§ the colour ledger) contains the distinction that decides
it: SU(2)'s eight channels share **one** clock, "so its ledger is the clock, 43, however many
channels use it", while each coloured channel "has its own routing". With the reference this
becomes a persistence statement about where each sector's frame is stored.

**Hypercharge is the complement.** The electroweak refreshes read the reserved reference, the
in-band marker that locates every resource of the phase (`ReferenceFrames.unique_marker`). For the
phase to persist, every one of its resources must be refreshed (Conservation), each once (Economy),
by the electroweak pair; this is the matching `1/e² = 1/g² + 1/g'²` that already gives the electric
coupling the whole footprint (`GaugeLedgers.footprint_from_rule`). Weak's frame is the shared
reference, stored once, so its refresh is confined to the reference's row (`RequirementRows`).

* `hyper_is_complement`: if every resource is refreshed by weak or hypercharge, weak refreshes the
  clock row and nothing else, then hypercharge refreshes exactly `GaugeLedgers.reqY`: the spatial
  rows, the wires and all sixteen payloads, including the sterile one.
* `hyper_ledger`: hence `129 + 5 + 16η`. The wires and the payloads, including `ν_R`, are not
  separate premises: they are what is left once weak has its row.

**Colour routes per channel.** Colour has no frame-stored reference (`ColourReference`: the reserved
cell is colourless), so there is no shared resource to refresh once; each channel's colour state can
be restored only on that channel. Conservation then requires every channel colour moves and Economy
none it fixes:
* `colour_requirement`: the channels colour moves are exactly the non-leptonic ones
  (`ReferenceMasses.colour_moves_iff`), twelve of them, and one payload refresh each costs `12η`.

The asymmetry between weak (one shared resource) and colour (one per channel) is therefore whether
the sector's frame is stored in the reference.
Premises: the electroweak pair covers the phase's resources once each; weak's refresh is confined to
the reference row; a sector without a stored reference restores each moved channel separately.
-/

noncomputable section
namespace PMConstants.RequirementComplement
open PMConstants GaugeLedgers

inductive EW | weak | hyper
  deriving DecidableEq

/-- **Hypercharge refreshes the complement of the clock row.** -/
theorem hyper_is_complement (f : Res → EW) (hclock : f .clock = .weak)
    (hconf : ∀ r, f r = .weak → r = .clock) (r : Res) : f r = .hyper ↔ r ∈ reqY := by
  constructor
  · intro h
    have hne : r ≠ .clock := by rintro rfl; rw [hclock] at h; cases h
    cases r with
    | clock => exact absurd rfl hne
    | space => simp [reqY]
    | wires => simp [reqY]
    | payload i => simp [reqY]
  · intro h
    have hne : r ≠ .clock := by
      rintro rfl
      simp [reqY] at h
    cases hf : f r with
    | weak => exact absurd (hconf r hf) hne
    | hyper => rfl

theorem hyper_ledger : ledger reqY = 129 + 5 + 16 * overhead := hyper_value

/-- **Colour's per-channel requirement.** -/
theorem colour_requirement :
    (Finset.univ.filter fun c : PacketGaugeActions.Channels =>
        ReferenceMasses.leptonic c = false).card = 12 ∧
      (12 : ℝ) * overhead = ColourChannels.colourLedger := by
  refine ⟨ReferenceMasses.colour_moved_card, ?_⟩
  norm_num [ColourChannels.colourLedger, overhead]

end PMConstants.RequirementComplement
