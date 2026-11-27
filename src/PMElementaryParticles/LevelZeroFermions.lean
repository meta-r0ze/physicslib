import PMElementaryParticles.NestedFermion
import PMSubstrate.SpeciesFootprints
import PMElementaryParticles.ProtocolInventory
import Mathlib.Data.Finset.Sum

/-!
# Level-0 fermions: roles before ledger assignments

No parent, promotion or fitted correction is introduced. The comparison labels
are supplied by ProtocolInventory.baseProtocol and CarrierChannels, not by mass.
No generation key is selected. The constructed programs satisfy the CURRENT
ring Pillars; native StrongMap readability and complete joint-state return are
separate open constructions. No new existence premise is adopted here.

| Pillar | Charged-lepton role | Up role | Down role | Source/status |
| --- | --- | --- | --- | --- |
| Capacity | Room and service for the one-packet trace. | Room and service for the coloured packet. | The same for its weak partner. | ProgramWitness.Capacity bounds traffic. It does not assign more units to a colour axis. Extra physical room is open. |
| Map | Retain channel/reference and generation. | Also retain the colour and weak label. | Also retain colour and the partner label. | MapRecord/MapClass hold; RecordEncoding.packet_encoding_injective preserves channels with metadata. StrongMap's native reader/correction remains open. Metadata states are not additional reversals. |
| Protocol | Reversible tick. | Reversible tick and existing colour/weak label actions. | The weak partner uses the same ring machinery. | RingReceiver.tick_bijective; PacketGaugeActions.weak_label_matches. No extra registration price follows. |
| Governor | Leave a non-firing site. | Restrict the same admitted ring operations. | The same restriction. | ProgramWitness.Governor. The restriction is certified, not a new signed mass credit. |
| Toll | Register when the retained bit differs. | The same requirement. | The same requirement. | ReversalEvents.registrations_eq_reversals; quiet_program_total. One event at unit price is the whole certified account, not baseline tollTerm. |
| Margin | A differing bit ring is not saturated. | The same reserve condition. | The same reserve condition. | NestedFermion.one_ring_margin_ceiling. No separate baseline marginTerm charge follows. Physical robustness of the isolated excitation is open. |

A held unit in THIS reading is a tagged occurrence of stream reversal: which
bit ring, and which tick of its base-period trace. It is not a carrier label,
coordinate direction, cell, or every tick of a quiet walk. The set below is
connected to the existing reversal count and footprint; it defines no second
mass reading. A singleton certifies the primitive event account. It does not
identify the physical particle with that account including all possible costs.

For the electron-labelled witness, all six ring pillars hold, but the only
charged operation in its account is the Toll registration. The other footprint
fields are zero by definition of that account. Their PHYSICAL pillar charges
are open, not proved zero. The same unit account works on up/down channels;
there is no theorem here that the quarks' complete physical costs equal one.

Paper V 6_impedance_matching.tex proposes localized quark anchors and a global
lepton architecture. That role proposal does not count held coordinate units,
prove a reserved-address overhead, or price a weak flip. Its approximate
mass/impedance identification is not imported as a premise or a mass law.
-/

noncomputable section
namespace PMElementaryParticles.LevelZeroFermions
open PMConstants.PacketGaugeActions
open PMElementaryParticles.EPSpine PMElementaryParticles.RetainedMap
open PMElementaryParticles.ReversalEvents PMElementaryParticles.ProtocolInventory
open PMSubstrate.E8Values PMSubstrate.OccupancyCost

/-- Times of reversals in one identified bit-ring trace. -/
def lineEvents (p : Program) (b : Fin 2) : Finset ℕ :=
  (Finset.range Delta).filter fun t =>
    (step true (p.firing b) (trace true (p.firing b) p.x0 t)).2 ≠
      (trace true (p.firing b) p.x0 t).2

/-- Left/right tags are bit rings 0/1; the payload is the tick, not a second particle. -/
def heldEvents (p : Program) : Finset (ℕ ⊕ ℕ) := (lineEvents p 0).disjSum (lineEvents p 1)

theorem line_events_card (p : Program) (b : Fin 2) :
    (lineEvents p b).card = count true (p.firing b) p.x0 Delta := by
  rw [lineEvents, Finset.card_filter]
  rfl

theorem held_events_card (p : Program) : (heldEvents p).card = total p := by
  rw [heldEvents,Finset.card_disjSum,line_events_card,line_events_card]
  rfl

theorem held_event_time (p : Program) (u : ℕ ⊕ ℕ) (hu : u ∈ heldEvents p) :
    u.elim id id < Delta := by
  cases u with
  | inl t => exact Finset.mem_range.mp (Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp hu)).1
  | inr t => exact Finset.mem_range.mp (Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hu)).1

theorem footprint_counts_held_events (p : Program) :
    footprint p = { events := (heldEvents p).card } := by
  rw [held_events_card]
  rfl

theorem cost_counts_held_events (p : Program) : cost (footprint p) = ((heldEvents p).card : ℝ) := by
  rw [held_events_card,footprint_cost]

theorem quiet_held_event_unique (g : Generation) (c : Channels) :
    ∃ u, heldEvents (quietProgram g c) = {u} := by
  apply Finset.card_eq_one.mp
  rw [held_events_card,quiet_program_total]

/-- An explicit OPEN residual for all roles not priced by the unit account.
No value or sign is assigned to it, and no complete species prediction follows. -/
theorem unit_with_open_residual (g : Generation) (c : Channels) (unpriced : ℝ) :
    cost ((footprint (quietProgram g c)).add { residual := unpriced }) = 1+unpriced := by
  rw [cost_add,quiet_program_cost]
  have hr : cost { residual := unpriced } = unpriced := by simp [cost]
  rw [hr]

/-- Complete list; wall/chirality is retained, generation is not chosen. -/
theorem electron_channels :
    (Finset.univ.filter fun c : Channels => baseProtocol c = some .electron) =
      {Sum.inr (Sum.inr (Sum.inl 1)), Sum.inr (Sum.inr (Sum.inr 1))} := by decide +kernel

theorem electron_channel_identity : ∀ c : Channels,
    baseProtocol c = some .electron ↔
      CarrierChannels.axis c = 0 ∧ CarrierChannels.electric c = -1 := by decide +kernel

theorem electron_classes : ∀ c : Channels, baseProtocol c = some .electron →
    (ProgramClasses.classOf c = 3 ∨ ProgramClasses.classOf c = 5) := by decide +kernel

theorem up_down_channels :
    (∀ c : Channels, baseProtocol c = some .up ↔
      ∃ a : Fin 3, c = Sum.inl (a,0) ∨ c = Sum.inr (Sum.inl (a,0))) ∧
    (∀ c : Channels, baseProtocol c = some .down ↔
      ∃ a : Fin 3, c = Sum.inl (a,1) ∨ c = Sum.inr (Sum.inl (a,1))) := by decide +kernel

/-- The active quark doublet is class 0; the two singlets are distinct classes. -/
theorem quark_classes :
    (∀ c : Channels, baseProtocol c = some .up →
      ProgramClasses.classOf c = if CarrierChannels.wall c then 0 else 1) ∧
    (∀ c : Channels, baseProtocol c = some .down →
      ProgramClasses.classOf c = if CarrierChannels.wall c then 0 else 2) := by decide +kernel

theorem charged_channels_visible : ∀ c : Channels,
    (baseProtocol c = some .electron ∨ baseProtocol c = some .up ∨ baseProtocol c = some .down) →
      ProgramClasses.classOf c ≠ 4 := by decide +kernel

/-- Existence is proved for the current ring contract, not postulated for an isolated particle. -/
theorem labelled_unit (g : Generation) (c : Channels)
    (hc : baseProtocol c = some .electron ∨ baseProtocol c = some .up ∨ baseProtocol c = some .down) :
    (quietProgram g c).Pillars ∧
      footprint (quietProgram g c) = { events := 1 } ∧
      cost (footprint (quietProgram g c)) = 1 ∧ (heldEvents (quietProgram g c)).card = 1 :=
  ⟨quiet_program_pillars g c (charged_channels_visible c hc),quiet_footprint_one g c,
    quiet_program_cost g c,by rw [held_events_card,quiet_program_total]⟩

/-- This does not assign physical zero prices to the other roles. -/
theorem unit_account_extra_fields (g : Generation) (c : Channels) :
    let f := footprint (quietProgram g c)
    f.cells = 0 ∧ f.capacity = 0 ∧ f.map = 0 ∧ f.protocol = 0 ∧
      f.governor = 0 ∧ f.toll = 0 ∧ f.margin = 0 ∧ f.residual = 0 := by
  rw [quiet_footprint_one]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem weak_flip_up_down : ∀ c : Channels,
    baseProtocol c = some .up → CarrierChannels.wall c = true →
      baseProtocol (flipWeak c) = some .down := by decide +kernel

theorem weak_singlets_fixed : ∀ c : Channels, CarrierChannels.wall c = false →
    flipWeak c = c := by decide +kernel

/-- These are separately prepared witnesses: leastRef and firing fields are
chosen again for the image label. This does not price a weak transition at a
fixed apparatus/reference. -/
theorem weak_flip_unit_account (g : Generation) (c : Channels) :
    footprint (quietProgram g (flipWeak c)) = footprint (quietProgram g c) := by
  rw [quiet_footprint_one,quiet_footprint_one]

/-! ## Coordinate counts and the reserved address

The following count is a background frame, not a quark's held-event set.
One excluded address gives RM-1 usable addresses and the fraction overhead.
The same frame exists for leptons. No theorem couples the packet's colour
flag to paying its reciprocal, or identifies D coordinate axes with D reversals.
-/

theorem frame_address_count : Fintype.card (Fin D × Fin Delta) = RM := by norm_num

theorem reserved_address_count (o : Fin RM) : (Finset.univ.erase o).card = RM-1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ o),Finset.card_univ,Fintype.card_fin]

theorem reserved_address_fraction (o : Fin RM) :
    (((Finset.univ.erase o).card : ℕ) : ℝ)/(RM : ℝ) = overhead := by
  rw [reserved_address_count]
  rfl

/-- If a reference unit changes, every numerator in that same unit rescales.
No electron correction is chosen, and no muon-specific theorem is added. -/
theorem reference_unit_change (x delta : ℝ) (h : 1+delta ≠ 0) :
    x/(1+delta)-x = -(x*delta)/(1+delta) := by
  field_simp
  ring

/-! ## Ledger comparison and what remains open

The declared up D/eta and down (D+sigma)/eta are not consequences of labelled_unit:
that theorem gives exactly one reversal for either label. The frame count above
certifies the usable-address fraction, not the quark-only reciprocal charge.
The weak flip changes up to down on the active wall and fixes the other-wall
singlets. The separately prepared unit accounts agree, with leastRef chosen
again for each label. That equality does not price a fixed-reference weak
transition and supplies no derivation of the sigma increment. The full quark costs remain the independently
supplied ledgers; the one-event account is not a competing quark mass prediction.

The held-event kind for Muon is now concrete on the base trace. Its actual child
set, resource ownership, parent period and sigma multiplicity remain open.
No count of missing muon slots follows from the number of summands. See
LedgerPillars for the price/role classification and the six-slot test.
-/

open PMSubstrate.SpeciesFootprints

/-- These are supplied-ledger identities, not prices derived from the weak flip. -/
theorem declared_point_ledger_difference :
    Quark.up = (D : ℝ)/Quark.η ∧ Quark.down-Quark.up = (sigma : ℝ)/Quark.η := by
  constructor
  · exact Quark.up_ledger
  · rw [Quark.down_ledger,Quark.up_ledger]
    unfold Quark.anchorPoint Quark.symWeight
    ring

/-- The declared point footprints have four events, not the singleton ring event.
This comparison changes neither footprint and derives no physical quark mass. -/
theorem unit_is_not_declared_quark_footprint (g : Generation) (c : Channels) :
    footprint (quietProgram g c) ≠ Quark.upFootprint ∧
      footprint (quietProgram g c) ≠ Quark.downFootprint := by
  have hu := SpacetimeProgram.declared_event_counts.2.2.1
  have hd := SpacetimeProgram.declared_event_counts.2.2.2.1
  rw [quiet_footprint_one]
  constructor
  · intro h; have he := congrArg Footprint.events h
    change 1 = Quark.upFootprint.events at he
    omega
  · intro h; have he := congrArg Footprint.events h
    change 1 = Quark.downFootprint.events at he
    omega

end PMElementaryParticles.LevelZeroFermions
