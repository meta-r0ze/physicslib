import PMElementaryParticles.LevelZeroFermions
import PMElementaryParticles.ChannelVectors
import PMConstants.SharedReference
import PMConstants.ColourReference
import PMConstants.ReferenceAnchor
import Mathlib.InformationTheory.Hamming

/-!
# Retained channel information, without a selected reference or physical bit chart

The coarse record ALREADY separates lepton/nonlepton and weak sign. It loses
wall and the individual colour axis; generation is separate. Rule 2 requires
recoverability, not a second stored copy of every function of a channel.

The requested tuple (class, axis, sign, internal coordinate) is redundant:
channelCoord alone is injective. The channelCode's wall and signed-axis label
suffice. word is its ordinary four-bit expansion, not a new physical readout.
It is length-minimal on the fourteen point channels, and each bit is essential.
Class and channel-vector content can be reconstructed, not charged again.
For a fixed generation the generation-specific internal channel content is
also determined. This is not a native StrongMap decoder for arbitrary Program
states: reference p also contains the packet's independent internal content.

Hamming cost depends on the actual encoding. The equally short Gray chart
below retains the same information and changes a distance. Nothing here
selects either chart physically. All numerical distances are conditional on
word and the once-per-bit comparison model in MapMaintenance.

The coarse lepton/colour records do not fix a wall or full colour axis.
Their completion sets below retain ALL compatible basis labels. SharedReference
and ColourReference specify type weights, not one channel; type completions
are sets of basis channels, not a replacement for that weighted reference.
The colour-symmetric vector (0,1,1,1) is not a channelCoord, so it has no word
without a further readout. ReferenceAnchor supplies two actual lepton channels,
not a choice between them. No reference generation is supplied by these APIs.
-/

noncomputable section
namespace PMElementaryParticles.ChannelRecord
open PMConstants.PacketGaugeActions
open PMElementaryParticles.ControlledGluedRegister
open PMElementaryParticles.HeavyFlipControl
open PMElementaryParticles.ProtocolInventory
open PMElementaryParticles.EPSpine

/-- Ordinary binary expansion of the EXISTING channelCode: wall, axis high/low, sign. -/
def word (c : Channels) : Fin 4 → Bool :=
  ![(channelCode c).1, decide ((labelIndex c).val / 4 = 1),
    decide (((labelIndex c).val / 2) % 2 = 1), RecordCoordinates.signBit c]

theorem word_injective : Function.Injective word := by decide +kernel

def pointChannels : Finset Channels := Finset.univ.filter fun c =>
  baseProtocol c = some .electron ∨ baseProtocol c = some .up ∨ baseProtocol c = some .down

theorem point_channels_card : pointChannels.card = 14 := by decide +kernel

/-- Fieldwise essential bits, on the requested channel set. -/
theorem every_bit_essential : ∀ i : Fin 4, ∃ c ∈ pointChannels, ∃ d ∈ pointChannels,
    c ≠ d ∧ (fun j => if j = i then false else word c j) =
      (fun j => if j = i then false else word d j) := by decide +kernel

/-- No injective binary encoding of these fourteen channels uses fewer than four bits. -/
theorem bit_length_minimal (n : ℕ) (e : {c // c ∈ pointChannels} → (Fin n → Bool))
    (he : Function.Injective e) : 4 ≤ n := by
  have hc := Fintype.card_le_of_injective e he
  have hp : Fintype.card {c // c ∈ pointChannels} = 14 := by
    simpa only [Fintype.card_coe] using point_channels_card
  rw [hp] at hc
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hc
  by_contra h
  have hn : n ≤ 3 := by omega
  interval_cases n <;> norm_num at hc

/-- The decorated fields are reconstructed from one channel code; no extra independent data. -/
theorem word_determines_semantics (c d : Channels) (h : word c = word d) :
    ProgramClasses.classOf c = ProgramClasses.classOf d ∧
      CarrierChannels.axis c = CarrierChannels.axis d ∧
      CarrierChannels.positiveSign c = CarrierChannels.positiveSign d ∧
      ChannelVectors.channelCoord c = ChannelVectors.channelCoord d := by
  cases word_injective h
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem word_determines_internal (g : Fin 3) (c d : Channels) (h : word c = word d) :
    EPLabel.internalContent (EPLabelGen.channelE8Gen g c) =
      EPLabel.internalContent (EPLabelGen.channelE8Gen g d) := by rw [word_injective h]

/-- Dropping class from the requested decorated record does NOT merge channels. -/
theorem class_field_redundant : Function.Injective fun c : Channels =>
    (CarrierChannels.axis c, CarrierChannels.positiveSign c, ChannelVectors.channelCoord c) := by
  intro c d h
  exact ChannelVectors.channelCoord_injective (congrArg (fun p => p.2.2) h)

/-- Dropping internal coordinates also preserves all channel information. -/
theorem internal_field_redundant : Function.Injective fun c : Channels =>
    (ProgramClasses.classOf c, CarrierChannels.axis c, CarrierChannels.positiveSign c) := by
  decide +kernel

theorem coarse_separates_species : ∀ c d : Channels, c ∈ pointChannels → d ∈ pointChannels →
    labelRecord c = labelRecord d → baseProtocol c = baseProtocol d := by decide +kernel

/-- Same information and bit length, a different metric: Rule 2 does not select a chart. -/
def grayWord (c : Channels) : Fin 4 → Bool :=
  ![word c 0, word c 1, xor (word c 1) (word c 2), word c 3]

theorem gray_injective : Function.Injective grayWord := by decide +kernel

theorem encoding_changes_distance :
    let e : Channels := .inr (.inr (.inl 1))
    let d : Channels := .inl (2,1)
    hammingDist (word e) (word d) = 2 ∧ hammingDist (grayWord e) (grayWord d) = 1 := by
  decide +kernel

/-- A fixed reference word cannot give both adjacent wall versions of the
charged lepton unit distance. This concerns this bit chart, not physical mass. -/
theorem no_fixed_word_unit_for_both_walls : ∀ r : Fin 4 → Bool,
    ¬ (hammingDist (word (.inr (.inr (.inl 1)))) r = 1 ∧
       hammingDist (word (.inr (.inr (.inr 1)))) r = 1) := by decide +kernel

/-- All lifts of a two-bit reference, without choosing the missing coordinates. -/
def coarseCompletions (r : Record) : Finset Channels := Finset.univ.filter fun c => labelRecord c = r

def coarseDistances (c : Channels) (colour : Bool) : Finset ℕ :=
  (coarseCompletions (IsolatedExcitation.refRecord colour)).image fun r => hammingDist (word c) (word r)

/-- Basis-support completions of a type weight; NOT a distance to the weight itself. -/
def typeDistances (c : Channels) (t : PMConstants.RequirementTable.Ty) : Finset ℕ :=
  (Finset.univ.filter fun r => PMConstants.GaugeReadoutWeights.channelType r = t).image
    fun r => hammingDist (word c) (word r)

theorem coarse_reference_lifts :
    (coarseCompletions (IsolatedExcitation.refRecord false)).card = 2 ∧
    (coarseCompletions (IsolatedExcitation.refRecord true)).card = 6 := by decide +kernel

theorem shared_reference_lifts :
    (Finset.univ.filter fun c => PMConstants.GaugeReadoutWeights.channelType c = .L).card = 2 ∧
    (Finset.univ.filter fun c => PMConstants.GaugeReadoutWeights.channelType c = .Q).card = 6 := by
  decide +kernel

/-- No channel word is supplied for the colour-coherent reference vector. -/
theorem colour_symmetric_not_channel : ∀ c : Channels,
    (fun i => (ChannelVectors.channelCoord c i : ℚ)) ≠ RecordEncoding.colourSymmetric := by
  decide +kernel

/-- Native two-component glue key, separate from the four channel bits. -/
def keyWord (g : Generation) : Fin 2 → Bool := ![decide (g.val.1 = 1), decide (g.val.2 = 1)]

def generatedWord (c : Channels) (g : Generation) : Fin 4 ⊕ Fin 2 → Bool := Sum.elim (word c) (keyWord g)

def keys : List Generation := [⟨(0,1),by decide⟩,⟨(1,0),by decide⟩,⟨(1,1),by decide⟩]

theorem key_distances : keys.map (fun g => keys.map fun h => hammingDist (keyWord g) (keyWord h)) =
    [[0,2,1],[2,0,1],[1,1,0]] := by decide +kernel

theorem generated_distance (c d : Channels) (g h : Generation) :
    hammingDist (generatedWord c g) (generatedWord d h) =
      hammingDist (word c) (word d)+hammingDist (keyWord g) (keyWord h) := by
  simp only [hammingDist,Finset.card_filter]
  rw [Fintype.sum_sum_type]
  rfl

theorem channel_distance_bound (c : Channels) (r : Fin 4 → Bool) : hammingDist (word c) r ≤ 4 := by
  simpa using (hammingDist_le_card_fintype (x := word c) (y := r))

theorem generated_distance_bound (c : Channels) (g : Generation)
    (r : Fin 4 ⊕ Fin 2 → Bool) : hammingDist (generatedWord c g) r ≤ 6 := by
  simpa using (hammingDist_le_card_fintype (x := generatedWord c g) (y := r))

/-- Summary for the report. Lists are (class, wall, coarse L/C, exact nuL/eL).
Sets are full coarse-L/C completions, then type supports Q,L,u,d,e,n. -/
def referenceProfile (c : Channels) : List ℕ × List (Finset ℕ) :=
  ([ (ProgramClasses.classOf c).val, if CarrierChannels.wall c then 1 else 0,
      IsolatedExcitation.hamming (labelRecord c) (IsolatedExcitation.refRecord false),
      IsolatedExcitation.hamming (labelRecord c) (IsolatedExcitation.refRecord true),
      hammingDist (word c) (word (PMConstants.ReferenceAnchor.lepton 0)),
      hammingDist (word c) (word (PMConstants.ReferenceAnchor.lepton 1)) ],
    [coarseDistances c false,coarseDistances c true,typeDistances c .Q,typeDistances c .L,
      typeDistances c .u,typeDistances c .d,typeDistances c .e,typeDistances c .n])

/-- All fourteen point channels exactly once, without selecting a reference. -/
def tableChannels : List Channels := [
  .inr (.inr (.inl 1)),
  .inr (.inr (.inr 1)),
  .inl (0,0),
  .inl (0,1),
  .inr (.inl (0,0)),
  .inr (.inl (0,1)),
  .inl (1,0),
  .inl (1,1),
  .inr (.inl (1,0)),
  .inr (.inl (1,1)),
  .inl (2,0),
  .inl (2,1),
  .inr (.inl (2,0)),
  .inr (.inl (2,1))]

theorem table_channels_complete : tableChannels.toFinset = pointChannels ∧ tableChannels.Nodup := by
  decide +kernel

/-- Exact finite certificate. No full reference is selected from a completion set. -/
theorem reference_table : tableChannels.map referenceProfile = [
  ([3,1,1,2,1,0],[{1,2},{2,3,4},{1,2,3},{0,1},{3,4},{2,3},{1},{2}]),
  ([5,0,1,2,2,1],[{1,2},{2,3,4},{2,3,4},{1,2},{2,3},{1,2},{0},{1}]),
  ([0,1,1,0,1,2],[{1,2},{0,1,2,3},{0,1,2,3},{1,2},{1,2,3},{2,3,4},{3},{2}]),
  ([0,1,2,1,2,1],[{2,3},{1,2,3,4},{0,1,2,3},{1,2},{2,3,4},{1,2,3},{2},{3}]),
  ([1,0,1,0,2,3],[{1,2},{0,1,2,3},{1,2,3,4},{2,3},{0,1,2},{1,2,3},{2},{1}]),
  ([2,0,2,1,3,2],[{2,3},{1,2,3,4},{1,2,3,4},{2,3},{1,2,3},{0,1,2},{1},{2}]),
  ([0,1,1,0,1,2],[{1,2},{0,1,2,3},{0,1,2,3},{1,2},{1,2,3},{2,3,4},{3},{2}]),
  ([0,1,2,1,2,1],[{2,3},{1,2,3,4},{0,1,2,3},{1,2},{2,3,4},{1,2,3},{2},{3}]),
  ([1,0,1,0,2,3],[{1,2},{0,1,2,3},{1,2,3,4},{2,3},{0,1,2},{1,2,3},{2},{1}]),
  ([2,0,2,1,3,2],[{2,3},{1,2,3,4},{1,2,3,4},{2,3},{1,2,3},{0,1,2},{1},{2}]),
  ([0,1,1,0,2,3],[{2,3},{0,1,2},{0,1,2},{2,3},{1,2},{2,3},{4},{3}]),
  ([0,1,2,1,3,2],[{3,4},{1,2,3},{0,1,2},{2,3},{2,3},{1,2},{3},{4}]),
  ([1,0,1,0,3,4],[{2,3},{0,1,2},{1,2,3},{3,4},{0,1},{1,2},{3},{2}]),
  ([2,0,2,1,4,3],[{3,4},{1,2,3},{1,2,3},{3,4},{1,2},{0,1},{2},{3}]) ] := by decide +kernel

/-- The reciprocal overhead is a separate supplied reading, not an integer comparison count. -/
theorem declared_overhead_gaps :
    PMSubstrate.SpeciesFootprints.Quark.up-(PMSubstrate.E8Values.D : ℝ) = 4/171 ∧
    PMSubstrate.SpeciesFootprints.Quark.down-
      ((PMSubstrate.E8Values.D : ℝ)+(PMSubstrate.E8Values.sigma : ℝ)) = 9/171 := by
  rw [PMSubstrate.SpeciesFootprints.Quark.up_ledger,PMSubstrate.SpeciesFootprints.Quark.down_ledger]
  norm_num [PMSubstrate.SpeciesFootprints.Quark.anchorPoint,PMSubstrate.SpeciesFootprints.Quark.symWeight,
    PMSubstrate.SpeciesFootprints.Quark.η,PMSubstrate.E8Values.overhead]

end PMElementaryParticles.ChannelRecord
