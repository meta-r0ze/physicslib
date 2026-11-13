import PMConstants.SharedReference
import PMConstants.ColourChannels
import PMConstants.MinimalRefresh

/-!
# Colour reads the payload: the ledger `12η`

`ColourChannels` reads the colour ledger as the payload of the coloured channels,
`L₃ = 12η`, and lists as its remaining premise that colour links maintain the payload rather
than the reference. The single-reference result supplies that.

* `colour_reference_in_payload`: in a layout whose single reserved cell carries the lepton-doublet
  reference (selected in `SharedReference.reference_selected`), a reference that responds to
  colour cannot sit in the reserved cell, since `L` has no colour response. It lies in the
  payload.
* `payload_weight`: each payload cell carries the payload fraction `η = 171/172`, the same
  `ReferenceFrames.optimal_172_overhead` that fixes `η`.
* `colour_ledger_minimal`: colour's required resources are the channels it acts on, the twelve
  coloured ones (`coloured_card`). Each is a payload resource of weight `η`, so the
  Economy-minimal admissible refresh cost (`MinimalRefresh.minimal_is_ledger`) is exactly
  `12η = colourLedger`.
* `strong_from_payload`: hence `0.11799 < α N_sys/L₃ < 0.11800`
  (`ColourChannels.strong_from_channels`).

The step "colour maintains the payload, not the reference" is now a consequence.

* `coloured_eq_bulk`, `coloured_iff_triplet`: the twelve channels are exactly the requirement
  table's colour column (`ResourceLedger.colouredSet`), which `RequirementTable.colour_column`
  derives from the representation: a channel routes through the colour bulk exactly when its type
  is a colour triplet. With `MinimalRefresh` (Conservation: every acted-on channel is refreshed;
  Economy: nothing else), colour's required resources are the channels it acts on, derived.

The coupling's read scale is derived separately (`ReadScale.colour_exact_read`).
-/

noncomputable section
namespace PMConstants.ColourReference
open PMConstants Finset GaugeReadoutWeights RequirementTable ReferenceCharge

/-- A reference layout whose shared electroweak reference is the lepton doublet, with a colour
reference added. -/
structure ColourLayout extends SharedReference.ReferenceLayout where
  sharedIsLepton : refOf 0 = .L
  colourRef : Ty
  colourResponds : 0 < colourIndex (ref colourRef)

/-- **Colour's reference is not the reserved cell.** -/
theorem colour_reference_in_payload (C : ColourLayout) : C.cell C.colourRef ∉ C.R := by
  intro hc
  have h1 := SharedReference.reserved_single C.R C.nonempty C.maximal
  have heq := card_le_one.mp h1.le _ hc _ (C.cell_mem 0)
  have ht := C.cell_inj heq
  have hcol := C.colourResponds
  rw [ht, C.sharedIsLepton, lepton_reference_no_colour] at hcol
  exact lt_irrefl _ hcol

/-- Each payload cell carries the payload fraction `η`. -/
theorem payload_weight (C : ColourLayout) :
    ((univ \ C.R).card : ℝ) / 172 = overhead :=
  ReferenceFrames.optimal_172_overhead C.R C.nonempty C.maximal

/-- The coloured channels among the sixteen. -/
def colouredChannels : Finset (Fin 16) :=
  univ.filter fun i => ty i = .Q ∨ ty i = .u ∨ ty i = .d

theorem coloured_card : colouredChannels.card = 12 := by decide

/-- **The colour ledger is the Economy-minimal refresh cost of the coloured payload.** -/
theorem colour_ledger_minimal (C : ColourLayout) :
    IsLeast {c | ∃ L, MinimalRefresh.admissible colouredChannels L ∧
        MinimalRefresh.cost (fun _ : Fin 16 => ((univ \ C.R).card : ℝ) / 172) L = c}
      ColourChannels.colourLedger := by
  have h := MinimalRefresh.minimal_is_ledger (fun _ : Fin 16 => ((univ \ C.R).card : ℝ) / 172)
    (fun _ => by positivity) colouredChannels
  have hs : (∑ _r ∈ colouredChannels, ((univ \ C.R).card : ℝ) / 172) =
      ColourChannels.colourLedger := by
    rw [sum_const, coloured_card, payload_weight C, nsmul_eq_mul, ColourChannels.colourLedger]
    norm_num
  rwa [hs] at h

/-- The strong coupling read on the coloured payload. -/
theorem strong_from_payload :
    (0.11799 : ℝ) < CertifiedConstants.α * footprint / ColourChannels.colourLedger ∧
      CertifiedConstants.α * footprint / ColourChannels.colourLedger < 0.11800 :=
  ColourChannels.strong_from_channels

/-- The premises are satisfiable: the `SharedReference` witness with a quark colour reference. -/
def witness : ColourLayout where
  toReferenceLayout := SharedReference.witness
  sharedIsLepton := rfl
  colourRef := .Q
  colourResponds := by norm_num [colourIndex, ref]

/-- **Colour's channels are the requirement table's colour column.** -/
theorem coloured_eq_bulk : colouredChannels = ResourceLedger.colouredSet := by decide

/-- **A channel is one of colour's required resources exactly when its type is a triplet.** -/
theorem coloured_iff_triplet (i : Fin 16) :
    i ∈ colouredChannels ↔ colourDim (ty i) = 3 := by
  rw [coloured_eq_bulk, ResourceLedger.colouredSet, mem_filter, ← colour_column]
  simp

end PMConstants.ColourReference
