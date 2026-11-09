import PMConstants.ReferenceCharge
import PMConstants.ReferenceFrames

/-!
# One reserved cell, one reference: the weak and hypercharge refreshes share it

`ReferenceCharge` left one premise: the weak and hypercharge refreshes read against a single
reference type. It follows from the premise that already fixes `η = 171/172`.

* `reserved_single`: a mandatory in-band reference with maximal payload reserves exactly one of
  the 172 cells (the argument of `ReferenceFrames.optimal_172_overhead`).
* `ReferenceLayout`: each of the weak and hypercharge refreshes reads against a reference type,
  and distinct reference types occupy distinct reserved cells.
* `shared`: then both refreshes use the same reference type.
* `responsive_iff`: a type that responds to both refreshes is `Q` or `L`.
* `reference_selected`: the E8 part of the selection — the shared reference responds to both
  refreshes, hence is `Q` or `L`, and `L` gives the manuscript `s = 1849/8295`.

The measured selection (a quark reference puts the W mass more than `2400σ` below the direct
average, so the shared reference is the lepton doublet) lives in
`tools/e8p/E8PConstants/ReadoutPulls.lean` (`quark_w_window`, `quark_reference_excluded`,
`reference_selected_wmass`). No colour-invariance premise is needed.
* `colour_not_reserved`: if the colour refresh also read against the single reserved reference,
  that type would need colour response as well, which only `Q` has, and `Q` is excluded. So the
  colour refresh's reference is not the reserved cell, consistent with its payload-weighted
  ledger `12η`.

Premises: the in-band reference and maximal payload of `ResourceSelection` (already used for
`η`), one reserved cell per distinct reference type, and that the weak and hypercharge refreshes
both read against a reserved reference with nonzero response.
-/

noncomputable section
namespace PMConstants.SharedReference
open PMConstants Finset GaugeReadoutWeights RequirementTable ReferenceCharge

/-- **Maximal payload reserves exactly one cell.** -/
theorem reserved_single (R : Finset (Fin 172)) (hR : R.Nonempty)
    (hopt : ∀ S : Finset (Fin 172), S.Nonempty → (univ \ S).card ≤ (univ \ R).card) :
    R.card = 1 := by
  have hmax := hopt {0} (by simp)
  have hsing : (univ \ ({0} : Finset (Fin 172))).card = 171 := by
    rw [ReferenceFrames.payload_count]; simp
  rw [hsing, ReferenceFrames.payload_count] at hmax
  have hpos := hR.card_pos
  have hle : R.card ≤ 172 := by simpa using card_le_univ R
  omega

/-- Reference layout for the two refreshes (`0` weak, `1` hypercharge). -/
structure ReferenceLayout where
  R : Finset (Fin 172)
  nonempty : R.Nonempty
  maximal : ∀ S : Finset (Fin 172), S.Nonempty → (univ \ S).card ≤ (univ \ R).card
  refOf : Fin 2 → Ty
  cell : Ty → Fin 172
  cell_inj : Function.Injective cell
  cell_mem : ∀ i, cell (refOf i) ∈ R

/-- **The weak and hypercharge refreshes share one reference type.** -/
theorem shared (L : ReferenceLayout) : L.refOf 0 = L.refOf 1 := by
  have h1 := reserved_single L.R L.nonempty L.maximal
  exact L.cell_inj (card_le_one.mp h1.le _ (L.cell_mem 0) _ (L.cell_mem 1))

/-- The types that respond to both refreshes. -/
theorem responsive_iff (t : Ty) :
    (0 < weakIndex (ref t) ∧ 0 < hyperIndex (ref t)) ↔ t = .Q ∨ t = .L := by
  cases t <;> norm_num [weakIndex, hyperIndex, ref]

/-- W mass for the quark-doublet reference. -/
def quarkWMass (mZ : ℝ) : ℝ := mZ * Real.sqrt (1 - 16641 / 23087)

/-- **The E8 part of the shared-reference selection.** Given a layout whose shared reference
responds to both refreshes, it is `Q` or `L`, and `L` gives the manuscript mixing. The measured
exclusion of `Q` is `tools/e8p/E8PConstants/ReadoutPulls.lean`. -/
theorem reference_selected (L : ReferenceLayout)
    (hresp : 0 < weakIndex (ref (L.refOf 0)) ∧ 0 < hyperIndex (ref (L.refOf 0))) :
    L.refOf 0 = L.refOf 1 ∧ (L.refOf 0 = .Q ∨ L.refOf 0 = .L) ∧
      refMixing (weakIndex (ref .L)) (hyperIndex (ref .L)) = clockRatio :=
  ⟨shared L, (responsive_iff _).mp hresp, lepton_reference_mixing⟩

/-- **Colour cannot share the reserved reference.** A type responding to all three refreshes is
`Q`, the excluded case. -/
theorem colour_not_reserved (t : Ty) :
    (0 < weakIndex (ref t) ∧ 0 < hyperIndex (ref t) ∧ 0 < colourIndex (ref t)) ↔ t = .Q := by
  cases t <;> norm_num [weakIndex, hyperIndex, colourIndex, ref]

/-- Cells for the six types, with the lepton doublet on cell `0`. -/
def witnessCell : Ty → Fin 172
  | .L => 0 | .Q => 1 | .u => 2 | .d => 3 | .e => 4 | .n => 5

/-- The premises are satisfiable: one reserved cell, both refreshes on the lepton doublet. -/
def witness : ReferenceLayout where
  R := {0}
  nonempty := ⟨0, by simp⟩
  maximal := fun S hS => by
    rw [ReferenceFrames.payload_count, ReferenceFrames.payload_count]
    have := hS.card_pos
    simp only [card_singleton]; omega
  refOf := fun _ => .L
  cell := witnessCell
  cell_inj := by intro a b h; cases a <;> cases b <;> simp_all [witnessCell]
  cell_mem := fun _ => by simp [witnessCell]

end PMConstants.SharedReference
