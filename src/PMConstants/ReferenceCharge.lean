import PMConstants.GeneratorNormalization

/-!
# The common reference carrier fixes the charge-unit normalization

`GeneratorNormalization` showed that the selected stiffness is counted in charge units, not by
the packet trace form. This module derives that from where a refresh's response is read.

A refresh's stiffness is the comparison response of its reference carrier. For a reference
prepared on one carrier type `t`, the response indices are those of the type weight concentrated
on `t` (`GaugeReadoutWeights`, per-carrier weight one): weak `I_W` and hypercharge `I_Y` are the
type's summed squared charges `T₃²` and `(Y/2)²` (`reference_indices`).

* `equal_response_iff`: weak and hypercharge refreshes have equal, nonzero response on a common
  reference type exactly when that type is the lepton doublet `L`, the only multiplet with
  `|T₃| = |Y/2| = 1/2`. The quark doublet gives ratio `9`; `u`, `d`, `e` have no weak response and
  `n` none at all.
* `lepton_reference_mixing`: with the lepton-doublet reference, the ledgers enter with equal
  indices and the weak fraction is the manuscript value `1849/8295`, the charge-unit result. On
  `L` the conserved charge `Q = T₃ + Y/2` takes the values `0` and `−1` (neutrino, electron).
* `quark_reference_mixing`: a quark-doublet reference would give `s = 16641/23087 ≈ 0.721`.
* `lepton_reference_no_colour`: the lepton doublet carries no colour, so the colour refresh
  needs its own reference, consistent with the separate colour ledger `12η`.

* `shared_colourless_reference_iff`: a reference type that responds to both refreshes and is
  untouched by colour actions is exactly `L`. So "the reference is on the lepton axis" follows
  from requiring that the shared reference persist under the other sector's actions.

Premises: weak and hypercharge refreshes share one reference carrier type, and colour actions
do not change it. The lepton axis is the one `CarrierRepresentation` reads as the temporal axis
the clock SU(2) refreshes.
-/

noncomputable section
namespace PMConstants.ReferenceCharge
open PMConstants GaugeReadoutWeights RequirementTable

/-- A reference prepared on carrier type `t` (per-carrier weight one on that type). -/
def ref (t : Ty) : Ty → ℝ := fun s => if s = t then 1 else 0

/-- The reference indices of each type: summed `T₃²` and `(Y/2)²` over its carriers. -/
theorem reference_indices :
    (weakIndex (ref .Q), hyperIndex (ref .Q)) = (3 / 2, 1 / 6) ∧
      (weakIndex (ref .u), hyperIndex (ref .u)) = (0, 4 / 3) ∧
      (weakIndex (ref .d), hyperIndex (ref .d)) = (0, 1 / 3) ∧
      (weakIndex (ref .L), hyperIndex (ref .L)) = (1 / 2, 1 / 2) ∧
      (weakIndex (ref .e), hyperIndex (ref .e)) = (0, 1) ∧
      (weakIndex (ref .n), hyperIndex (ref .n)) = (0, 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [weakIndex, hyperIndex, ref]

/-- **Equal weak and hypercharge response on a common reference type holds only for `L`.** -/
theorem equal_response_iff (t : Ty) :
    (0 < weakIndex (ref t) ∧ weakIndex (ref t) = hyperIndex (ref t)) ↔ t = .L := by
  cases t <;> norm_num [weakIndex, hyperIndex, ref]

/-- Weak fraction with reference indices `I_W, I_Y` multiplying the ledgers. -/
def refMixing (IW IY : ℝ) : ℝ := IW * 43 / (IW * 43 + IY * (footprint - 43))

/-- **The lepton-doublet reference gives the manuscript value.** -/
theorem lepton_reference_mixing :
    refMixing (weakIndex (ref .L)) (hyperIndex (ref .L)) = clockRatio := by
  norm_num [refMixing, weakIndex, hyperIndex, ref, clockRatio, footprint, overhead]

/-- A quark-doublet reference instead. -/
theorem quark_reference_mixing :
    refMixing (weakIndex (ref .Q)) (hyperIndex (ref .Q)) = 16641 / 23087 := by
  norm_num [refMixing, weakIndex, hyperIndex, ref, footprint, overhead]

/-- The lepton doublet carries no colour. -/
theorem lepton_reference_no_colour : colourIndex (ref .L) = 0 := by
  norm_num [colourIndex, ref]

/-- The uniform packet, for comparison, gives the raw value. -/
theorem uniform_reference_mixing :
    refMixing (weakIndex ReadoutAccounting.selectedWeights)
      (hyperIndex ReadoutAccounting.selectedWeights) = 5547 / 37777 := by
  norm_num [refMixing, weakIndex, hyperIndex, ReadoutAccounting.selectedWeights, footprint,
    overhead]

/-- **A shared, colour-invariant reference is the lepton doublet.** A carrier type that responds
to both the weak and the hypercharge refresh and is untouched by colour actions (zero colour
index) is exactly `L`; equal response then follows (`equal_response_iff`). -/
theorem shared_colourless_reference_iff (t : Ty) :
    (0 < weakIndex (ref t) ∧ 0 < hyperIndex (ref t) ∧ colourIndex (ref t) = 0) ↔ t = .L := by
  cases t <;> norm_num [weakIndex, hyperIndex, colourIndex, ref]

end PMConstants.ReferenceCharge
