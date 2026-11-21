import PMElementaryParticles.RecordPortIdentification
import PersistenceMechanics.ReversibleEncoding

/-!
# Reversible Encoding on the record ledger, and the colour reference

Nested Rule 2 (`PersistenceMechanics.ReversibleEncoding`) applied to the protocol record.
The coarse description is `labelRecord` (two bits: lepton axis or not, sign). It merges
labels: six per colour record class, two per lepton class (`record_fibers`). So the record
alone is not reversible (`record_not_injective`).

* `packet_encoding_injective`: the packet's own channel code
  (`ControlledGluedRegister.channelCode`) is metadata that makes the encoding reversible.
  Rule 2 holds inside the packet; no external colour store is required.
* `metadata_lower_bound`: any reversible metadata has at least six states (the colour fibres).
* `bitToll_colour_blind`: the record comparator cannot see colour. Every record Toll is
  invariant under colour permutation (`HeavyFlipControl.record_colour`).

**The colour reference is a single-site state.** The record comparison is bit-level
(projective): it compares the lepton-axis bit and the sign bit, not individual channels. So
the colour reference record `(axis ≠ 0, +)` needs a state with no lepton-axis component and
positive colour components, not one colour axis. On the four axis coordinates (axis 0 the
lepton axis, axes 1–3 the colour axes):

* `colourSymmetric_lepton_axis`, `colourSymmetric_positive`: the state `(0,1,1,1)` has
  exactly the colour reference record;
* `colourSymmetric_invariant`: it is fixed by every permutation of the colour axes;
* `colour_axis_overlap`: a channel-resolving comparison of a colour axis with it would see
  squared overlap `1/3`. No certified comparator resolves channels, so this angle does not
  enter the record Toll.

So the colour reference does not force composites, and it does not supply a partial
comparison angle. See `LINE-AND-COMPOSITION.md`.
-/

noncomputable section
namespace PMElementaryParticles.RecordEncoding

open PMConstants.PacketGaugeActions PMElementaryParticles.HeavyFlipControl
open PersistenceMechanics.ReversibleEncoding

/-- **Fibre sizes of the record description.** -/
theorem record_fibers :
    (Finset.univ.filter fun c : Channels => labelRecord c = (false, false)).card = 6 ∧
      (Finset.univ.filter fun c : Channels => labelRecord c = (false, true)).card = 6 ∧
      (Finset.univ.filter fun c : Channels => labelRecord c = (true, true)).card = 2 ∧
      (Finset.univ.filter fun c : Channels => labelRecord c = (true, false)).card = 2 := by
  decide +kernel

theorem record_merges : ∃ c d : Channels, c ≠ d ∧ labelRecord c = labelRecord d := by
  decide +kernel

/-- **The record alone is not reversible.** -/
theorem record_not_injective : ¬ Function.Injective labelRecord := fun h => by
  obtain ⟨c, d, hne, heq⟩ := record_merges
  exact hne (h heq)

/-- **Rule 2 holds inside the packet.** The channel code is reversible metadata. -/
theorem packet_encoding_injective :
    Function.Injective (encode labelRecord ControlledGluedRegister.channelCode) :=
  (encode_injective_iff _ _).mpr fun _ _ _ hm => ControlledGluedRegister.channelCode_bijective.1 hm

/-- **At least six metadata states.** -/
theorem metadata_lower_bound (M : Type*) [Fintype M] (m : Channels → M)
    (h : Function.Injective (encode labelRecord m)) : 6 ≤ Fintype.card M := by
  have hb := fiber_card_le labelRecord m h (false, false)
  rw [record_fibers.1] at hb
  exact hb

/-- **The record comparator is colour-blind.** -/
theorem bitToll_colour_blind (ref : Bool) (a b : Fin 3) (c : Channels) :
    WireSchedule.bitToll ref (permuteColour a b c) = WireSchedule.bitToll ref c := by
  rw [IsolatedExcitation.bitToll_eq_hamming, IsolatedExcitation.bitToll_eq_hamming,
    record_colour]

/-! ## The colour reference as one site state -/

/-- Axis coordinates of a vector-class state: axis 0 is the lepton axis, 1–3 the colour axes. -/
abbrev Axes := Fin 4 → ℚ

/-- The colour-symmetric state with positive colour components. -/
def colourSymmetric : Axes := ![0, 1, 1, 1]

def axisVec (j : Fin 4) : Axes := Pi.single j 1

def dot (u v : Axes) : ℚ := ∑ i, u i * v i

theorem colourSymmetric_eq (j : Fin 4) : colourSymmetric j = if j = 0 then 0 else 1 := by
  fin_cases j <;> simp [colourSymmetric]

/-- No lepton-axis component: its axis record is "colour" with certainty. -/
theorem colourSymmetric_lepton_axis : colourSymmetric 0 = 0 := by
  simp [colourSymmetric]

/-- Every colour component is positive: its sign record is `+`. -/
theorem colourSymmetric_positive (j : Fin 4) (hj : j ≠ 0) : 0 < colourSymmetric j := by
  rw [colourSymmetric_eq]
  simp [hj]

/-- **Colour symmetry.** Every permutation of the colour axes fixes it. -/
theorem colourSymmetric_invariant (σ : Equiv.Perm (Fin 4)) (h0 : σ 0 = 0) :
    colourSymmetric ∘ σ = colourSymmetric := by
  funext j
  have hiff : σ j = 0 ↔ j = 0 :=
    ⟨fun h => σ.injective (h.trans h0.symm), fun h => by rw [h, h0]⟩
  simp only [Function.comp, colourSymmetric_eq, hiff]

/-- A channel-resolving comparison of a colour axis with the colour-symmetric state would see
squared overlap `1/3` of the norms. -/
theorem colour_axis_overlap (j : Fin 4) (hj : j ≠ 0) :
    dot (axisVec j) colourSymmetric ^ 2 =
      (1 / 3) * dot colourSymmetric colourSymmetric * dot (axisVec j) (axisVec j) := by
  fin_cases j
  · exact absurd rfl hj
  all_goals simp [dot, axisVec, colourSymmetric, Fin.sum_univ_four, Pi.single_apply]
  all_goals norm_num

end PMElementaryParticles.RecordEncoding
