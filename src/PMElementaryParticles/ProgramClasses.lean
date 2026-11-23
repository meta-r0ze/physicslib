import PMConstants.PacketGaugeActions

/-!
# Program classes: five per generation

The 16 packet channels (`PMConstants.PacketGaugeActions.Channels`) carry the
substrate's own actions: the weak flip `flipWeak`, the colour transpositions
`permuteColour`, and the charge `charge` (its diagonal is the hypercharge).

* Under the weak and colour actions the channels fall into six classes
  (`classOf`): invariant (`classOf_flipWeak`, `classOf_permuteColour`), onto
  (`classOf_surjective`), and each class is one orbit (`class_transitive`).
* Exactly two classes are left fixed by every weak and colour action
  (`unmoved_iff`): the two singlets.
* Exactly one channel has zero charge diagonal (`charge_zero_iff`).
* So exactly one class is fixed by every action **and** carries no charge
  (`invisible_iff`): class `4`, the total singlet `.inr (.inr (.inr 0))`.
  No substrate observable distinguishes it from the vacuum.

Map's failure mode is a record that cannot be distinguished from the
reference. Read with the substrate's observables, Map removes exactly class `4`,
and **five classes remain** (`visible_class_iff`, `visibleClasses_card`): the
weak-doublet colour triplet (6 channels), two colour-triplet singlets (3 + 3),
the colourless weak doublet (2), and the charged singlet (1), 15 channels.
With the three glue cosets (generations) this is fifteen programs.

The record-bit Map of `PillarPredicates` does not see charge or chirality and
keeps six classes; this module is the class-level reading. Consequence to
keep in view: the total singlet is the right-handed-neutrino-like channel, so
a neutrino mass cannot be a mass term that needs it (`NeutrinoContext`).
-/

noncomputable section

namespace PMElementaryParticles.ProgramClasses

open PMConstants.PacketGaugeActions

/-- The six weak × colour classes of the 16 channels. -/
def classOf : Channels → Fin 6
  | .inl _ => 0
  | .inr (.inl (_, s)) => if s = 0 then 1 else 2
  | .inr (.inr (.inl _)) => 3
  | .inr (.inr (.inr s)) => if s = 0 then 4 else 5

theorem classOf_flipWeak : ∀ c, classOf (flipWeak c) = classOf c := by decide

theorem classOf_permuteColour : ∀ a b c, classOf (permuteColour a b c) = classOf c := by
  decide

theorem classOf_surjective : Function.Surjective classOf := by decide

/-- `c'` is reached from `c` by a colour transposition, then possibly the weak flip. -/
def Joined (c c' : Channels) : Prop :=
  ∃ a b : Fin 3, c' = permuteColour a b c ∨ c' = flipWeak (permuteColour a b c)

instance (c c' : Channels) : Decidable (Joined c c') := by unfold Joined; infer_instance

/-- **Each class is one orbit**: any two channels of a class are joined. -/
theorem class_transitive : ∀ c c', classOf c = classOf c' → Joined c c' := by
  decide

/-- Fixed by every weak and colour action. -/
def Unmoved (c : Channels) : Prop := flipWeak c = c ∧ ∀ a b, permuteColour a b c = c

instance (c : Channels) : Decidable (Unmoved c) := by unfold Unmoved; infer_instance

theorem unmoved_iff : ∀ c, Unmoved c ↔ (classOf c = 4 ∨ classOf c = 5) := by decide

/-- Exactly one channel has zero charge. -/
theorem charge_zero_iff (c : Channels) : charge c c = 0 ↔ c = .inr (.inr (.inr 0)) := by
  fin_cases c <;> norm_num [charge, block, channelIndex, Matrix.kroneckerMap_apply]

/-- **Exactly one class is invisible to every substrate observable.** -/
theorem invisible_iff (c : Channels) : (Unmoved c ∧ charge c c = 0) ↔ classOf c = 4 := by
  rw [unmoved_iff, charge_zero_iff]
  revert c
  decide

/-- **Five classes are distinguishable from the vacuum.** -/
theorem visible_class_iff (k : Fin 6) :
    (∃ c, classOf c = k ∧ ¬ (Unmoved c ∧ charge c c = 0)) ↔ k ≠ 4 := by
  simp only [invisible_iff]
  revert k
  decide

def visibleClasses : Finset (Fin 6) := Finset.univ.filter (· ≠ 4)

theorem visibleClasses_card : visibleClasses.card = 5 := by decide

/-- The channels outside the invisible class. -/
def visibleChannels : Finset Channels := Finset.univ.filter (fun c => classOf c ≠ 4)

/-- Fifteen visible channels per generation. -/
theorem visible_channels_card : visibleChannels.card = 15 := by decide

end PMElementaryParticles.ProgramClasses

end
