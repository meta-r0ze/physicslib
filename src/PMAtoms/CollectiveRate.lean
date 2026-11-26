import PMAtoms.CollectiveRegime
import PMAtoms.PersistenceRate
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.


# Collective channels → hazard → mean life

The collective mass envelope is not the persistence selector: fission fragments
can be lower in mass while the barrier keeps the rate small.  This module wires
the channel barrier to a hazard and then to `Rates.meanLife` and `PersistsOn`.
-/

noncomputable section
namespace PMAtoms
open PersistenceMechanics PMHadrons

/-- Schematic barrier suppression.  The physical barrier/clock normalization is
still an open E8 input. -/
def barrierRate (barrier : ℝ) : ℝ := Real.exp (-barrier)

theorem barrierRate_pos (barrier : ℝ) : 0 < barrierRate barrier := by
  unfold barrierRate
  positivity

def CollectiveChannel.rate (c : CollectiveChannel) : ℝ :=
  barrierRate c.barrier

def collectiveRate (channels : List CollectiveChannel) : ℝ :=
  Rates.parallelRate (channels.map CollectiveChannel.rate)

theorem collectiveRate_nonneg (channels : List CollectiveChannel) :
    0 ≤ collectiveRate channels := by
  unfold collectiveRate Rates.parallelRate
  exact List.sum_nonneg (by intro r hr; rcases List.mem_map.mp hr with ⟨c, _, rfl⟩; exact le_of_lt (barrierRate_pos _))

theorem collectiveRate_pos (channels : List CollectiveChannel) (h : channels ≠ []) :
    0 < collectiveRate channels := by
  cases channels with
  | nil => contradiction
  | cons c cs =>
      simp only [collectiveRate, Rates.parallelRate, List.map_cons, List.sum_cons]
      exact add_pos_of_pos_of_nonneg (barrierRate_pos c.barrier)
        (List.sum_nonneg (by
          intro r hr
          rcases List.mem_map.mp hr with ⟨d, _, rfl⟩
          exact le_of_lt (barrierRate_pos d.barrier)))

/-- Mean life of the collective channel family. -/
def collectiveMeanLife (channels : List CollectiveChannel) (h : channels ≠ []) : ℝ :=
  Rates.meanLife (collectiveRate channels) (collectiveRate_pos channels h)

theorem collectiveMeanLife_pos (channels : List CollectiveChannel) (h : channels ≠ []) :
    0 < collectiveMeanLife channels h :=
  Rates.meanLife_pos (collectiveRate_pos channels h)

/-- Persistence on a timescale `T`: no channels means indefinite persistence;
otherwise the mean life exceeds the observation time. -/
def PersistsOn (T : ℝ) (channels : List CollectiveChannel) : Prop :=
  channels = [] ∨ ∃ h : channels ≠ [], T ≤ collectiveMeanLife channels h

theorem persistsOn_nil (T : ℝ) : PersistsOn T [] := Or.inl rfl

theorem persistsOn_mono {T U : ℝ} {channels : List CollectiveChannel}
    (hTU : T ≤ U) (h : PersistsOn U channels) : PersistsOn T channels := by
  rcases h with rfl | ⟨hne, h⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hne, le_trans hTU h⟩

theorem not_persistsOn_of_lt_meanLife {T : ℝ} {channels : List CollectiveChannel}
    (hne : channels ≠ []) (h : collectiveMeanLife channels hne < T) :
    ¬ PersistsOn T channels := by
  intro hp
  rcases hp with rfl | ⟨_, hle⟩
  · exact hne rfl
  · linarith


/-- The ledger time: toll divided by total energy.  Dimensionless when both are
in the same E8 unit. -/
def tollTime (toll energy : ℝ) : ℝ := toll / energy

/-- Persistence over the ledger window `toll/energy`. -/
def PersistsAtToll (toll energy : ℝ) (channels : List CollectiveChannel) : Prop :=
  PersistsOn (tollTime toll energy) channels

theorem persistsAtToll_iff (toll energy : ℝ) (channels : List CollectiveChannel) :
    PersistsAtToll toll energy channels ↔
      (channels = [] ∨ ∃ h : channels ≠ [],
        tollTime toll energy ≤ collectiveMeanLife channels h) := Iff.rfl

/-- If the toll window exceeds the mean life, the system does not persist. -/
theorem not_persistsAtToll_of_lt_meanLife {toll energy : ℝ}
    {channels : List CollectiveChannel} (hne : channels ≠ [])
    (h : collectiveMeanLife channels hne < tollTime toll energy) :
    ¬ PersistsAtToll toll energy channels := by
  intro hp
  rcases hp with rfl | ⟨_, hle⟩
  · exact hne rfl
  · linarith

end PMAtoms
