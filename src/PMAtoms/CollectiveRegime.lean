import PMAtoms.NuclearRegime
import PMAtoms.Nucleus
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.


# Collective / fission regime beyond the deformed frontier

Beyond `Z=96`, `N=152` the smooth shell ledger is replaced by a competition of
collective channels: shape configurations and fission/alpha exits.  A channel
persists only if no allowed channel lowers the collective mass.
-/

namespace PMAtoms
open PMElementaryParticles PMHadrons

/-- A collective exit channel with its mass and barrier. -/
structure CollectiveChannel where
  mass : ℝ
  barrier : ℝ

def CollectiveChannel.totalMass (c : CollectiveChannel) : ℝ :=
  c.mass + c.barrier

/-- Lower envelope of the parent mass and all collective channels. -/
def collectiveMass (parent : ℝ) (channels : List CollectiveChannel) : ℝ :=
  channels.foldl (fun m c => min m (CollectiveChannel.totalMass c)) parent

theorem collectiveMass_le_parent (parent : ℝ) (channels : List CollectiveChannel) :
    collectiveMass parent channels ≤ parent := by
  unfold collectiveMass
  induction channels generalizing parent with
  | nil => simp
  | cons c cs ih =>
      simp only [List.foldl_cons]
      exact le_trans (ih (min parent (CollectiveChannel.totalMass c))) (min_le_left _ _)

theorem collectiveMass_le_channel (parent : ℝ) (channels : List CollectiveChannel)
    (c : CollectiveChannel) (hc : c ∈ channels) :
    collectiveMass parent channels ≤ CollectiveChannel.totalMass c := by
  unfold collectiveMass
  induction channels generalizing parent with
  | nil => simp at hc
  | cons d ds ih =>
      simp only [List.foldl_cons]
      rw [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact le_trans (collectiveMass_le_parent (min parent (CollectiveChannel.totalMass c)) ds)
          (min_le_right _ _)
      · exact ih (min parent (CollectiveChannel.totalMass d)) hc

/-- The collective persistence criterion: no channel lowers the parent mass. -/
def CollectivePersists (parent : ℝ) (channels : List CollectiveChannel) : Prop :=
  ∀ c ∈ channels, parent ≤ CollectiveChannel.totalMass c

theorem collectiveMass_eq_parent_of_forall (parent : ℝ) (channels : List CollectiveChannel)
    (h : CollectivePersists parent channels) :
    collectiveMass parent channels = parent := by
  unfold collectiveMass
  induction channels generalizing parent with
  | nil => simp
  | cons c cs ih =>
      have hc : parent ≤ CollectiveChannel.totalMass c := h c (by simp)
      have hmin : min parent (CollectiveChannel.totalMass c) = parent := min_eq_left hc
      simp only [List.foldl_cons, hmin]
      exact ih parent (fun d hd => h d (by simp [hd]))


/-- Alpha exit channel using the smooth ledger for the daughter and the E8 shell
weight as the barrier. -/
noncomputable def alphaChannel (p : Nuclide) : CollectiveChannel :=
  { mass := nuclearMassPackingShellPaired (p.Z - 2) (p.N - 2) +
      nuclearMassPackingShellPaired 2 2
    barrier := shellWeight }

/-- Fission channel for two supplied fragments, with the E8 shell weight as the
barrier. -/
noncomputable def fissionChannel (_p f1 f2 : Nuclide) : CollectiveChannel :=
  { mass := nuclearMassPackingShellPaired (f1.Z) (f1.N) +
      nuclearMassPackingShellPaired (f2.Z) (f2.N)
    barrier := shellWeight }

theorem alphaChannel_totalMass (p : Nuclide) :
    (alphaChannel p).totalMass =
      nuclearMassPackingShellPaired (p.Z - 2) (p.N - 2) +
        nuclearMassPackingShellPaired 2 2 + shellWeight := rfl

theorem fissionChannel_totalMass (p f1 f2 : Nuclide) :
    (fissionChannel p f1 f2).totalMass =
      nuclearMassPackingShellPaired (f1.Z) (f1.N) +
        nuclearMassPackingShellPaired (f2.Z) (f2.N) + shellWeight := rfl


theorem not_collectivePersists_of_lower {parent : ℝ} {channels : List CollectiveChannel}
    {c : CollectiveChannel} (hc : c ∈ channels) (h : c.totalMass < parent) :
    ¬ CollectivePersists parent channels := by
  intro hp
  have hle := hp c hc
  linarith

end PMAtoms
