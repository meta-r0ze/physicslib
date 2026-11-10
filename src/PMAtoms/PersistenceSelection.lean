import PMAtoms.NuclearDecay
import PMAtoms.CollectiveRate
import PMAtoms.PersistenceRate
import Mathlib.Tactic

/-!

# Persistence selection of a nuclide

A nuclide's fate is selected by its exit-channel hazards, not by mass alone
(`CollectiveRate.not_collectivePersists_of_lower` shows mass minimality is the wrong criterion past
the frontier). The rate layer (`PersistenceRate`) selects the least-total-hazard member of a family;
this module wires the nuclear exit table (`NuclearDecay.nuclearExitChannels`) into it. So the
**valley** is a persistence selection once the barrier/rate unit is fixed (`NuclearRateUnit`), with
the regime split (`NuclearRegime`) deciding which ledger supplies the Q-values.
-/

namespace PMAtoms.PersistenceSelection

/-- The exit-channel rate system of a nuclide (fission split supplied). -/
noncomputable def nuclearExitRateSystem (p f1 f2 : Nuclide) : RateSystem :=
  ⟨(nuclearExitChannels p f1 f2).map CollectiveChannel.rate⟩

theorem nuclearExitChannels_ne_nil (p f1 f2 : Nuclide) :
    nuclearExitChannels p f1 f2 ≠ [] := by
  intro h
  have := nuclearExitChannels_length p f1 f2
  rw [h] at this
  simp at this

/-- The exit hazard is the collective rate of the exit table. -/
theorem nuclearExitRateSystem_totalRate (p f1 f2 : Nuclide) :
    (nuclearExitRateSystem p f1 f2).totalRate =
      collectiveRate (nuclearExitChannels p f1 f2) := rfl

/-- **A nuclide persists on timescale `T` exactly when its exit mean life reaches `T`** (the exit
table is never empty, so the empty-channel case cannot occur). -/
theorem nuclearPersistsOn_iff (p f1 f2 : Nuclide) (T : ℝ) :
    PersistsOn T (nuclearExitChannels p f1 f2) ↔
      T ≤ collectiveMeanLife (nuclearExitChannels p f1 f2) := by
  unfold PersistsOn
  constructor
  · rintro (h | h)
    · exact absurd h (nuclearExitChannels_ne_nil p f1 f2)
    · exact h
  · exact Or.inr

/-- **The persistence-selected nuclide is the least-total-hazard one** (`PersistenceRate`). -/
theorem selectedNuclide_min (systems : Finset RateSystem) (h : systems.Nonempty) :
    ∀ s ∈ systems, (selectedSystem systems h).totalRate ≤ s.totalRate :=
  selectedSystem_min systems h

/-- **The persistence-selected nuclide has the longest mean life** (among positive-hazard systems).
So the selection is a persistence selection, not a mass one: a lower-mass neighbour with a higher
exit hazard is not selected (`CollectiveRate.not_collectivePersists_of_lower`). -/
theorem selectedNuclide_meanLife_max (systems : Finset RateSystem) (h : systems.Nonempty)
    (hpos : ∀ s ∈ systems, 0 < s.totalRate) :
    ∀ s ∈ systems, s.meanLife ≤ (selectedSystem systems h).meanLife := by
  intro s hs
  have hmin := selectedSystem_min systems h s hs
  have hbest := hpos (selectedSystem systems h) (selectedSystem_mem systems h)
  simp only [RateSystem.meanLife, PMElementaryParticles.MeanLife]
  exact one_div_le_one_div_of_le hbest hmin

end PMAtoms.PersistenceSelection
