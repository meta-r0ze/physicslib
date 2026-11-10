import PMHadrons.TollGovernor
import PMElementaryParticles.RateModel
import Mathlib.Tactic

/-!

# The nuclear rate unit from the Governor

The per-channel rate is `β · c0 · Σ prob` (`PMElementaryParticles.channelRate`), with `c0 = 1` the
toll (`PMSubstrate.NetCost`) and `β` the hazard. The one input named by the review is the *absolute
attempt frequency* `β · c0`. On E8 the per-slot share that keeps a system going is the **Governor**
credit `χ/Δ = 2/43` (`PMHadrons.TollGovernor.governorPerSlot`, from
`PMSubstrate.ImpedanceTerms.governor_uniform`); it already appears as the phase margin
(`PMAtoms.PersistenceComplex.phaseMargin_eq_one_add_governor`, `41/43 = 1 + governorTerm`).

This module records the candidate identification `β · c0 = χ/Δ`, so the per-slot attempt frequency
is the Governor share and a channel's rate is `χ/Δ · Σ prob`. The identification is a **named model
foundation** (a candidate to test), not yet derived.
-/

namespace PMAtoms.NuclearRateUnit

open PMSubstrate.E8Values

/-- Candidate: the per-slot nuclear attempt frequency is the Governor credit `χ/Δ`. -/
noncomputable def attemptFrequency : ℝ := (chi : ℝ) / (Delta : ℝ)

theorem attemptFrequency_eq : attemptFrequency = 2 / 43 := by
  unfold attemptFrequency
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.Delta_eq]
  norm_num

/-- The per-slot channel rate with the attempt frequency fixed by the Governor. -/
noncomputable def governorChannelRate {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}
    (E : Fin k → Finset Ω) : ℝ :=
  attemptFrequency * ∑ i, PMSubstrate.NetCost.prob (E i)

/-- **It is the general `RateModel.channelRate` with `β · c0 = χ/Δ`** (`c0 = 1`). -/
theorem governorChannelRate_eq {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}
    (E : Fin k → Finset Ω) :
    governorChannelRate E = PMElementaryParticles.channelRate attemptFrequency 1 E := by
  rw [PMElementaryParticles.channelRate_eq]
  unfold governorChannelRate
  ring

end PMAtoms.NuclearRateUnit
