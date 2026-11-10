import PMHadrons.TollGovernor
import PMElementaryParticles.RateModel
import PMAtoms.CollectiveRate
import PMAtoms.NuclearExitWaveBridge
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

theorem attemptFrequency_pos : 0 < attemptFrequency := by
  rw [attemptFrequency_eq]; norm_num

/-! ## The Governor-pinned collective rate

The collective rate (`CollectiveRate.collectiveRate = Σ exp(−barrier)`) is the channel's summed
barrier fraction; with the attempt frequency fixed by the Governor it becomes
`χ/Δ · Σ exp(−barrier)`, and the mean life follows in E8 ticks. -/

/-- The Governor-pinned collective rate `χ/Δ · Σ barrier fractions`. -/
noncomputable def governorCollectiveRate (channels : List CollectiveChannel) : ℝ :=
  attemptFrequency * collectiveRate channels

theorem governorCollectiveRate_eq (channels : List CollectiveChannel) :
    governorCollectiveRate channels = collectiveRate channels * attemptFrequency := by
  unfold governorCollectiveRate; ring

theorem governorCollectiveRate_pos (channels : List CollectiveChannel) (h : channels ≠ []) :
    0 < governorCollectiveRate channels :=
  mul_pos attemptFrequency_pos (collectiveRate_pos channels h)

/-- The Governor-pinned collective mean life, in E8 ticks. -/
noncomputable def governorCollectiveMeanLife (channels : List CollectiveChannel) : ℝ :=
  PMElementaryParticles.MeanLife (governorCollectiveRate channels)

theorem governorCollectiveMeanLife_pos (channels : List CollectiveChannel) (h : channels ≠ []) :
    0 < governorCollectiveMeanLife channels :=
  PMElementaryParticles.MeanLife_pos (governorCollectiveRate_pos channels h)

/-! ## The standard exit table with the Governor

The β⁻/β⁺/α/fission exit table (`NuclearExitWaveBridge`) is a collective decay channel with a
supplied toll `c0`; pinning `c0 = χ/Δ` gives the standard exit-table channel its Governor rate. -/

/-- The standard exit-table decay channel with the Governor as its toll (`c0 = χ/Δ`). -/
noncomputable def governorExitChannel (p f1 f2 : Nuclide) :
    PersistenceMechanics.Decay.DecayChannel :=
  nuclearExitDecayChannel attemptFrequency p f1 f2

theorem governorExitChannel_toll (p f1 f2 : Nuclide) :
    (governorExitChannel p f1 f2).toll = attemptFrequency := rfl

theorem governorExitChannel_rate (β : ℝ) (p f1 f2 : Nuclide) :
    PersistenceMechanics.Decay.rate β (governorExitChannel p f1 f2) =
      collectiveFiniteRate β attemptFrequency (nuclearExitBarrier p f1 f2) Finset.univ :=
  nuclearExitDecayChannel_rate β attemptFrequency p f1 f2

end PMAtoms.NuclearRateUnit
