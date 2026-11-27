import PMSubstrate.ClockScale
import PMKAutomaton.AutonomousCensus
import PMElementaryParticles.ProgramWitness

/-!
# Conditional physical clock-scale conflict

The named SCOPE input is a positive root-tick duration kappa, in electron
time units. PhysicalUnits and PMAtoms.E8Tick use that same upstream type.
No theorem derives kappa from Delta or from electronTime's SI conversion.
The existing e8p E8TickUnit value is a whole Delta-update block at the legacy
kappa=1 candidate; it is NOT a single root-update duration.

The supplied telegraph/Dirac context relation rate=mass is not assumed as a
PM law. Conditional on it, unit electron rate and one reversal per Delta
updates require kappa=1/43, not the legacy 1. At kappa=1 unit rate instead
requires 43 reversals per 43 updates. This violates the existing Margin
ceiling WHEN that native execution is identified with a differing record
ring. A proof of the physical identification is not silently supplied.
-/
namespace PMElementaryParticles.ClockScaleBoundary
open PMSubstrate.ClockScale PMElementaryParticles.ProgramWitness

theorem differing_ring_margin_excludes_unit_rate (p : RingProgram) (hm : Margin p)
    (b : Fin 2) (hd : differs p b) :
    perElectronTime legacyUnitTick (registrations p b : ℝ) PMSubstrate.E8Values.Delta ≠ 1 := by
  apply legacy_unit_rate_excludes_margin
  have hr := hm b hd
  have hb : registrations p b ≤ 42 := by omega
  exact_mod_cast hb

/-- The robust at-rest Boolean family fails the old strict per-ring Margin ceiling. -/
theorem saturated_family_exceeds_margin {n : ℕ} (b : Bool)
    (s : PMKAutomaton.AutonomousRing.OnePacket n) :
    ¬ PMKAutomaton.AutonomousRing.nativeReversals
      (PMKAutomaton.AutonomousRing.explicitRule 4 b) s 43 ≤ 42 := by
  rw [PMKAutomaton.AutonomousRing.saturated_reversals]
  norm_num

end PMElementaryParticles.ClockScaleBoundary
