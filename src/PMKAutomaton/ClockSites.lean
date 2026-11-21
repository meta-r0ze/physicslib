import PMKAutomaton.ClockTickWeights
import PMKAutomaton.RingReceiver
import PMSubstrate.E8Values

/-!
# Receiver sites are clock readings

`ClockRing` proves that a `+1` root step is `finRotate 43` on the clock
reading. `RingReceiver` runs its two streams on `Fin Δ` by `streamShift` of
`finRotate`. This module identifies the two: a lattice point `z` has receiver
site `site z = clockReading z`, the ring size is `Δ = 43`, forward tick roots
advance the site and backward tick roots retreat it.

The main arrival theorem is `arrivals_are_lattice_steps`: the live arrival at a
site comes from one forward root step back, and the record arrival from one
backward root step back.

The identification of one receiver tick with one root event is the update
model, and Closure for equal weights is the premise stated in
`PMElementaryParticles/LINE-AND-COMPOSITION.md`. Neither premise is proved here.
-/

namespace PMKAutomaton.ClockSites

open PMKAutomaton.ClockRing
open PMKAutomaton.ClockTickWeights
open PMSubstrate

/-- The receiver site of a lattice point: its clock reading in `Fin 43`. -/
def site (z : V) : Fin 43 := toFin (clockReading z)

/-- The receiver ring size is the substrate period `Δ`. -/
theorem ring_size : (43 : ℕ) = PMSubstrate.E8Values.Delta :=
  PMSubstrate.E8Values.Delta_eq.symm

/-- A forward tick root advances the receiver site. -/
theorem site_add_forward (f z : V) (hf : clockReading f = 1) :
    site (z + f) = finRotate 43 (site z) :=
  ClockRing.plus_step_rotates z f hf

/-- A backward tick root retreats the receiver site. -/
theorem site_add_backward (b z : V) (hb : clockReading b = -1) :
    site (z + b) = (finRotate 43).symm (site z) := by
  have hneg : clockReading (-b) = 1 := by
    rw [clockReading_neg, hb]
    norm_num
  have h := ClockRing.plus_step_rotates (z + b) (-b) hneg
  have hz : (z + b) + (-b) = z := by abel
  rw [hz] at h
  have h' := congrArg (finRotate 43).symm h.symm
  simpa [site] using h'

/-- **Arrivals are lattice steps.** With a forward tick root `f` and a
backward tick root `b`, the live arrival at `site z` is the live field at
`site (z - f)`, and the record arrival is the record field at `site (z - b)`. -/
theorem arrivals_are_lattice_steps
    (s : PMAction.OpenReferenceFlow.State (Fin 43) Bool) (z f b : V)
    (hf : clockReading f = 1) (hb : clockReading b = -1) :
    RingReceiver.arrivals s (site z) =
      ((s (site (z - f))).1, (s (site (z - b))).2) := by
  have hlive : (finRotate 43)⁻¹ (site z) = site (z - f) := by
    have h := site_add_forward f (z - f) hf
    have hz : z - f + f = z := by abel
    rw [hz] at h
    have h' := congrArg (finRotate 43).symm h
    simpa [site] using h'
  have hrecord : finRotate 43 (site z) = site (z - b) := by
    have h := site_add_backward b (z - b) hb
    have hz : z - b + b = z := by abel
    rw [hz] at h
    have h' := congrArg (finRotate 43) h
    simpa [site] using h'
  unfold RingReceiver.arrivals PMAction.OpenReferenceFlow.streamShift
  rw [hlive, hrecord]

end PMKAutomaton.ClockSites
