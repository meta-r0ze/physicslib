import PMKAutomaton.ClockAlignment
import PMKAutomaton.Machine.SubstrateWeylRoots

/-!
# Equal tick weights from the aligned slice symmetries

`ClockAlignment` certifies one aligned spacetime `D4`, its twelve clock-silent
slice roots, and the six clock-axis roots at reading `+1` and six at reading
`-1`.

This module proves that reflections in the slice roots fix the clock reading
and act transitively on each six-root tick set. The six forward tick steps are
therefore one orbit of the substrate symmetries that fix the clock, and so are
the six backward steps.

The closure step is the same premise as in `SliceHop`: a weight defined inside
the substrate is invariant under the substrate's symmetries that fix the clock.
`SliceHop.silent_words_eq_orbit` shows the four clock-silent hop words are one
orbit of the clock-fixing swaps `swap01`, `swap23`, and `SliceHop.slice_uniform`
turns invariance under those swaps into a uniform weight. Given that premise,
the six forward steps carry equal weight and the six backward steps carry equal
weight. Closure itself is not proved here.

The finite orbit checks are `forward_closed`, `forward_one_orbit`,
`backward_closed` and `backward_one_orbit`; the clock invariance of a slice
reflection is `clockReading_reflect`.
-/

namespace PMKAutomaton.ClockTickWeights

open PMKAutomaton.ClockRing
open PMKAutomaton.ClockAlignment
open PMSubstrate

open PMAction.SubstrateWeylRoots (reflectIn)

/-- The pairing is linear in its first argument under integer scaling. -/
theorem pair_smul_left (k : ℤ) (x y : V) :
    PMSubstrate.Lattices.pairing (k • x) y = k * PMSubstrate.Lattices.pairing x y := by
  simp only [PMSubstrate.Lattices.pairing]
  rw [smul_dotProduct, smul_eq_mul]

/-- Reflecting a root in itself gives its negative. -/
theorem pair_reflect_self (alpha : V) (h : PMSubstrate.Lattices.pairing alpha alpha = 2) :
    reflectIn alpha alpha = -alpha := by
  funext i
  simp [reflectIn, Pi.neg_apply, h]
  ring

/-- The clock reading is linear under integer scaling. -/
theorem clockReading_smul (k : ℤ) (x : V) :
    clockReading (k • x) = (k : ZMod 43) * clockReading x := by
  unfold clockReading
  rw [pair_smul_left, pair_smul_left]
  push_cast
  ring

/-- **A slice reflection fixes the clock reading.** The slice root is
clock-silent, so subtracting its integer multiple leaves the reading unchanged. -/
theorem clockReading_reflect (v alpha : V) (h : clockReading alpha = 0) :
    clockReading (reflectIn alpha v) = clockReading v := by
  unfold reflectIn
  rw [sub_eq_add_neg, clockReading_add, clockReading_neg, clockReading_smul, h,
    mul_zero, neg_zero, add_zero]

/-- The six forward clock-axis roots. -/
def forwardRoots : List V := clockAxisRoots.filter fun r => clockReading r = 1

/-- The six backward clock-axis roots. -/
def backwardRoots : List V := clockAxisRoots.filter fun r => clockReading r = -1

theorem forwardRoots_length : forwardRoots.length = 6 := by decide +kernel
theorem backwardRoots_length : backwardRoots.length = 6 := by decide +kernel

/-- **The forward tick set is closed under slice reflections.** -/
theorem forward_closed :
    ∀ alpha ∈ sliceRoots, ∀ f ∈ forwardRoots, reflectIn alpha f ∈ forwardRoots := by
  decide +kernel

/-- **The backward tick set is closed under slice reflections.** -/
theorem backward_closed :
    ∀ alpha ∈ sliceRoots, ∀ f ∈ backwardRoots, reflectIn alpha f ∈ backwardRoots := by
  decide +kernel

/-- The first forward tick root. -/
def f0 : V := forwardRoots.headD 0

/-- The first backward tick root. -/
def b0 : V := backwardRoots.headD 0

theorem f0_mem : f0 ∈ forwardRoots := by decide +kernel
theorem b0_mem : b0 ∈ backwardRoots := by decide +kernel

/-- The finite check that two slice reflections carry `f0` to each forward root. -/
def forwardHit (f : V) : Bool :=
  sliceRoots.any fun alpha =>
    sliceRoots.any fun beta => decide (reflectIn beta (reflectIn alpha f0) = f)

/-- The finite check that two slice reflections carry `b0` to each backward root. -/
def backwardHit (f : V) : Bool :=
  sliceRoots.any fun alpha =>
    sliceRoots.any fun beta => decide (reflectIn beta (reflectIn alpha b0) = f)

theorem forward_hits_by_two :
    ∀ f ∈ forwardRoots, forwardHit f = true := by
  decide +kernel

theorem backward_hits_by_two :
    ∀ f ∈ backwardRoots, backwardHit f = true := by
  decide +kernel

/-- **One forward orbit.** Every forward tick root is two slice reflections
from `f0`. The two reflections may include a reflection that fixes the root. -/
theorem forward_one_orbit (f : V) (hf : f ∈ forwardRoots) :
    ∃ alpha ∈ sliceRoots, ∃ beta ∈ sliceRoots,
      reflectIn beta (reflectIn alpha f0) = f := by
  have h := List.any_eq_true.mp (forward_hits_by_two f hf)
  obtain ⟨alpha, ha, h2⟩ := h
  rw [List.any_eq_true] at h2
  obtain ⟨beta, hb, h3⟩ := h2
  exact ⟨alpha, ha, beta, hb, of_decide_eq_true h3⟩

/-- **One backward orbit.** Every backward tick root is two slice reflections
from `b0`. -/
theorem backward_one_orbit (f : V) (hf : f ∈ backwardRoots) :
    ∃ alpha ∈ sliceRoots, ∃ beta ∈ sliceRoots,
      reflectIn beta (reflectIn alpha b0) = f := by
  have h := List.any_eq_true.mp (backward_hits_by_two f hf)
  obtain ⟨alpha, ha, h2⟩ := h
  rw [List.any_eq_true] at h2
  obtain ⟨beta, hb, h3⟩ := h2
  exact ⟨alpha, ha, beta, hb, of_decide_eq_true h3⟩

end PMKAutomaton.ClockTickWeights
