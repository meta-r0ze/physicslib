import PMKAutomaton.ClockAlignment
import PMSubstrate.Channels

/-!
# A clock-aligned pair of D4 sectors

`PMSubstrate.Channels.sectorBasis` supplies two orthogonal D4 sectors in E8, but
its coordinates are not aligned with the clock plane. This module supplies a
second placement. Its first four columns are the aligned spacetime D4 of
`ClockAlignment`; the last four are an internal D4, chosen from
`ClockAlignment.internalRoots`.

The matrix identity `aligned_d4d4` proves that the new columns have the same
block Gram matrix as `Channels.sectorBasis`. The spacetime block's slice roots
are clock-silent (`sector0_slice_silent`) and the internal block has no
clock-silent root (`sector1_not_silent`).

The placement changes the coordinates, not the Gram identity. Dependents that
use only `e8_two_d4_sectors` are independent of the choice; dependents that use
`sectorBasis` coordinates must be rechecked before switching. This module does
not switch them.
-/

namespace PMKAutomaton.AlignedSectors

open PMKAutomaton.ClockRing
open PMKAutomaton.ClockAlignment
open PMSubstrate

/-- First internal simple root. -/
def p : V := ofCode 407832223

/-- Internal central node. -/
def q : V := ofCode 407867557

/-- Third internal simple root. -/
def r : V := ofCode 407893921

/-- Fourth internal simple root. -/
def s : V := ofCode 407865529

theorem p_mem : p ∈ internalRoots := by decide +kernel
theorem q_mem : q ∈ internalRoots := by decide +kernel
theorem r_mem : r ∈ internalRoots := by decide +kernel
theorem s_mem : s ∈ internalRoots := by decide +kernel

theorem pair_p_q : pair p q = -1 := by decide +kernel
theorem pair_q_r : pair q r = -1 := by decide +kernel
theorem pair_q_s : pair q s = -1 := by decide +kernel
theorem pair_p_r : pair p r = 0 := by decide +kernel
theorem pair_p_s : pair p s = 0 := by decide +kernel
theorem pair_r_s : pair r s = 0 := by decide +kernel

/-- The eight aligned simple roots, first the spacetime D4 and then the
internal D4. -/
def alignedColumns : Fin 8 → V := ![a, b, c, beta, p, q, r, s]

/-- The clock-aligned placement. Its first four columns are `a,b,c,beta`; the
last four are the internal D4. -/
def alignedSectorBasis : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => alignedColumns j i

/-- **The aligned placement has the same D4 block Gram matrix.** -/
theorem aligned_d4d4 :
    alignedSectorBasis.transpose * Lattices.gram * alignedSectorBasis = Channels.d4d4 := by
  decide +kernel

/-- The first block is the spacetime D4 root set of `ClockAlignment`. -/
theorem a_mem_spacetime : a ∈ spacetimeRoots := by decide +kernel
theorem b_mem_spacetime : b ∈ spacetimeRoots := by decide +kernel
theorem c_mem_spacetime : c ∈ spacetimeRoots := by decide +kernel
theorem beta_mem_spacetime : beta ∈ spacetimeRoots := by decide +kernel

/-- **Sector 0's slice roots are clock-silent.** -/
theorem sector0_slice_silent (z : V) (hz : z ∈ spacetimeRoots)
    (hcu : pair z ClockPlane.cu = 0) (hcv : pair z ClockPlane.cv = 0) :
    clockReading z = 0 := by
  apply sliceRoots_silent
  rw [sliceRoots]
  exact List.mem_filter.mpr ⟨hz, by simp [hcu, hcv]⟩

/-- **Sector 1 has no clock-silent root.** -/
theorem sector1_not_silent : ∀ z ∈ internalRoots, clockReading z ≠ 0 :=
  internalRoots_not_silent


/-- Combined witness: the aligned D4 block Gram, the clock plane, silent
spacetime slice roots and clock-axis roots of reading `±1`. This stays in
`PMKAutomaton` because `PMSubstrate.Vacuum` cannot import downstream modules. -/
theorem aligned_sectors_clock_witness :
    alignedSectorBasis.transpose * Lattices.gram * alignedSectorBasis = Channels.d4d4 ∧
      (∀ z ∈ sliceRoots, pair z ClockPlane.cu = 0 ∧ pair z ClockPlane.cv = 0 ∧
        clockReading z = 0) ∧
      (∀ z ∈ clockAxisRoots, clockReading z = 1 ∨ clockReading z = -1) := by
  refine ⟨aligned_d4d4, ?_, ?_⟩
  · intro z hz
    have hz' := List.mem_filter.mp hz
    have hpair : pair z ClockPlane.cu = 0 ∧ pair z ClockPlane.cv = 0 :=
      of_decide_eq_true hz'.2
    exact ⟨hpair.1, hpair.2, sliceRoots_silent z hz⟩
  · decide +kernel

end PMKAutomaton.AlignedSectors
