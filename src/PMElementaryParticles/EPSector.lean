import PMElementaryParticles.GaugeSector

/-!
# The program spine on the derived gauge sector

This module puts `EPSpine.Program` on the placement of `GaugeSector`. It replaces the
internal-D4 placement of `EPLabel` and `EPLabelGen` (now in PMChecks), which breaks colour and
the weak flip.

* `readout z` is the gauge readout: the pairings of `z` with the two colour roots, the weak
  root and the charge direction. It is additive (`readout_add`, `readout_nsmul`).
* In each generation the readout tells the 16 placed channels apart
  (`placement_readout_injective`).
* A forward ring step conserves the charge exactly when it is gauge neutral
  (`forward_charge_iff`). There are two neutral forward steps (`neutralSteps_length`), and their
  sum is the clock time vector (`neutralSteps_sum_time`).
* `labelled p` is the program's packet plus its placed label. A walk by a neutral step keeps the
  generation (the packet's glue key), moves the site, and keeps the label readout
  (`neutral_walk`).
* `sector_spine`: every generation and every visible class has a program that meets all six
  pillars, whose label sits in the wall the library's `active` bit names (`wallKey`), and whose
  generation and label are kept on every neutral walk.
-/

namespace PMElementaryParticles.EPSector

open PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment PMKAutomaton.ClockSites
open PMConstants.PacketGaugeActions
open PMElementaryParticles.ProgramClasses PMElementaryParticles.EPSpine
open PMElementaryParticles.GaugeSector

/-- Gauge readout: pairings with `colourA`, `colourB`, `weak`, `chargeDir`. -/
def readout (z : V) : Fin 4 → ℤ := ![pair z colourA, pair z colourB, pair z weak, pair z chargeDir]

theorem readout_add (z w : V) : readout (z + w) = readout z + readout w := by
  funext i; fin_cases i <;> simp [readout, pair_add_left]

theorem readout_nsmul (z : V) (n : ℕ) : readout (n • z) = n • readout z := by
  induction n with
  | zero => funext i; fin_cases i <;> simp [readout, pair]
  | succ n ih => rw [succ_nsmul, readout_add, ih, succ_nsmul]

theorem placement_readout_injective :
    ∀ g c c', readout (placement g c) = readout (placement g c') → c = c' := by decide

/-- A forward ring step conserves the charge exactly when it is gauge neutral. -/
theorem forward_charge_iff :
    ∀ f ∈ clockAxisRoots, clockReading f = 1 → (pair f chargeDir = 0 ↔ readout f = 0) := by
  decide +kernel

/-- The gauge-neutral forward ring steps. -/
def neutralSteps : List V :=
  clockAxisRoots.filter fun f => decide (clockReading f = 1 ∧ readout f = 0)

theorem neutralSteps_length : neutralSteps.length = 2 := by decide +kernel

theorem neutralSteps_sum_time : ∃ f ∈ neutralSteps, ∃ f' ∈ neutralSteps, f + f' = timeVec := by
  decide +kernel

/-- Index of a generation in `GaugeSector.placement`. -/
def sectorIndex (g : Generation) : Fin 3 :=
  if g.1 = (0, 1) then 0 else if g.1 = (1, 0) then 1 else 2

theorem sectorIndex_key : ∀ g : Generation, ownKey (sectorIndex g) = g.1 := by decide

theorem sectorIndex_bijective : Function.Bijective sectorIndex := by decide

/-- The program's packet plus its placed label. -/
def labelled (p : Program) : V := p.packet + placement (sectorIndex p.generation) p.label

theorem neutral_walk (p : Program) (f : V) (hf : f ∈ neutralSteps) (n : ℕ) :
    glueKey (p.packet + n • f) = p.generation.1 ∧
      site (p.packet + n • f) = (finRotate 43)^[n] (site p.packet) ∧
      readout (labelled p + n • f) =
        readout p.packet + readout (placement (sectorIndex p.generation) p.label) := by
  have hf' := List.mem_filter.mp hf
  obtain ⟨hax, hd⟩ := hf'
  have h1 : clockReading f = 1 := (of_decide_eq_true hd).1
  have h0 : readout f = 0 := (of_decide_eq_true hd).2
  obtain ⟨hk, hs⟩ := forward_walk p.packet f hax h1 n
  refine ⟨hk.trans p.packet_key, hs, ?_⟩
  rw [labelled, readout_add, readout_nsmul, h0, smul_zero, add_zero, readout_add]

/-- **The spine on the derived sector.** -/
theorem sector_spine (g : Generation) (k : Fin 6) (hk : k ≠ 4) :
    ∃ p : Program, p.generation = g ∧ classOf p.label = k ∧ p.Pillars ∧
      glueKey (placement (sectorIndex g) p.label) =
        wallKey (sectorIndex g) (PMElementaryParticles.ProtocolInventory.active p.label) ∧
      ∀ f ∈ neutralSteps, ∀ n : ℕ, glueKey (p.packet + n • f) = g.1 ∧
        readout (labelled p + n • f) - readout p.packet =
          readout (placement (sectorIndex g) p.label) := by
  obtain ⟨p, hg, hc, hp⟩ := spine g k hk
  subst hg
  refine ⟨p, rfl, hc, hp, placement_walls _ _, fun f hf n => ⟨(neutral_walk p f hf n).1, ?_⟩⟩
  rw [(neutral_walk p f hf n).2.2]; abel

end PMElementaryParticles.EPSector
