import PMKAutomaton.ClockAlignment
import PMKAutomaton.ClockSites
import PMElementaryParticles.ProgramWitness

/-!
# The EP spine: programs on the node machinery

**Step 2: ring steps keep the generation.** A ring step is a clock-axis root of
the spacetime `D4`. Spacetime roots have glue key `0` (`clockAxis_key`), and the
glue key is additive (`ClockAlignment.glueKey_add`), so a step never changes a
packet's glue coset (`step_keeps_generation`). Walking forward `n` steps keeps
the coset and moves the receiver site `n` places (`forward_walk`); the same
holds backward (`backward_walk`). The ring dynamics are generation-blind.

**Step 1: one program type on the physical machine.** A `Program` is a label,
a generation (one of the three nonzero glue keys, `generation_card`), a
reference, one firing pattern per record-bit ring on the 43-site clock ring,
and an E8 packet: a root in the program's coset. Its start site is the
packet's clock reading (`Program.x0 = site packet`), so the receiver ring the
pillars are checked on is the packet's own clock position.

**Step 4: the spine theorem.** For every generation and every visible class
there is a program meeting all six pillars (`spine`); the invisible class has
none (`singlet_no_program`); `3 × 5 = 15` (`programs_card`). Each program's
packet stays in its coset and tracks the receiver ring under its own steps
(`program_walk`).
-/

noncomputable section

namespace PMElementaryParticles.EPSpine

open PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment PMKAutomaton.ClockSites
open PMConstants.PacketGaugeActions
open PMElementaryParticles.IsolatedExcitation
open PMElementaryParticles.RingRates
open PMElementaryParticles.ProgramClasses PMElementaryParticles.ProgramWitness

/-! ## Step 2: ring steps keep the generation -/

/-- Clock-axis roots are spacetime roots, so their glue key is `0`. -/
theorem clockAxis_key {f : V} (hf : f ∈ clockAxisRoots) : glueKey f = 0 := by
  have h1 := (List.mem_filter.1 hf).1
  exact (of_decide_eq_true (List.mem_filter.1 h1).2).1

/-- **A ring step never changes the generation.** -/
theorem step_keeps_generation (z f : V) (hf : f ∈ clockAxisRoots) :
    glueKey (z + f) = glueKey z := by
  rw [glueKey_add, clockAxis_key hf, add_zero]

/-- There are forward and backward ring steps. -/
theorem exists_forward : ∃ f ∈ clockAxisRoots, clockReading f = 1 := by decide +kernel
theorem exists_backward : ∃ f ∈ clockAxisRoots, clockReading f = -1 := by decide +kernel

/-- Walking `n` forward steps keeps the coset and advances the site `n` places. -/
theorem forward_walk (z f : V) (hf : f ∈ clockAxisRoots) (h1 : clockReading f = 1)
    (n : ℕ) :
    glueKey (z + n • f) = glueKey z ∧ site (z + n • f) = (finRotate 43)^[n] (site z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : z + (n + 1) • f = (z + n • f) + f := by rw [succ_nsmul]; abel
    rw [hz, step_keeps_generation _ _ hf, site_add_forward f _ h1, ih.1, ih.2,
      Function.iterate_succ_apply']
    exact ⟨rfl, rfl⟩

/-- Walking `n` backward steps keeps the coset and moves the site back `n` places. -/
theorem backward_walk (z f : V) (hf : f ∈ clockAxisRoots) (h1 : clockReading f = -1)
    (n : ℕ) :
    glueKey (z + n • f) = glueKey z ∧
      site (z + n • f) = (⇑(finRotate 43).symm)^[n] (site z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : z + (n + 1) • f = (z + n • f) + f := by rw [succ_nsmul]; abel
    rw [hz, step_keeps_generation _ _ hf, site_add_backward f _ h1, ih.1, ih.2,
      Function.iterate_succ_apply']
    exact ⟨rfl, rfl⟩

/-! ## Step 1: the program type -/

/-- A generation: a nonzero glue key, one of the three glue cosets. -/
abbrev Generation := {k : ZMod 2 × ZMod 2 // k ≠ 0}

theorem generation_card : Fintype.card Generation = 3 := by decide

/-- An EP program on the node machinery. -/
structure Program where
  label : Channels
  generation : Generation
  reference : Bool
  firing : Fin 2 → Fin 43 → IsolatedRequests
  packet : V
  packet_root : packet ∈ rootList
  packet_key : glueKey packet = generation.1

/-- The start site is the packet's clock reading. -/
def Program.x0 (p : Program) : Fin 43 := site p.packet

/-- The receiver-ring data the pillars read. -/
def Program.toRing (p : Program) : RingProgram := ⟨p.label, p.reference, p.firing, p.x0⟩

def Program.Pillars (p : Program) : Prop := ProgramWitness.Pillars p.toRing

/-- **The packet stays in its generation and tracks the receiver ring.** -/
theorem program_walk (p : Program) (f : V) (hf : f ∈ clockAxisRoots)
    (h1 : clockReading f = 1) (n : ℕ) :
    glueKey (p.packet + n • f) = p.generation.1 ∧
      site (p.packet + n • f) = (finRotate 43)^[n] p.x0 := by
  obtain ⟨hk, hs⟩ := forward_walk p.packet f hf h1 n
  exact ⟨hk.trans p.packet_key, hs⟩

/-! ## Step 4: the spine -/

/-- Every generation has a root in its coset. -/
theorem exists_root_of_key : ∀ g : Generation, ∃ r ∈ rootList, glueKey r = g.1 := by
  decide +kernel

theorem witnessAt_registrations (c : Channels) (x0 : Fin 43) (b : Fin 2) :
    registrations ⟨c, leastRef c, fun _ => oneFiringN 43 0, x0⟩ b = 1 :=
  one_site_exact true 0 x0

/-- The least-Toll one-site program meets all six pillars from any start site. -/
theorem witnessAt_pillars (c : Channels) (x0 : Fin 43) (hc : classOf c ≠ 4) :
    ProgramWitness.Pillars ⟨c, leastRef c, fun _ => oneFiringN 43 0, x0⟩ := by
  refine ⟨?_, ?_, ?_, hc, ?_, ?_⟩
  · unfold Capacity; rw [witnessAt_registrations, witnessAt_registrations]; norm_num
  · intro b _; rw [witnessAt_registrations]; norm_num
  · exact (leastRef_hamming c).symm.le
  · intro b _; rw [witnessAt_registrations]
  · exact ⟨0, 1, by simp [oneFiringN, PMKAutomaton.RingReceiver.exchange]⟩

/-- **The spine.** Every generation and every visible class has a program on
the node machinery that meets all six pillars. -/
theorem spine (g : Generation) (k : Fin 6) (hk : k ≠ 4) :
    ∃ p : Program, p.generation = g ∧ classOf p.label = k ∧ p.Pillars := by
  obtain ⟨c, rfl⟩ := classOf_surjective k
  obtain ⟨r, hr, hkey⟩ := exists_root_of_key g
  exact ⟨⟨c, g, leastRef c, fun _ => oneFiringN 43 0, r, hr, hkey⟩, rfl, rfl,
    witnessAt_pillars c (site r) hk⟩

/-- The invisible class has no program in any generation. -/
theorem singlet_no_program (p : Program) (h : classOf p.label = 4) : ¬ p.Pillars :=
  fun hp => hp.2.2.2.1 h

/-- Three generations times five visible classes: fifteen programs. -/
theorem programs_card :
    Fintype.card (Generation × {k : Fin 6 // k ≠ 4}) = 15 := by decide

end PMElementaryParticles.EPSpine

end
