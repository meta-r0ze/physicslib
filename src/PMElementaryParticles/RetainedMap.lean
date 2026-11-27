import PMElementaryParticles.ReversalEvents

/-!
# Conserved carrier identity and readable reference records

Ring-root words conserve the glue generation and internal content. The label
record is a function of the channel, not the generation. It retains label
information; it does not distinguish all conserved carrier identities.
It would be incorrect to say that it retains no conserved quantity.

`ReadableReference` states the requested strengthened Map as an explicit
period-end decoding contract. Its retained identity is generation, channel and
conserved internal content. Class and labelRecord are functions of the channel. Only the already conserved
carrier labels are used. The decoder must read the actual two-ring machine state.
It cannot read a free generation tag or root coordinates.
The retained requests, probe, phase and both port streams are allowed.

This is a specification, not a derived repair mechanism. PMSubstrate.Pillars.map_maintains
proves bounded correction toward a supplied reference; it supplies neither a
carrier encoder nor a record decoder. This module does not claim that PM requires
all conserved observables to be copied into this particular Boolean record.
The E8 carrier itself retains its glue key. Reading that carrier and reading the
Boolean rings are different contracts.

All generations admit coset roots at receiver site one. Their quiet-equal-ring
witnesses have exactly the same Boolean execution for a common channel. No
single decoder can read the generation of all those witnesses, even at the
first period end. Thus adding a static generation annotation would not prove
readability or select a reversal minimum under the strengthened Map. A physical
encoding/admission rule is needed before that minimum and its line count can
be determined. This is not a proof that no such encoding can exist in the rings.
-/

noncomputable section
namespace PMElementaryParticles.RetainedMap
open PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment PMKAutomaton.ClockSites
open PMElementaryParticles.EPSpine PMElementaryParticles.EPLabelGen
open PMElementaryParticles.IsolatedExcitation PMElementaryParticles.ProgramWitness
open PMElementaryParticles.HeavyFlipControl PMElementaryParticles.RingRates
open PMElementaryParticles.ReversalEvents
open PMConstants.PacketGaugeActions

/-- A word may change direction arbitrarily; each increment must be an admitted ring root. -/
theorem word_keeps_generation (z : V) (w : List V)
    (h : ∀ r ∈ w, r ∈ clockAxisRoots) : glueKey (z+w.sum) = glueKey z := by
  induction w generalizing z with
  | nil => simp
  | cons r w ih =>
    rw [List.sum_cons, ← add_assoc]
    exact (ih (z+r) (fun s hs => h s (by simp [hs]))).trans
      (step_keeps_generation z r (h r (by simp)))

theorem word_keeps_internal (z : V) (w : List V)
    (h : ∀ r ∈ w, r ∈ clockAxisRoots) : EPLabel.internalContent (z+w.sum) = EPLabel.internalContent z := by
  induction w generalizing z with
  | nil => simp
  | cons r w ih =>
    rw [List.sum_cons, ← add_assoc]
    exact (ih (z+r) (fun s hs => h s (by simp [hs]))).trans
      (EPLabel.step_keeps_label z r (h r (by simp)))

/-- Conservation is conditional on the root-step execution, not on an arbitrary successor. -/
theorem program_identity_conserved (p : Program) (w : List V)
    (h : ∀ r ∈ w, r ∈ clockAxisRoots) :
    glueKey (genPacket p+w.sum) = p.generation.val ∧
    EPLabel.internalContent (genPacket p+w.sum) = EPLabel.internalContent (genPacket p) :=
  ⟨(word_keeps_generation _ w h).trans (genPacket_key p), word_keeps_internal _ w h⟩

theorem word_label_readout (p : Program) (w : List V)
    (h : ∀ r ∈ w, r ∈ clockAxisRoots) :
    EPLabel.internalContent (genPacket p+w.sum) - EPLabel.internalContent p.packet =
      EPLabel.internalContent (channelE8Gen (genIndex p.generation) p.label) := by
  rw [word_keeps_internal _ w h, genPacket, EPLabel.internalContent_add]
  abel

/-- Reading the existing generation-specific channel placement recovers the same label. -/
theorem word_label_unique (p : Program) (w : List V)
    (h : ∀ r ∈ w, r ∈ clockAxisRoots) (c : Channels)
    (hr : EPLabel.internalContent (genPacket p+w.sum) - EPLabel.internalContent p.packet =
      EPLabel.internalContent (channelE8Gen (genIndex p.generation) c)) : c = p.label := by
  apply channelGen_internalContent_injective (genIndex p.generation)
  exact hr.symm.trans (word_label_readout p w h)

/-- No generation input occurs in the old labelRecord. -/
theorem label_record_generation_blind (c : Channels) (g h : Generation) :
    (fun _ : Generation => labelRecord c) g = (fun _ : Generation => labelRecord c) h := rfl

theorem label_record_cannot_decode_generation (c : Channels) :
    ¬ ∃ decode : Record → Generation, ∀ g : Generation, decode (labelRecord c) = g := by
  rintro ⟨decode, h⟩
  obtain ⟨g, k, hne⟩ : ∃ g k : Generation, g ≠ k := by decide +kernel
  exact hne ((h g).symm.trans (h k))

/-- One common receiver site is available in every generation. -/
theorem root_at_one : ∀ g : Generation,
    ∃ r ∈ rootList, glueKey r = g.val ∧ site r = 1 := by decide +kernel

def rootAtOne (g : Generation) : V := Classical.choose (root_at_one g)

theorem rootAtOne_spec (g : Generation) :
    rootAtOne g ∈ rootList ∧ glueKey (rootAtOne g) = g.val ∧ site (rootAtOne g) = 1 :=
  Classical.choose_spec (root_at_one g)

def quietProgram (g : Generation) (c : Channels) : Program :=
  ⟨c, g, leastRef c, quietEqualRing c, rootAtOne g,
    (rootAtOne_spec g).1, (rootAtOne_spec g).2.1⟩

theorem quiet_x0 (g : Generation) (c : Channels) : (quietProgram g c).x0 = 1 :=
  (rootAtOne_spec g).2.2

theorem quiet_program_pillars (g : Generation) (c : Channels) (hc : ProgramClasses.classOf c ≠ 4) :
    (quietProgram g c).Pillars := quiet_pillars c _ hc

theorem quiet_program_total (g : Generation) (c : Channels) : total (quietProgram g c) = 1 := by
  rw [total_eq_registrations]
  exact quiet_total c _

theorem quiet_footprint_one (g : Generation) (c : Channels) :
    footprint (quietProgram g c) = { events := 1 } := by
  unfold footprint
  rw [quiet_program_total]

theorem quiet_program_cost (g : Generation) (c : Channels) :
    PMSubstrate.OccupancyCost.cost (footprint (quietProgram g c)) = 1 := by
  rw [quiet_footprint_one]
  exact PMSubstrate.OccupancyCost.cost_oneEvent

/-- This is the minimum under the CURRENT pillars only, with no strengthened Map assumed. -/
theorem current_minimum (g : Generation) (k : Fin 6) (hk : k ≠ 4) :
    ∃ p : Program, p.generation = g ∧ ProgramClasses.classOf p.label = k ∧
      p.Pillars ∧ total p = 1 ∧
      ∀ q : Program, q.Pillars → total p ≤ total q := by
  obtain ⟨c, hc⟩ := ProgramClasses.classOf_surjective k
  refine ⟨quietProgram g c, rfl, hc, quiet_program_pillars g c (by simpa only [hc] using hk),
    quiet_program_total g c, ?_⟩
  intro q hq
  rw [quiet_program_total]
  exact total_floor q hq

/-- The old witness pays two physical reversals, not one. -/
theorem old_witness_two (c : Channels) :
    count true ((witness c).firing 0) (witness c).x0 43 +
      count true ((witness c).firing 1) (witness c).x0 43 = 2 := by
  rw [← registrations_eq_reversals, ← registrations_eq_reversals]
  change registrations (witness c) 0 + registrations (witness c) 1 = 2
  rw [witness_registrations, witness_registrations]

/-- Retained carrier labels; class and record bits are read from its channel. -/
abbrev RetainedReference := Generation × Channels × (Fin 4 → ℤ)

def reference (p : Program) : RetainedReference :=
  (p.generation, p.label, EPLabel.internalContent (genPacket p))

/-- The actual Boolean machine state of both rings. No carrier tag is appended. -/
abbrev RingObservation := Fin 2 → PMKAutomaton.RingReceiver.State 43

def initialRing (p : Program) (b : Fin 2) : PMKAutomaton.RingReceiver.State 43 :=
  (0, (p.firing b, (fun _ => false, localizedPortsN 43 p.x0 activePacket)))

def observe (p : Program) (t : ℕ) : RingObservation := fun b =>
  (PMKAutomaton.RingReceiver.tick 43 true)^[t] (initialRing p b)

/-- One shared decoder, applied at every positive period end. -/
def ReadableReference (read : RingObservation → RetainedReference) (p : Program) : Prop :=
  ∀ n : ℕ, read (observe p ((n+1)*43)) = reference p

def StrongMap (read : RingObservation → RetainedReference) (p : Program) : Prop :=
  p.Pillars ∧ ReadableReference read p

/-- A decoder chosen afresh per program would make readability vacuous. -/
theorem per_program_constant_decoder (p : Program) :
    ReadableReference (fun _ => reference p) p := fun _ => rfl

theorem strong_floor (read : RingObservation → RetainedReference) (p : Program)
    (h : StrongMap read p) : 1 ≤ total p := total_floor p h.1

theorem readable_generation (read : RingObservation → RetainedReference) (p : Program)
    (h : ReadableReference read p) (n : ℕ) :
    (read (observe p ((n+1)*43))).1 = p.generation := congrArg Prod.fst (h n)

theorem readable_class_record (read : RingObservation → RetainedReference) (p : Program)
    (h : ReadableReference read p) (n : ℕ) :
    ProgramClasses.classOf (read (observe p ((n+1)*43))).2.1 = ProgramClasses.classOf p.label ∧
    labelRecord (read (observe p ((n+1)*43))).2.1 = labelRecord p.label := by
  have hc := congrArg (fun x : RetainedReference => x.2.1) (h n)
  exact ⟨congrArg ProgramClasses.classOf hc, congrArg labelRecord hc⟩

theorem readable_internal (read : RingObservation → RetainedReference) (p : Program)
    (h : ReadableReference read p) (n : ℕ) :
    (read (observe p ((n+1)*43))).2.2 = EPLabel.internalContent (genPacket p) :=
  congrArg (fun x : RetainedReference => x.2.2) (h n)

theorem quiet_observations_equal (g h : Generation) (c : Channels) (t : ℕ) :
    observe (quietProgram g c) t = observe (quietProgram h c) t := by
  funext b
  change (PMKAutomaton.RingReceiver.tick 43 true)^[t]
      (0, (quietEqualRing c b, (fun _ => false,
        localizedPortsN 43 (quietProgram g c).x0 activePacket))) =
    (PMKAutomaton.RingReceiver.tick 43 true)^[t]
      (0, (quietEqualRing c b, (fun _ => false,
        localizedPortsN 43 (quietProgram h c).x0 activePacket)))
  rw [quiet_x0, quiet_x0]

/-- The present one-reversal witnesses have no common generation-sensitive ring decoder. -/
theorem no_uniform_quiet_decoder (c : Channels) :
    ¬ ∃ read : RingObservation → RetainedReference,
      ∀ g : Generation, ReadableReference read (quietProgram g c) := by
  rintro ⟨read, h⟩
  obtain ⟨g, k, hne⟩ : ∃ g k : Generation, g ≠ k := by decide +kernel
  have hg := h g 0
  have hk := h k 0
  rw [quiet_observations_equal g k c 43] at hg
  exact hne (congrArg Prod.fst (hg.symm.trans hk))

/-- A shared faithful reader cannot simply be added as a consequence of the old pillars. -/
theorem no_decoder_for_all_current_programs (c : Channels) (hc : ProgramClasses.classOf c ≠ 4) :
    ¬ ∃ read : RingObservation → RetainedReference,
      ∀ p : Program, p.Pillars → ReadableReference read p := by
  rintro ⟨read, h⟩
  apply no_uniform_quiet_decoder c
  exact ⟨read, fun g => h (quietProgram g c) (quiet_program_pillars g c hc)⟩

end PMElementaryParticles.RetainedMap
